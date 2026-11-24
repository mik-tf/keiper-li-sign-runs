#!/usr/bin/env python3
"""W2: independent certificate for a W1 sign-run witness. Imports nothing from the W1 search code.

Claim certified (CONDITIONAL ON RH): c_m has the stated sign for every integer m in [M, M+L-1].
  c_m = sum over zeros rho of 2 w cos(m theta), w = 1/(1/4+gamma^2), theta = 2 atan(1/(2 gamma))
  (paper Lemma 1: c_m = F(m) for m >= 1; under RH every zero is gamma = Im rho).
Method (python-flint balls):
  1. zeros: z2000.json midpoints re-verified by Hardy Z sign change at mid +- 1e-20 (prec 128), intervals
     disjoint, count N(T)=2000 by Arb zeta_nzeros (as crosscheck_window.py). Then zeros 1..K are recomputed
     at high precision with acb.zeta_zero(k) and each ball must lie inside [mid-eps, mid+eps] of the same index.
  2. explicit sum F_K(m) = sum_{k<=K} 2 w_k cos(m theta_k), m an exact integer, balls at prec ~ 3.33(log10 M + 40) bits.
  3. tail: T_K = C - sum_{k<=K} 2 w_k, C = 2 + gammaE - log(4 pi) = sum of ALL 2w (multiplicity included)
     (paper identity, Appendix A / crosscheck_window.py 'tail'); |sum_{k>K} 2 w cos| <= T_K.
  4. sign: positive run needs lower(F_K(m)) - upper(T_K) > 0; negative needs -upper(F_K(m)) - upper(T_K) > 0.
  5. F4 (W3 review): for every zero used, Hardy Z changes sign between the two endpoints of its zeta_zero ball
     (widened by 4 ulps), evaluated at the working precision + 160 bits; so only zeta, lgamma, zeta_nzeros are trusted, not zeta_zero.
Usage: python3 certify_witness.py CODE_DIR WITNESS.txt K L SIGN(+1|-1) OUT_JSON
"""
import sys, json, time, hashlib
import flint
from flint import arb, acb, ctx, fmpq

def main():
    cdir, nfile, K, L, sign, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    t_start = time.time()
    n = int(open(nfile).read().strip())
    # window of positive indices; c_{-m} = c_m (F even), so n<0 gives |n|-L+1 .. |n|
    M = n if n > 0 else abs(n) - L + 1
    if not M >= 1:
        raise SystemExit('FAIL: window start M < 1')
    digits = len(str(M + L))
    # ---- step 1: zeros
    ctx.prec = 128
    zj = json.load(open(f"{cdir}/z2000.json"))
    N = zj["N"]
    if not (zj["count_NT"] == N == 2000):
        raise SystemExit("FAIL: z2000.json count is not 2000")
    T = arb(fmpq(*zj["T"]))
    def q(man, e):
        return fmpq(man * 2 ** e, 1) if e >= 0 else fmpq(man, 2 ** (-e))
    mids = [arb(q(l[0], l[1])) for l in zj["gamma_mid_man_exp_rad_man_exp"]]
    eps = arb(10) ** -20
    def Zf(t):
        s = acb(arb(1) / 2, t)
        thv = acb(arb(1) / 4, t / 2).lgamma().imag - t / 2 * arb.pi().log()
        return (acb(0, thv).exp() * s.zeta()).real
    def sg(x): return 1 if x > 0 else (-1 if x < 0 else 0)
    sign_changes_ok = False
    for i, g in enumerate(mids):
        if not sg(Zf(g - eps)) * sg(Zf(g + eps)) == -1:
            raise SystemExit(f"FAIL: no sign change {i+1}")
        nxt = mids[i + 1] - eps if i + 1 < N else T
        if not (g + eps) < nxt:
            raise SystemExit(f"FAIL: overlap {i+1}")
    sign_changes_ok = True  # loop above raises SystemExit on any failure
    cnt = T.zeta_nzeros()
    count_ok = bool(cnt == N and cnt.rad() == 0)
    if not count_ok:
        raise SystemExit("FAIL: zeta_nzeros count is not 2000")
    # ---- precision
    bits = int(3.3219 * (digits + 40)) + 64
    ctx.prec = bits
    t0 = time.time()
    gam = []
    zeros_inside = False
    f4_checked = 0
    f4_min_gap_ulps = None
    for k in range(1, K + 1):
        z = acb.zeta_zero(k)
        g = z.imag
        # F4: Z sign change at both endpoints of the ball, widened by 4 ulps of the working precision
        # endpoints are exact numbers (radius 0); Z there is about 2^-bits, so evaluate with 160 extra bits
        ctx.prec = bits + 160
        w = (g.rad() + g.mid().abs_upper() * arb(2) ** (-bits) * 4).upper()
        lo, hi = (g.mid() - w).mid(), (g.mid() + w).mid()
        zlo, zhi = Zf(lo), Zf(hi)
        ctx.prec = bits
        if not sg(zlo) * sg(zhi) == -1:
            raise SystemExit(f"FAIL F4: zeta_zero({k}) no Z sign change at ball endpoints, ball radius {float(g.rad())}, width used {float(w)}, Z(lo)={float(zlo.mid())} rad {float(zlo.rad())}, Z(hi)={float(zhi.mid())} rad {float(zhi.rad())}")
        f4_checked += 1
        # from here on the zero is the widened ball [lo, hi], the one F4 certifies, not the narrower zeta_zero ball
        g = arb(g.mid(), w)
        if not ((g > mids[k-1] - eps) and (g < mids[k-1] + eps)):
            raise SystemExit(f"FAIL: zeta_zero({k}) not inside z2000 ball")
        gam.append(g)
    zeros_inside = len(gam) == K
    t_zeros = time.time() - t0
    one = arb(1)
    a = [2 / (one / 4 + g * g) for g in gam]
    th = [2 * (one / (2 * g)).atan() for g in gam]
    C = 2 + arb.const_euler() - (4 * arb.pi()).log()
    TK = C - sum(a, arb(0))
    if not TK > 0:
        raise SystemExit("FAIL: T_K not positive")
    TKu = TK.upper()
    # ---- step 2-4
    t0 = time.time()
    margins = []; maxrad = arb(0); first_fail = None; rows = []
    for m in range(M, M + L):
        F = arb(0)
        for k in range(K):
            F += a[k] * (arb(m) * th[k]).cos()
        rad = F.rad()
        if rad > maxrad: maxrad = rad
        marg = (F.lower() - TKu) if sign > 0 else (-F.upper() - TKu)
        margins.append(marg)
        if not marg > 0 and first_fail is None:
            first_fail = (m - M, m, float(marg.mid()))
    t_sum = time.time() - t0
    mn = min(margins, key=lambda x: float(x.mid()))
    ok = first_fail is None and maxrad < arb(10) ** -30
    res = {
        "status": "PASS" if ok else "FAIL", "conditional_on": "RH",
        "n_file": nfile.split("/")[-1], "n_signed_digits": len(str(abs(n))),
        "K": K, "L": L, "sign": sign, "M_start": str(M), "M_start_sha256": hashlib.sha256(str(M).encode()).hexdigest(),
        "M_end": str(M + L - 1), "prec_bits": bits,
        "T_K": float(TK.mid()), "T_K_upper": float(TKu), "T_K_rad": float(TK.rad()),
        "min_margin": float(mn.mid()), "min_margin_at_m_minus_M": margins.index(mn),
        "max_ball_radius_F_K": float(maxrad), "first_fail_j_m_margin": first_fail,
        "zeros_inside_z2000_balls": zeros_inside, "z2000_hardy_Z_sign_changes_2000": sign_changes_ok, "F4_endpoint_sign_changes_checked": f4_checked, "F4_ok": f4_checked == K, "N_T_count": N if count_ok else None,
        "python_flint_version": flint.__version__, "flint_version": getattr(flint, "__FLINT_VERSION__", None), "arb_version": getattr(flint, "__ARB_VERSION__", None), "flint_all_version_attrs": {a: str(getattr(flint, a)) for a in dir(flint) if "VERSION" in a.upper()},
        "python_version": sys.version, "argv": " ".join(sys.argv), "python_O": not __debug__,
        "time_zeros_s": t_zeros, "time_sums_s": t_sum, "time_total_s": time.time() - t_start,
    }
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps(res))

main()
