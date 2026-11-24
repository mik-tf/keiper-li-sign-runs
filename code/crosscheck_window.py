#!/usr/bin/env python3
"""Independent implementation cross-check of Theorem A (sign window under RH).

Does not import certify.py / certify_run.py. Reads as DATA only: z2000.json (zero midpoints and
the stated T, N(T)=2000 count) and the kernel numerators K_d = m_d/2^50 from cert_L{1699,1573}.json.
Everything else is python-flint ball arithmetic (arb/acb), prec 128:
  * zeros: each archived midpoint g is re-verified here: a sign change of Hardy Z (acb zeta, acb lgamma,
    Z = Re(exp(i theta) zeta(1/2+it))) with Z's sign decided by balls at g-eps and g+eps, eps=1e-20,
    so a zero of zeta lies in [g-eps,g+eps]; the 2000 intervals are checked disjoint and below T.
    The count N(T)=2000 is Arb's zeta_nzeros(T), the same trusted routine as certify.py (not independent).
    Under RH: 2000 simple zeros in the intervals and N(T)=2000 means these are all zeros up to T.
  * weights w=1/(1/4+g^2), theta=2 atan(1/(2g)) as balls over [g-eps,g+eps].
  * tail weight tau = (2+gammaE-log 4pi) - 2 sum w (exact identity of the paper, Lemma formula), tau>0 checked.
  * inequality (paper Appendix A, Theorem A):
      w1 k(0) > sum 2 w|k(th)| + sum_{rho!=1} w|k(th-th1)| + sum w|k(th+th1)| + tau k(0) (1 + M)
    M = bound of |k|/k(0) on the arc |phi| in [th1-thT, th1+thT], by a grid of centres (spacing 4e-7)
    plus the Lipschitz term h*delta (|k'| <= h k(0)); own grid, finer than certify.py.
Usage: python3 crosscheck_window.py <code dir with z2000.json, cert_L*.json> --json OUT
"""
import sys, json, time
from flint import arb, acb, ctx, fmpq

args = sys.argv[1:]
out = None
if "--json" in args:
    i = args.index("--json"); out = args[i + 1]; del args[i:i + 2]
cdir = args[0] if args else "papers/keiper-li-sign-runs/code"
ctx.prec = 128
t0 = time.time()
zj = json.load(open(f"{cdir}/z2000.json"))
N = zj["N"]
assert zj["count_NT"] == N == 2000
T = arb(fmpq(*zj["T"]))
def q(man, e):
    return fmpq(man * 2 ** e, 1) if e >= 0 else fmpq(man, 2 ** (-e))
mids = [arb(q(l[0], l[1])) for l in zj["gamma_mid_man_exp_rad_man_exp"]]
eps = arb(10) ** -20

half = acb(1, 0) / 2
def Z(t):
    t = arb(t)
    s = acb(half.real, t)
    th = (acb(arb(1) / 4, t / 2)).lgamma().imag - t / 2 * arb.pi().log()
    e = acb(0, th).exp()
    v = e * s.zeta()
    return v.real
def sgn(x):
    if x > 0: return 1
    if x < 0: return -1
    return 0
gam = []
for g in mids:
    a, b = Z(g - eps), Z(g + eps)
    assert sgn(a) * sgn(b) == -1, "no certified sign change"
    gam.append(arb(g.mid(), eps.upper()))        # ball [g-eps, g+eps]
for i in range(N):
    nxt = gam[i + 1].lower() if i + 1 < N else T
    assert gam[i].upper() < nxt, "intervals overlap"
cnt = T.zeta_nzeros()
assert cnt == N and cnt.rad() == 0, "N(T) count mismatch"
assert gam[0].lower() > 10
t1 = time.time()

one = arb(1)
w = [one / (arb(1) / 4 + g * g) for g in gam]
th = [2 * (one / (2 * g)).atan() for g in gam]
C = 2 + arb.const_euler() - (4 * arb.pi()).log()
tail = C - 2 * sum(w, arb(0))
assert tail > 0
tau = tail.upper()
thT = 2 * (one / (2 * T)).atan()
th1, w1 = th[0], w[0]

def ratio_up12(r):
    # upper endpoint of the ball, rounded UP at 12 decimals, as an exact decimal string
    n = int((r.upper() * 10**12).upper().ceil().unique_fmpz())
    return "%d.%012d" % (n // 10**12, n % 10**12)

def run(L):
    cert = json.load(open(f"{cdir}/cert_L{L}.json"))
    h = (L - 1) // 2
    m = [int(s) for s in cert["kernel_numerators_K0_to_Kh"]]
    assert cert["L"] == L and len(m) == h + 1 and all(x >= 0 for x in m)
    k0 = m[0] + 2 * sum(m[1:])
    k0b = arb(k0)
    terms = [(d, arb(2 * m[d])) for d in range(1, h + 1) if m[d]]
    m0 = arb(m[0])
    def kabs(phi):
        s = m0
        for d, a in terms:
            s += a * (d * phi).cos()
        return abs(s) / k0b
    s1 = arb(0); s2 = arb(0)
    for i in range(N):
        s1 += 2 * w[i] * kabs(th[i])
        if i: s2 += w[i] * kabs(th[i] - th1)
        s2 += w[i] * kabs(-th[i] - th1)
    lo = (-thT - th1).lower(); hi = (thT - th1).upper()
    ncell = int(float(hi - lo) / 8e-7) + 1
    delta = (hi - lo) / (2 * ncell)                 # half-width of a cell
    M = arb(0)
    for j in range(ncell):
        c = lo + (2 * j + 1) * delta
        v = kabs(c).upper()
        if v > M: M = v
    M = M + h * (delta + arb(10) ** -15)
    if M > 1: M = arb(1)
    rhs = s1 + s2 + tau * (1 + M)
    ratio = rhs / w1
    ok = bool(ratio < 1)
    return dict(L=L, h=h, nonzero_Kd=len(terms), k0_numerator=str(k0), M_upper=float(M.upper()),
                archived_M_upper=cert["tail_arc_M_upper"], ratio_ball=ratio.str(15),
                ratio_upper=ratio_up12(ratio), ratio_enclosure_width=float(2 * ratio.rad()),
                archived_ratio_upper=cert["ratio_rhs_over_lhs_upper"],
                consistent_with_archived=bool(ratio.upper() <= arb(cert["ratio_rhs_over_lhs_upper"]) ),
                certified_below_1=ok)

res = dict(prec_bits=128, zeros=N, T=float(T.mid()), zero_halfwidth="1e-20", count_NT_source="arb zeta_nzeros(T), same routine as certify.py",
           tail_weight=tail.str(12), w1=w1.str(12), windows=[run(1699), run(1573)])
res["pass"] = all(r["certified_below_1"] and r["consistent_with_archived"] for r in res["windows"])
res["seconds"] = round(time.time() - t0, 1)
res["seconds_zero_check"] = round(t1 - t0, 1)
if out:
    json.dump(res, open(out, "w"), indent=1)
print(json.dumps(res, indent=1))
