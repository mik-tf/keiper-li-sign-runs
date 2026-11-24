"""(b') Certified bracket for delta/(th_1/pi), Theorem 4 and fallback 4' of PLAN.md (ball arithmetic, python-flint).

Usage: python certify_density.py z2000.json out.json [--ns N --nt N --workers W --fs 0.5 --ft 0.5
                                                      --edgecells N --tailonly --floatcheck DIR]
Per plan, sections 1 and 2.  All quantities are balls (arb, 128 bits); the lattice (h_s, h_t, L) is exact dyadic.
  delta_full/(th1/pi) in  2 f (central +- (err + tail)) / (th1/pi),      f = h_s h_t/(4 pi^2)
  Theorem 4 :  central = sum_in phi_100 Re That ; err = sum_in |phi_100||Re That| min(2,Q) ; tail = box tail of |phi_100||That|
  Theorem 4':  central +- tail  (truncated K=100 model, same lattice)
Box tail: |phi_100| <= prod_k min(1, env(a_k L_k)), L_k = max(|t| sin th_k, |s| - |t|(1-cos th_k)) <= |zeta_k| (degree-1 homogeneous),
env(x) = sqrt(2/(pi x)) (1 + 1/(8x)) for all x > 0: DLMF 10.17(iii), nu = 0, l = 1, read 2026-11-22 (DEFAULT, used for the headline).
Non-default (always also computed, reported as *_bareenv_NUMERIC_ONLY rows): env(x) = sqrt(2/(pi x)), numeric check only, no source found.
Units: tail_bound returns the tail of the RAW lattice sum sum |phi_100||That| (no factor f); br() multiplies by scale = 2f/(th1/pi) once.
Lattice shell count: Abel summation, N(r) <= (2 r ns+1)(2 r nt+1), sum_{lambda>1} lambda^-p <= p c/(p-2), c = 4 ns nt (1+1/2ns)(1+1/2nt).
"""
import sys, json, time, argparse
from fractions import Fraction
from multiprocessing import Pool
from flint import arb, acb, ctx, fmpq
import flint

ctx.prec = 128
K = 100


def dy_up(x, bits):
    """exact dyadic Fraction >= upper(x), multiple of 2^-bits"""
    m, e = x.upper().man_exp()
    v = Fraction(int(m)) * Fraction(2) ** int(e)
    n = -((-v * 2 ** bits) // 1)
    return Fraction(int(n), 2 ** bits)


def dy_dn(x, bits):
    m, e = x.lower().man_exp()
    v = Fraction(int(m)) * Fraction(2) ** int(e)
    n = (v * 2 ** bits) // 1
    return Fraction(int(n), 2 ** bits)


def ab(fr):
    return arb(fmpq(fr.numerator, fr.denominator))


def ball(l):
    def q(man, e): return arb(fmpq(man * 2 ** e, 1)) if e >= 0 else arb(fmpq(man, 2 ** (-e)))
    return arb(q(l[0], l[1]).mid(), q(l[2], l[3]).upper())


def pack(x):
    return (tuple(int(v) for v in x.mid().man_exp()), tuple(int(v) for v in x.rad().man_exp()))


def _dy(m, e):
    return fmpq(m * 2 ** e, 1) if e >= 0 else fmpq(m, 2 ** (-e))


def unpack(p):
    (m, e), (rm, re_) = p
    return arb(_dy(m, e)) + arb(0, _dy(rm, re_))


def Efun(z):
    if z == 0: return acb(1)
    iz = acb(0, z)
    return (iz.exp() - 1) / iz


def ReThat(sig, tau, L2):
    """L^2 * Re g, g = int_{0<x<y<1} e^{i sig x - i tau y}"""
    if sig == 0:
        if tau == 0: return L2 / 2
        e = acb(0, -tau).exp()
        g = (e * (1 + acb(0, tau)) - 1) / (tau * tau)
    else:
        g = (Efun(sig - tau) - Efun(-tau)) / acb(0, sig)
    return L2 * g.real


# ---------------- setup (module level, inherited by forked workers) ----------------
G = {}


def setup(zpath, fs, ft):
    zj = json.load(open(zpath)); N = zj["N"]
    gam = [ball(l) for l in zj["gamma_mid_man_exp_rad_man_exp"]]
    one = arb(1)
    w = [one / (arb(1) / 4 + g * g) for g in gam]
    th = [2 * (one / (2 * g)).atan() for g in gam]
    C = 2 + arb.const_euler() - (4 * arb.pi()).log()
    a = [2 * x for x in w]
    Tt = C - sum(a, arb(0))                      # T_2000, weight of zeros beyond the list (with multiplicity)
    assert Tt > 0
    thm = one / gam[-1].lower()                  # th_g <= 1/g <= 1/gamma_2000 for the zeros beyond the list
    Sd = sum((2 * a[k] * (th[k] / 2).sin() for k in range(N)), arb(0)) + Tt.upper() * thm
    Lfr = dy_up(Sd, 20); L = ab(Lfr)
    hs_fr = dy_dn(fs * 2 * arb.pi() / (C + L), 10); ht_fr = dy_dn(ft * 2 * arb.pi() / (2 * L), 10)
    hs = ab(hs_fr); ht = ab(ht_fr)
    assert bool(hs * (C + L) < 2 * arb.pi()) and bool(ht * 2 * L < 2 * arb.pi()), "aliasing"
    c = [x.cos() for x in th[:K]]; sn = [x.sin() for x in th[:K]]
    M0 = sum((a[k] ** 2 for k in range(K, N)), arb(0))
    M1 = sum((a[k] ** 2 * (1 - th[k].cos()) for k in range(K, N)), arb(0))
    M2 = 2 * M1
    Tz = arb(fmpq(*zj["T"]))                     # certified height: every zero beyond the list has gamma >= T
    Aq = (2 / (arb(1) / 4 + Tz * Tz)).upper()    # a_k <= A = 2/(1/4+T^2) for k > 2000 (w decreasing)
    thT = (2 * (1 / (2 * Tz)).atan()).upper()    # th_k <= th(T) = 2 atan(1/(2T))
    G.update(Aq=Aq, thT=thT, N=N, gam=gam, th=th, a=a, C=C, Tt=Tt, thm=thm, Sd=Sd, L=L, Lfr=Lfr, hs=hs, ht=ht, hs_fr=hs_fr, ht_fr=ht_fr,
             c=c, sn=sn, omc=[1 - x for x in c], M0=M0, M1=M1, M2=M2, T=zj["T"],
             area=L * L / 2, th1=th[0], f=hs * ht / (4 * arb.pi() ** 2))


# ---------------- lattice rows ----------------
def row(i):
    a = G["a"][:K]; omc = G["omc"]; sn = G["sn"]; hs = G["hs"]; ht = G["ht"]; L = G["L"]; L2 = L * L
    M0, M1, M2, Tt, thm = G["M0"], G["M1"], G["M2"], G["Tt"].upper(), G["thm"]
    nt = G["nt"]
    s = i * hs
    cen = arb(0); err = arb(0); absum = arb(0)
    s2 = s * s
    if G["bound"] == "r1":      # amendment r1: sum a^2 g <= A G T_2000, g=(|s|+|t|th)^2 <= (|s|+|t|th(T))^2
        Tq = G["Aq"] * Tt; thm = G["thT"]
    else:                       # r0 (original plan): sum a^2 <= T_2000^2, th <= 1/gamma_2000
        Tq = Tt * Tt
    two = arb(2)
    for j in range(nt + 1):
        t = j * ht
        ph = arb(1)
        for k in range(K):
            re = s - t * omc[k]; im = t * sn[k]
            ph *= (a[k] * (re * re + im * im).sqrt()).bessel_j(0)
        rt = ReThat(s * L, t * L, L2)
        wj = 1 if j == 0 else 2
        term = ph * rt
        cen += wj * term
        ab_ = abs(term)
        absum += wj * ab_
        Q = (s2 * M0 - 2 * s * t * M1 + t * t * M2) / 4 + Tq * (abs(s) + t * thm) ** 2 / 4
        qu = Q.upper()
        if qu > two: qu = two
        err += wj * ab_ * qu
    return i, pack(cen), pack(err), pack(absum)


# ---------------- box tail ----------------
def max_lower(x, y):
    xl = x.lower(); yl = y.lower()
    return xl if xl > yl else yl


def tail_bound(ns, nt, ncell, bare=False):
    a = G["a"][:K]; omc = G["omc"]; sn = G["sn"]
    Smax = ns * G["hs"]; Tmax = nt * G["ht"]
    pi = arb.pi()

    def cellU(tl, tu, sl):
        """|t| in [tl,tu], |s| >= sl: upper bound of prod min(1,env) and a lower bound of the count of envelope factors"""
        U = arb(1); m = 0
        for k in range(K):
            Lk = max_lower(tl * sn[k], sl - tu * omc[k])
            if not (Lk > 0): continue
            x = a[k] * Lk
            if bare:   # numeric check only, no source found
                r = (2 / (pi * x)).sqrt()
            else:      # DLMF 10.17(iii), nu=0, l=1: valid for all x > 0 (a factor with r >= 1 is skipped, i.e. min(1, env))
                r = (2 / (pi * x)).sqrt() * (1 + 1 / (8 * x))
            ru = r.upper()
            if ru < 1:
                U *= ru; m += 1
        return U.upper(), m

    Umax = arb(0); mmin = 10 ** 9
    # edge |s| = Smax, |t| in [0,Tmax]   ((s,t) -> (-s,-t) symmetry of |phi| and of the bound)
    for e in range(ncell):
        tl = Tmax * arb(e) / ncell; tu = Tmax * arb(e + 1) / ncell
        U, m = cellU(tl, tu, Smax)
        if U > Umax: Umax = U
        mmin = min(mmin, m)
    # edge |t| = Tmax, |s| in [0,Smax]
    for e in range(ncell):
        sl = Smax * arb(e) / ncell
        U, m = cellU(Tmax, Tmax, sl)
        if U > Umax: Umax = U
        mmin = min(mmin, m)
    p = Fraction(mmin, 2)
    if p <= 2: return None, Umax, mmin
    cc = 4 * ns * nt * (1 + Fraction(1, 2 * ns)) * (1 + Fraction(1, 2 * nt))
    sh = ab(p * cc / (p - 2))
    tail = G["area"] * Umax * sh      # raw-lattice-sum units (|That| <= area = L^2/2); the factor f enters once, in br()
    assert G["area"] == G["L"] * G["L"] / 2   # units guard: tail must not carry f = hs ht/(4 pi^2)
    return tail.upper(), Umax, mmin


def fstr(x, d=12): return x.str(d, radius=False)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("z"); ap.add_argument("out")
    ap.add_argument("--ns", type=int, default=346); ap.add_argument("--nt", type=int, default=705)
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--fs", type=float, default=0.5); ap.add_argument("--ft", type=float, default=0.5)
    ap.add_argument("--edgecells", type=int, default=4000)
    ap.add_argument("--bound", choices=["r0", "r1"], default="r1")
    ap.add_argument("--tailonly", action="store_true")
    ap.add_argument("--diag-nobeyond", action="store_true", help="NOT CERTIFIED: drops the beyond-2000 term of Q, diagnostic only")
    ap.add_argument("--floatcheck", default=None)
    A = ap.parse_args()
    t00 = time.time()
    setup(A.z, A.fs, A.ft)
    G["nt"] = A.nt; G["bound"] = A.bound
    if A.diag_nobeyond: G["Tt"] = arb(0)
    print("M0,M1 (101..2000):", fstr(G["M0"], 6), fstr(G["M1"], 6), "T2000^2:", fstr(G["Tt"]**2, 6), flush=True)
    ns, nt = A.ns, A.nt
    print(f"flint {flint.__version__} prec {ctx.prec} N={G['N']} C={fstr(G['C'])} T2000={fstr(G['Tt'])} Sd<={fstr(G['Sd'])} "
          f"L={G['Lfr']} hs={G['hs_fr']} ({float(G['hs_fr']):.4f}) ht={G['ht_fr']} ({float(G['ht_fr']):.4f}) "
          f"lattice {2*ns+1}x{nt+1}", flush=True)
    res = dict(flint=flint.__version__, prec=ctx.prec, ns=ns, nt=nt, L=str(G["Lfr"]), hs=str(G["hs_fr"]), ht=str(G["ht_fr"]),
               C=fstr(G["C"], 20), T2000=fstr(G["Tt"], 12), Sd_upper=fstr(G["Sd"], 12), edgecells=A.edgecells)
    t = time.time()
    tb, Um, mm = tail_bound(ns, nt, A.edgecells)
    tbf, Umf, mmf = tail_bound(ns, nt, A.edgecells, bare=True)
    print(f"tail (raw sum) DLMF env: {None if tb is None else fstr(tb,4)} Umax={fstr(Um,4)} m={mm};  bare env (numeric check only): "
          f"{None if tbf is None else fstr(tbf,4)} Umax={fstr(Umf,4)} m={mmf}  ({time.time()-t:.0f}s)", flush=True)
    res.update(tail_raw_dlmf=None if tb is None else fstr(tb, 8), Umax=fstr(Um, 8), mmin=mm,
               tail_raw_bareenv_NUMERIC_ONLY=None if tbf is None else fstr(tbf, 8), Umax_bare=fstr(Umf, 8), mmin_bare=mmf)
    if A.tailonly or ((tb is None or tbf is None) and not A.floatcheck):
        json.dump(res, open(A.out, "w"), indent=1); return
    t = time.time()
    rows = {}
    with Pool(A.workers) as pool:
        for r in pool.imap_unordered(row, range(-ns, ns + 1), chunksize=1):
            rows[r[0]] = r
            if len(rows) % 50 == 0: print(f"rows {len(rows)}/{2*ns+1} {time.time()-t:.0f}s", flush=True)
    cen = arb(0); err = arb(0); absum = arb(0)
    for i in sorted(rows):
        cen += unpack(rows[i][1]); err += unpack(rows[i][2]); absum += unpack(rows[i][3])
    run_s = time.time() - t
    f = G["f"]; den = G["th1"] / arb.pi()
    scale = 2 * f / den

    def br(c0, e0, tl):
        lo = scale * (c0 - e0 - tl); hi = scale * (c0 + e0 + tl)
        return lo.lower(), hi.upper()
    out = {}
    for name, (tl, e0) in ({} if tb is None or tbf is None else dict(thm4=(tb, err.upper()), thm4_bareenv_NUMERIC_ONLY=(tbf, err.upper()),
                               thm4p=(tb, arb(0)), thm4p_bareenv_NUMERIC_ONLY=(tbf, arb(0)))).items():
        lo, hi = br(cen, e0, tl)
        out[name] = dict(lo=fstr(lo, 12), hi=fstr(hi, 12), width=fstr(hi - lo, 4), width_pct=float((hi - lo) * 100))
    res.update(central_sum=cen.str(25), err_sum_upper=fstr(err.upper(), 6), abs_sum=fstr(absum, 8),
               ratio_center_K100=fstr(scale * cen, 12), results=out,
               lattice_points=(2 * ns + 1) * (nt + 1), run_seconds=run_s, total_seconds=time.time() - t00,
               th1_over_pi=fstr(den, 12), workers=A.workers)
    print(json.dumps(res["results"], indent=1), flush=True)
    print("center ratio (K=100 model, central sum only):", res["ratio_center_K100"], flush=True)
    if A.floatcheck:
        import numpy as np
        sys.path.insert(0, A.floatcheck)
        import fourier_bracket as fb
        af = np.array([float(x.mid()) for x in G["a"][:K]])
        thf = np.array([float(x.mid()) for x in G["th"][:K]])
        cf = np.cos(thf); sf = np.sin(thf)
        hs = float(G["hs"].mid()); ht = float(G["ht"].mid()); L = float(G["L"].mid())
        S = hs * np.arange(-ns, ns + 1); T = ht * np.arange(0, nt + 1)
        ph = fb.phi_grid(S, T, af, cf, sf)
        SS, TT = np.meshgrid(S, T, indexing="ij")
        ReT = (L ** 2) * fb.That_over_L2(SS * L, TT * L).real
        wt = np.where(T == 0, 1.0, 2.0)[None, :]
        fl = float(np.sum(ph * ReT * wt))
        print(f"floatcheck: ball central {float(cen.mid()):.15e} float {fl:.15e} diff {float(cen.mid())-fl:.2e}", flush=True)
        res["floatcheck_central_float"] = fl
    json.dump(res, open(A.out, "w"), indent=1)


if __name__ == "__main__":
    main()
