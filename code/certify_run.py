"""(a'') certify stored torus runs in ball arithmetic (arb, 128 bits), phases exact fmpq.
Usage: python certify_run.py z2000.json results.json outdir
Run condition: sign*F_x(j) > T_K for all j. For each run key: window j=0..L-1, m = min_j F_x(j) - T_K, F_x(j)=sum_{k<=K} 2 w_k cos(j th_k + x_k),
T_K = C - 2 sum_{k<=K} w_k, C = 2+gamma_E-log(4 pi) = 2 lam1. Certified m_lo = lower bound of m.
r_lo = m_lo / upper(2 sum_{k<=K} w_k). Direct cos per term, no recurrence.
"""
import sys, json, time
from flint import arb, ctx, fmpq
ctx.prec = 128
ONLY = None                              # added: --only KEY (certify one stored run; default: all, as before)
if "--only" in sys.argv:
    _i = sys.argv.index("--only"); ONLY = sys.argv[_i + 1]; del sys.argv[_i:_i + 2]
zj = json.load(open(sys.argv[1])); res = json.load(open(sys.argv[2])); outdir = sys.argv[3]
def ball(l):
    def q(man, e): return arb(fmpq(man * 2 ** e, 1)) if e >= 0 else arb(fmpq(man, 2 ** (-e)))
    return arb(q(l[0], l[1]).mid(), q(l[2], l[3]).upper())
gam = [ball(l) for l in zj["gamma_mid_man_exp_rad_man_exp"]]
one = arb(1)
w = [one / (arb(1) / 4 + g * g) for g in gam]
th = [2 * (one / (2 * g)).atan() for g in gam]
C = 2 + arb.const_euler() - (4 * arb.pi()).log()
def lower(a): return a.mid() - a.rad()
def upper(a): return a.mid() + a.rad()
summary = []
for key in sorted(res, key=lambda s: (int(s.split("K")[1]), s)):
    if ONLY is not None and key != ONLY: continue
    r = res[key]; K = r["K"]; L = r["L_robust"]; t0 = time.time()
    xf = r["x_robust"]; assert len(xf) == K
    order = sorted(range(K), key=lambda k: float(gam[k].mid()))
    assert all(upper(gam[order[i]]) < lower(gam[order[i+1]]) for i in range(K-1)), 'zero balls not pairwise disjoint'
    xq = [fmpq(*float(v).as_integer_ratio()) for v in xf]       # exact dyadic rationals
    xa = [arb(q) for q in xq]
    sw = sum((w[k] for k in range(K)), arb(0))
    T = C - 2 * sw
    m_lo = None; jmin = None
    for j in range(L):
        F = arb(0)
        for k in range(K):
            F += 2 * w[k] * (th[k] * j + xa[k]).cos()
        mj = lower(r['sign'] * F - T)   # stored sign -1: run of F_x < 0 (x already carries the flip)
        if m_lo is None or mj < m_lo: m_lo, jmin = mj, j
    r_lo = m_lo / upper(2 * sw)
    ok = bool(m_lo > 0)
    out = dict(key=key, K=K, sign_stored=r["sign"], window="j=0..L-1", L=L, prec=128, m_lo=str(m_lo.str(12)),
               m_lo_float=float(m_lo), r_lo_float=float(r_lo), argmin_j=jmin, T_K_float=float(T.mid()),
               float_margin=r["margin_over_tail"], certified=ok, seconds=round(time.time() - t0, 1),
               x_num_den=[[int(q.p), int(q.q)] for q in xq])
    json.dump(out, open(f"{outdir}/cert_run_{key}.json", "w"))
    summary.append((key, K, r["sign"], L, float(m_lo), float(r_lo), ok))
    print(f"{key}\tK={K}\tL={L}\tm_lo={float(m_lo):.4e}\tr_lo={float(r_lo):.4e}\t{'PASS' if ok else 'FAIL'}\t{time.time()-t0:.0f}s", flush=True)
if ONLY is None: json.dump(summary, open(f"{outdir}/summary.json", "w"))
