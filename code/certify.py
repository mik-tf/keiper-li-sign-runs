"""Step 2-3: LP kernel (float), round to exact nonnegative rationals, certify in ball arithmetic.
Usage: python certify.py zeros.json L [L ...]     (each L odd; writes cert_L<L>.json if certified)
       python certify.py zeros.json --bisect LO HI (smallest odd L in [LO,HI] that certifies, assuming monotone)
Inequality certified (RH, all zeros listed up to T are simple and complete, see zeros.py):
  w1 k(0) > sum_rho w|k(th_rho)| + sum_{rho != rho1} w|k(th_rho - th1)|
with K >= 0 supported on L=2h+1 consecutive integers, symmetric, k~(phi)=K_0+2 sum_d K_d cos(d phi).
Unlisted zeros (|gamma|>T) carry total weight tail = (2+gamma_E-log 4pi) - 2 sum_listed w (exact identity),
bounded by tail*1 in the first sum (|k|<=k(0)) and tail*M in the second, M = rigorous bound of |k|/k(0) on
the arc [-thT-th1, thT-th1] (grid of centres + Lipschitz bound |k~'|<=h k(0)).
"""
import sys, json, time
import numpy as np
from fractions import Fraction
from flint import arb, acb, acb_poly, ctx, fmpz, fmpq
import flint
from scipy.optimize import linprog
from scipy.sparse import hstack, vstack, identity, csr_matrix, coo_matrix
OUTDIR = "."                              # added: --outdir DIR (default: current directory, as before)
if "--outdir" in sys.argv:
    _i = sys.argv.index("--outdir"); OUTDIR = sys.argv[_i + 1]; del sys.argv[_i:_i + 2]
ctx.prec = 128
S = 50                                   # kernel denominator 2^S
zj = json.load(open(sys.argv[1])); N = zj["N"]
def ball(l):
    def q(man, e): return arb(fmpq(man * 2 ** e, 1)) if e >= 0 else arb(fmpq(man, 2 ** (-e)))
    return arb(q(l[0], l[1]).mid(), q(l[2], l[3]).upper())
gam = [ball(l) for l in zj["gamma_mid_man_exp_rad_man_exp"]]
Tb = arb(fmpq(*zj["T"]))
one = arb(1)
w = [one / (arb(1) / 4 + g * g) for g in gam]
th = [2 * (one / (2 * g)).atan() for g in gam]
C = 2 + arb.const_euler() - (4 * arb.pi()).log()
tail = C - 2 * sum(w, arb(0))
assert tail > 0
thT = 2 * (one / (2 * Tb)).atan()
th1 = th[0]; w1 = w[0]
tail_u = tail.upper()
print(f"zeros={N} T={float(Tb):.3f} w1={float(w1):.6f} tail={float(tail):.4e}", flush=True)

# ---------------- float LP ----------------
gf = np.array([float(g.mid()) for g in gam]); wf = 1 / (0.25 + gf ** 2); thf = 2 * np.arctan(1 / (2 * gf))
tailf = float(tail.mid()); t1 = thf[0]; w1f = wf[0]; thTf = float(thT.mid())
def lp(L, ng=161):
    h = (L - 1) // 2; d = np.arange(h + 1)
    grid = np.linspace(-thTf, thTf, ng) - t1
    F = np.concatenate([thf, thf[1:] - t1, -thf - t1 + 0 * thf, grid])   # first sum doubled via weight 2
    W = np.concatenate([2 * wf, wf[1:], wf, np.zeros(ng)])
    F = np.concatenate([thf, thf[1:] - t1, -thf - t1, grid])
    n = len(F)
    A = np.cos(np.outer(F, d)); A[:, 1:] *= 2
    # vars: K(h+1), t(n), s ; min W.t + tail*s ; |A K|<=t ; for grid rows t unused: |A K|<=s
    c = np.concatenate([np.zeros(h + 1), W, [tailf]])
    isgrid = np.zeros(n, bool); isgrid[-ng:] = True
    Tcol = identity(n, format="csr").tolil()
    for i in range(n - ng, n): Tcol[i, i] = 0
    Tcol = Tcol.tocsr()
    sc = csr_matrix(np.where(isgrid, -1.0, 0.0)[:, None])
    Ak = csr_matrix(A)
    Aub = vstack([hstack([Ak, -Tcol, sc]), hstack([-Ak, -Tcol, sc])], format="csr")
    Aeq = csr_matrix(np.concatenate([[1], 2 * np.ones(h), np.zeros(n + 1)])[None, :])
    r = linprog(c, A_ub=Aub, b_ub=np.zeros(2 * n), A_eq=Aeq, b_eq=[1], bounds=[(0, None)] * (h + 2 + n), method="highs")
    assert r.status == 0, r.message
    K = r.x[:h + 1]
    return K, (r.fun + tailf) / w1f      # float ratio (tail*1 for first sum added)

# ---------------- certification ----------------
def certify(K, L, ncell=None):
    h = (L - 1) // 2
    m = [int(max(0, np.floor(k * 2 ** S))) for k in K]            # exact nonnegative integers, K_d = m_d / 2^S
    k0 = m[0] + 2 * sum(m[1:])
    a = [arb(m[0])] + [arb(2 * x) for x in m[1:]]
    k0b = arb(k0)
    dd = [arb(d) for d in range(h + 1)]
    def kabs(phi):                                                # enclosure of |k~(phi)|/k(0), direct sum of cos(d phi)
        tot = a[0]
        for d in range(1, h + 1):
            tot += a[d] * (dd[d] * phi).cos()
        return abs(tot) / k0b
    s1 = arb(0); s2 = arb(0)
    for i in range(N):
        s1 += 2 * w[i] * kabs(th[i])
        if i: s2 += w[i] * kabs(th[i] - th1)
        s2 += w[i] * kabs(-th[i] - th1)
    # tail arc
    lo = (-thT - th1).lower(); hi = (thT - th1).upper()
    width = hi - lo
    if ncell is None: ncell = int(float(width) / 5e-6) + 1
    delta = width / ncell
    M = arb(0)
    for j in range(ncell):
        c = lo + (j + arb(1) / 2) * delta
        v = kabs(c).upper()
        if v > M: M = v
    M = M + h * (delta / 2 + arb(10) ** -15)                       # |k~'| <= h k(0)
    if M > 1: M = arb(1)
    rhs = s1 + s2 + tail_u * 1 + tail_u * M
    ok = bool(rhs < w1)
    ratio = (rhs / w1).upper()
    return ok, ratio, m, k0, M

def run(L):
    t = time.time()
    K, fr = lp(L)
    t_lp = time.time() - t
    ok, ratio, m, k0, M = certify(K, L)
    print(f"L={L} float LP ratio={fr:.5f} certified ratio<= {ratio.str(8, radius=False)} margin={float(1-ratio):.5f} "
          f"ok={ok} M={float(M):.4f} lp={t_lp:.0f}s total={time.time()-t:.0f}s", flush=True)
    return ok, ratio, m, k0, M

def save(L, ok, ratio, m, k0, M):
    h = (L - 1) // 2
    out = {"claim": "CERTIFIED (ball arithmetic, python-flint; conditional on RH): no window of L consecutive n has c_n>=0 throughout, nor c_n<=0 throughout.",
           "L": L, "h": h, "zeros_listed": N, "T": zj["T"], "T_float": float(Tb),
           "kernel_denominator": f"2^{S}", "kernel_numerators_K0_to_Kh": [str(x) for x in m],
           "k0_numerator_sum": str(k0), "K_symmetric_nonneg": True,
           "ratio_rhs_over_lhs_upper": ratio.str(10, radius=False), "margin_lower": float(1 - ratio),
           "tail_weight": tail.str(10), "w1": w1.str(10), "tail_arc_M_upper": float(M), "ok": ok,
           "flint": flint.__version__, "numpy": np.__version__, "prec_bits": ctx.prec}
    json.dump(out, open(f"{OUTDIR}/cert_L{L}.json", "w"))

if sys.argv[2] == "--bisect":
    lo, hi = int(sys.argv[3]), int(sys.argv[4])      # hi assumed to certify; lo odd
    best = None
    while hi - lo > 2:
        mid = (lo + hi) // 2; mid += 1 - mid % 2
        if mid >= hi: break
        r = run(mid)
        if r[0]: hi = mid; save(mid, *r)
        else: lo = mid
    print("smallest certified odd L:", hi)
else:
    for L in map(int, sys.argv[2:]):
        r = run(L)
        if r[0]: save(L, *r)
