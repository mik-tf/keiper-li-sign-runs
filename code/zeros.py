"""Step 1: rigorous zeros of zeta (python-flint = FLINT/Arb), completeness and simplicity check.
Usage: python zeros.py NZEROS out.json
Certified part (ball arithmetic):
  * Arb acb.zeta_zeros(1, N+1): N+1 isolated zeros on the critical line (Arb, Turing/Platt isolation).
  * T = dyadic point strictly between zero N and zero N+1.
  * arb.zeta_nzeros(T) = N(T), the number of zeros (with multiplicity) in 0<Im<=T, rigorous per Arb
    docs (Turing's method, Trudgian's S(t) bound; from memory, check). It must be the exact integer N.
  * Independent of Arb's isolation: Hardy Z(t) evaluated in balls at mid-eps and mid+eps for every
    listed zero must be nonzero with opposite signs. So each disjoint interval holds a zero of Z, hence N
    distinct zeros, hence (count = N(T)) every zero up to T is listed, on the line, and simple.
"""
import sys, json
from flint import acb, arb, ctx, fmpz, fmpq
import flint
N = int(sys.argv[1]); out = sys.argv[2]
ctx.prec = 200
zs = acb.zeta_zeros(1, N + 1)
g = []
for z in zs:
    assert z.real == arb(1) / 2 and z.real.rad() == 0, "real part not exactly 1/2"
    g.append(z.imag)
for a, b in zip(g, g[1:]):
    assert a < b, "balls overlap/not ordered"
# T dyadic between zero N and N+1
lo = g[N - 1].upper(); hi = g[N].lower()
T = ((lo + hi) / 2)
T = arb(T.mid()) if T.rad() != 0 else T
# round T to a short dyadic
Tq = fmpq(int((T * 2**20).floor().unique_fmpz()), 2**20)
Tb = arb(Tq)
assert g[N - 1] < Tb < g[N]
cnt = Tb.zeta_nzeros()
print("N(T) =", cnt, "T =", Tq)
assert cnt == N and cnt.rad() == 0, "count mismatch"
# Hardy Z sign check
pi = arb.pi()
def Z(t):
    t = arb(t)
    th = (acb(0.25, 0) + acb(0, 1) * t / 2).lgamma().imag - t / 2 * pi.log()
    return (acb(0, th).exp() * acb(arb(1) / 2, t).zeta()).real
eps = arb(2) ** -20
signs = 0
for i in range(N):
    m = arb(g[i].mid())
    a, b = Z(m - eps), Z(m + eps)
    ok = (a > 0 and b < 0) or (a < 0 and b > 0)
    assert ok, f"no certified sign change at zero {i+1}"
    assert g[i].rad() < eps / 4
    if i:
        prev_hi = arb(g[i - 1].mid()) + eps
        if not prev_hi < m - eps:
            raise SystemExit(f"intervals {i} and {i+1} not disjoint")
    signs += 1
print("sign-change intervals:", signs)
def me(x):
    m, e = x.mid().man_exp(); r = x.rad().man_exp()
    return [int(m), int(e), int(r[0]), int(r[1])]
json.dump({"N": N, "T": [int(Tq.p), int(Tq.q)], "count_NT": N, "sign_changes": signs,
           "flint": flint.__version__, "prec": 200, "eps_exp": -20,
           "gamma_mid_man_exp_rad_man_exp": [me(x) for x in g[:N]]}, open(out, "w"))
print("max radius", max(float(x.rad()) for x in g[:N]), "gamma_N", g[N-1].str(15, radius=False))
