"""F2 check: each paper interval I_k = [mu_k - 2^-20, mu_k + 2^-20] (mu_k = z2000.json midpoint) lies inside
the Lean interval [(N_k - 1025)/2^30, (N_k + 1025)/2^30], N_k = round(mu_k 2^30); also the Lean intervals
are disjoint and increasing (the same fact Lean proves as `intervalsOrdered`). Run from this directory."""
import json
from fractions import Fraction
z = json.load(open("../code/z2000.json"))
rows = z["gamma_mid_man_exp_rad_man_exp"]
assert len(rows) == 2000
Ns = []
for man, e, *_ in rows:
    mu = Fraction(man) * Fraction(2) ** e
    N = round(mu * 2 ** 30)
    r = Fraction(1, 2 ** 20)
    assert Fraction(N - 1025, 2 ** 30) <= mu - r and mu + r <= Fraction(N + 1025, 2 ** 30)
    Ns.append(N)
assert all(Ns[k] + 2050 < Ns[k + 1] for k in range(1999))
print("ok: 2000 containments, min gap", min(Ns[k + 1] - Ns[k] for k in range(1999)), "units of 2^-30")
