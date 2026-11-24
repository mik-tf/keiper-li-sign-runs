#!/usr/bin/env python3
"""Sign changes of c_n = l_{n+1} - 2 l_n + l_{n-1} from Johansson's 20-digit
Keiper-Li table. Line k+1 (0-based index k) holds lambda_k/k (Keiper normalisation),
k=1..100000; line 1 is a placeholder (-log 2), and lambda_0 = 0.  Usage: table_sign_changes.py TABLE [OUT.json]
CHECKED NUMERICALLY (finite range), not certified.  Output: derived counts only."""
import sys, json
from decimal import Decimal, getcontext
getcontext().prec = 60
path = sys.argv[1]
out = sys.argv[2] if len(sys.argv) > 2 else "table_sign_changes.json"
T = [Decimal(s.strip()) for s in open(path) if s.strip()]
L = [Decimal(0)] + [T[k] * k for k in range(1, len(T))]  # lambda_k = k * table value
M = len(L) - 1  # last index
def half_ulp(k):  # rounding half-unit of lambda_k = k * (20-significant-digit table value)
    x = T[k]
    if x == 0: return Decimal(0)
    return k * Decimal(10) ** (x.adjusted() - 19) / 2
c, err = {}, {}
for n in range(1, M):
    c[n] = L[n+1] - 2*L[n] + L[n-1]
    err[n] = half_ulp(n+1) + 2*half_ulp(n) + half_ulp(n-1)
sgn = {n: (c[n] > 0) - (c[n] < 0) for n in c}
# a sign is uncertain if |c| <= worst-case rounding error
uncertain = [n for n in c if abs(c[n]) <= err[n]]
def S(a, b):  # sign changes between consecutive n in [a,b] (pairs (n-1,n) both in range)
    return sum(1 for n in range(a+1, b+1) if sgn[n] != sgn[n-1])
th = 0.0225103222285  # theta_1/pi
lo, hi = 0.969481285147, 0.971027176735
Ns = [1000, 3000, 10000, 30000, 100000]
rows = []
for N in Ns:
    Nv = min(N, M-1)
    s = S(1, Nv); st = S(Nv//2, Nv)
    unc = [n for n in uncertain if n <= Nv]
    rows.append(dict(N_requested=N, N_used=Nv, S=s, bound=th*Nv, ratio=s/(th*Nv),
        tail_range=[Nv//2, Nv], S_tail=st, tail_ratio=st/(th*(Nv-Nv//2)),
        tail_ratio_in_thmD_bracket=lo <= st/(th*(Nv-Nv//2)) <= hi,
        n_uncertain_signs=len(unc)))
res = dict(label="CHECKED NUMERICALLY (finite range), not certified",
    source="Johansson 20-digit lambda_n table, lines k=1..%d, value lambda_k/k (values not stored)" % M,
    definition="S(N) = #{n in [2,N]: sign c_n != sign c_{n-1}}, c_n for n=1..%d" % (M-1),
    theta1_over_pi=th, thmD_bracket=[lo, hi], rows=rows,
    precision=dict(model="worst-case rounding of 20 significant digits: half-ulp(l_{n+1})+2 half-ulp(l_n)+half-ulp(l_{n-1})",
        uncertain_n=uncertain, n_zero_c=sum(1 for n in c if c[n]==0),
        min_abs_c_over_err=float(min(abs(c[n])/err[n] for n in c)),
        argmin_n=min(c, key=lambda n: abs(c[n])/err[n]),
        max_err=float(max(err.values()))))
json.dump(res, open(out, "w"), indent=1)
for r in rows: print(r)
print("uncertain:", uncertain[:20], len(uncertain), "min|c|/err", res["precision"]["min_abs_c_over_err"], "at", res["precision"]["argmin_n"], "max_err", res["precision"]["max_err"])
