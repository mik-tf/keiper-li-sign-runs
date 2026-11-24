#!/usr/bin/env python3
"""Floating-point implementation check of the Theorem A comb certificate. NOT a proof.

Independent of certify_comb.py (no import, no flint): numpy double precision, exact sup by pieces.
For a cell [lo,hi] of u the integers c_j = floor(u + j P_1 + 1/2) are constant between breakpoints, and on a piece
  R(u) = (sum_k 2 w_k |B_k| + W S) / Z1(u),  |B_k| independent of u,  Z1(u) = 2 w_1 sum a_j cos((c_j - u - j P_1) theta_1)
with Z1 concave where positive, so the sup of R on a piece is at its end points. We evaluate every piece end point
(both one-sided limits at a breakpoint), take the max per cell, and compare with the certified upper bounds in
cert_comb_622.json and cert_comb_711.json: max |difference| over cells and the two sups.
Usage: python3 crosscheck_comb.py CODE_DIR --json OUT.json        (CODE_DIR holds z2000.json, weights_622.json, cert_comb_*.json)
"""
import sys, json, math
from fractions import Fraction
import numpy as np

def pieces(lo, hi, P, M):
    """breakpoints of floor(u + j P + 1/2) inside (lo,hi), j<M"""
    bp = {lo, hi}
    for j in range(M):
        x0 = lo + j * P + 0.5
        n = math.floor(x0) + 1
        while n - j * P - 0.5 < hi:
            u = n - j * P - 0.5
            if lo < u < hi: bp.add(u)
            n += 1
    return sorted(bp)

def main():
    d = sys.argv[1]
    out = sys.argv[sys.argv.index("--json") + 1]
    z = json.load(open(d + "/z2000.json"))
    g = np.array([l[0] * 2.0 ** l[1] for l in z["gamma_mid_man_exp_rad_man_exp"]])
    w = 1.0 / (0.25 + g * g)
    th = 2 * np.arctan(1.0 / (2 * g))
    C = 2 + 0.5772156649015329 - math.log(4 * math.pi)
    W = C - 2 * w.sum()
    P1 = 2 * math.pi / th[0]
    res = {"kind": "floating point implementation check, not a proof", "tiers": {}}
    for L, name in ((622, "cert_comb_622.json"), (711, "cert_comb_711.json")):
        c = json.load(open(d + "/" + name))
        M = c["M_troughs"]
        ai = c["weights_int_over_2^50"]
        if L == 622:
            if json.load(open(d + "/weights_622.json"))["a"] != ai: raise SystemExit("FAIL weights differ")
        a = np.array([x / 2.0 ** 50 for x in ai]); S = a.sum()
        cells = c["cells"] if "cells" in c else None
        if cells is None: raise SystemExit("FAIL no cells in " + name)
        diffs = []; fsup = 0.0; csup = 0.0; viol = 0
        for cell in cells:
            lo = float(Fraction(cell["u_lo"])); hi = float(Fraction(cell["u_hi"]))
            Rc = float(cell["R_upper"])
            best = 0.0
            bp = pieces(lo, hi, P1, M)
            for p0, p1 in zip(bp[:-1], bp[1:]):
                um = (p0 + p1) / 2
                cj = np.floor(um + np.arange(M) * P1 + 0.5)
                ph = np.exp(1j * np.outer(th, cj))            # (N, M)
                Bk = np.abs(ph @ a)
                num = (2 * w[1:] * Bk[1:]).sum() + W * S
                for u in (p0, p1):
                    Z1 = 2 * w[0] * (a * np.cos((cj - u - np.arange(M) * P1) * th[0])).sum()
                    best = max(best, num / Z1)
            diffs.append(abs(Rc - best)); fsup = max(fsup, best); csup = max(csup, Rc)
            if best > Rc + 1e-12: viol += 1
        r9 = lambda x: float("%.9g" % x)
        res["tiers"][str(L)] = {"cells": len(cells), "max_abs_diff_per_cell": r9(max(diffs)), "float_sup": r9(fsup),
                                "certified_sup": r9(csup), "cells_float_above_certified": viol,
                                "float_below_one": bool(fsup < 1)}
        print(L, res["tiers"][str(L)])
    json.dump(res, open(out, "w"), indent=1)
main()
