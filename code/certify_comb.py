#!/usr/bin/env python3
"""Certificate for the trough-comb bound on sign runs of c_n (paper Theorem A).

Claim certified (CONDITIONAL ON RH): every window of L consecutive indices n >= 1 contains an n with
c_n > 0 and an n with c_n < 0, i.e. every run of one sign has length <= L - 1.
Proof sketch (see README.md): troughs t_j = t' + j P_1 of zero 1, n_j = floor(t_j + 1/2), u = frac(t'),
delta_j = c_j - u - j P_1 with c_j = floor(u + j P_1 + 1/2); weights a_j >= 0 (ONE fixed vector for all cells);
  0 <= sum a_j c_{n_j} <= -Z1(u) + sum_{k>=2} 2 w_k |B_k(u)| + W S,
  Z1(u) = 2 w_1 sum a_j cos(delta_j theta_1),  B_k(u) = sum a_j exp(i (c_j - u) theta_k)   [= exp(i(j alpha_k + delta_j theta_k))]
so R(u) = (sum 2 w_k |B_k| + W S) / Z1 < 1 for every u in [0,1] is a contradiction. Crests give the same inequality.
Two certified evaluations of R, both recorded:
  closed form (no cover):  R_M(a) = [sum_{k>=2} 2 w_k (|A(alpha_k)| + S theta_k/2) + W S] / (2 w_1 cos(theta_1/2) S)
  cover of u (dyadic cells, adaptive bisection): u a ball per cell; every integer c_j between floor(lower) and floor(upper)
  of u + j P_1 + 1/2 is tried, in every combination; upper(R) < 1 is required for every combination.
Zeros (F2, F3): z2000.json midpoints, gamma_k enclosed by [mid - 2^-20, mid + 2^-20]; Hardy Z must have strict opposite
signs at both endpoints (128 bits). No zeta_zero is used. N(T)=2000 is only a recorded consistency flag: the proof needs
RH and 2000 disjoint sign-change intervals (extra or missing zeros fall into W = C - 2 sum w_k).
All checks raise SystemExit("FAIL ..."); no assert.
Usage: python3 certify_comb.py ZEROS.json L M WEIGHTS OUT.json
  WEIGHTS: 'sine' (a_j = 2^50 sin(pi j/(M+1)) rounded down), 'flat', or a JSON file {"den_exp":50,"a":[ints]} (length M).
"""
import sys, json, time, itertools, resource, hashlib, datetime
import flint
from flint import arb, acb, ctx, fmpq

EPS_EXP = -20
DEN_EXP = 50
CELL_START_EXP = 10   # first cells have width 2^-10
CELL_MAX_EXP = 18     # bisection stops at width 2^-18
MAX_FAILS = 20

def fail(msg):
    raise SystemExit("FAIL: " + msg)

def sg(x):
    return 1 if x > 0 else (-1 if x < 0 else 0)

def Zf(t):
    s = acb(arb(1) / 2, t)
    thv = acb(arb(1) / 4, t / 2).lgamma().imag - t / 2 * arb.pi().log()
    return (acb(0, thv).exp() * s.zeta()).real

def to_int(x):
    """exact integer value of an exact arb (radius 0) integer-valued ball, else None"""
    v = x.unique_fmpz()
    return None if v is None else int(v)

def main():
    if len(sys.argv) != 6:
        raise SystemExit(__doc__)
    zfile, L, M, wspec, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
    t_start = time.time()
    ctx.prec = 128
    if not (M >= 1 and L >= 1):
        fail("bad L or M")
    # ---- step 1: zeros
    zj = json.load(open(zfile))
    N = zj["N"]
    if not (zj["count_NT"] == N == 2000 and zj["sign_changes"] == N and zj["eps_exp"] == EPS_EXP):
        fail("z2000.json header is not N = 2000, 2000 sign changes, eps 2^-20")
    T = arb(fmpq(*zj["T"]))
    def q(man, e):
        return fmpq(man * 2 ** e, 1) if e >= 0 else fmpq(man, 2 ** (-e))
    mids = [arb(q(l[0], l[1])) for l in zj["gamma_mid_man_exp_rad_man_exp"]]
    if len(mids) != N:
        fail("number of midpoints")
    eps = arb(2) ** EPS_EXP
    pm1 = arb(-1).union(arb(1))
    t0 = time.time()
    for i, g in enumerate(mids):
        if not (g - eps) > 0:
            fail(f"zero {i+1} interval not positive")
        if not sg(Zf(g - eps)) * sg(Zf(g + eps)) == -1:
            fail(f"no Hardy Z sign change at the endpoints of interval {i+1}")
        nxt = mids[i + 1] - eps if i + 1 < N else T
        if not (g + eps) < nxt:
            fail(f"interval {i+1} overlaps the next one (or exceeds T)")
    t_zeros = time.time() - t0
    cnt = T.zeta_nzeros()
    count_consistent = bool(cnt == N and cnt.rad() == 0)   # recorded only (F3)
    gam = [g + eps * pm1 for g in mids]
    one = arb(1)
    w = [one / (one / 4 + g * g) for g in gam]
    th = [2 * (one / (2 * g)).atan() for g in gam]
    # ---- step 2: constants
    C = 2 + arb.const_euler() - (4 * arb.pi()).log()
    W = C - 2 * sum(w, arb(0))
    if not W > 0:
        fail("W not positive")
    Wu = W.upper()
    P1 = 2 * arb.pi() / th[0]
    if not (M * P1).upper() <= L:
        fail(f"M P_1 upper end {float((M*P1).upper())} exceeds L = {L}: the window may not hold M troughs")
    # ---- weights (one fixed vector for all cells)
    if wspec == "sine":
        a_int = [int(((arb.pi() * j / (M + 1)).sin() * arb(2) ** DEN_EXP).mid().floor().unique_fmpz() + 0) for j in range(1, M + 1)]
        wmode = "sine rounded down to integers over 2^50"
    elif wspec == "flat":
        a_int = [2 ** DEN_EXP] * M
        wmode = "flat"
    else:
        wj = json.load(open(wspec))
        if wj["den_exp"] != DEN_EXP:
            fail("weights den_exp must be 50")
        a_int = [int(x) for x in wj["a"]]
        wmode = "file " + wspec.split("/")[-1]
    if len(a_int) != M:
        fail("weights length != M")
    if not all(x >= 0 for x in a_int) or not sum(a_int) > 0:
        fail("weights must be >= 0 with positive sum")
    a = [arb(x) / arb(2) ** DEN_EXP for x in a_int]   # exact
    S = sum(a, arb(0))
    Su = S.upper()
    # ---- step 3a: closed form R_M(a) (no cover)
    t0 = time.time()
    al = [2 * arb.pi() * th[k] / th[0] for k in range(N)]
    num = W * S
    for k in range(1, N):
        re = arb(0); im = arb(0)
        for j in range(M):
            e = acb(0, al[k] * j).exp(); c, s = e.real, e.imag
            re += a[j] * c; im += a[j] * s
        absA = acb(re, im).abs_upper()
        num += 2 * w[k] * (absA + S * th[k] / 2)
    den = 2 * w[0] * (th[0] / 2).cos() * S
    if not den.lower() > 0:
        fail("closed form denominator not positive")
    Rcf = (num / den).upper()
    closed_ok = bool(Rcf < 1)
    t_closed = time.time() - t0
    # ---- step 3b: cover of u in [0,1]
    t0 = time.time()
    half = arb(1) / 2
    jP = [P1 * j for j in range(M)]
    stack = [(i, CELL_START_EXP) for i in range(2 ** CELL_START_EXP - 1, -1, -1)]
    done = []          # (i, k) certified cells
    cell_rec = []
    fails = []
    ncells = 0; n_ambig = 0; n_combos = 0; max_depth = CELL_START_EXP
    worst = None       # (margin float, i, k)
    two = arb(2)
    while stack:
        i, k = stack.pop()
        ncells += 1
        u = arb(fmpq(2 * i + 1, 2 ** (k + 1))) + arb(2) ** (-(k + 1)) * pm1
        cands = []
        for j in range(M):
            x = u + jP[j] + half
            lo = to_int(x.lower().floor()); hi = to_int(x.upper().floor())
            if lo is None or hi is None:
                fail("cannot take floor of cell endpoints")
            if hi - lo > 1:
                fail(f"cell ({i},{k}) too wide: more than two floor candidates for j={j}")
            cands.append(list(range(lo, hi + 1)))
        ambiguous = any(len(c) > 1 for c in cands)
        if ambiguous:
            n_ambig += 1
        cell_Rup = None
        cell_combos = 0
        for combo in itertools.product(*cands):
            n_combos += 1
            cell_combos += 1
            Z1 = arb(0)
            for j in range(M):
                d = combo[j] - u - jP[j]
                Z1 += a[j] * (d * th[0]).cos()
            Z1 = 2 * w[0] * Z1
            if not Z1.lower() > 0:
                cell_Rup = None; break
            nn = W * S
            for kk in range(1, N):
                re = arb(0); im = arb(0)
                for j in range(M):
                    e = acb(0, (combo[j] - u) * th[kk]).exp(); c, s = e.real, e.imag
                    re += a[j] * c; im += a[j] * s
                nn += 2 * w[kk] * acb(re, im).abs_upper()
            Rup = (nn / Z1).upper()
            if cell_Rup is None or Rup > cell_Rup:
                cell_Rup = Rup
        if cell_Rup is not None and cell_Rup < 1:
            done.append((i, k))
            cell_rec.append([i, k, cell_Rup.upper().str(15, radius=False), "ambiguous_floor" if ambiguous else "unique_floor", cell_combos])
            mg = float((1 - cell_Rup).mid())
            if worst is None or mg < worst[0]:
                worst = (mg, i, k, float(cell_Rup.mid()))
            continue
        if k < CELL_MAX_EXP:
            stack.append((2 * i + 1, k + 1)); stack.append((2 * i, k + 1))
            max_depth = max(max_depth, k + 1)
        else:
            rr = float(cell_Rup.mid()) if cell_Rup is not None else None
            fails.append({"i": i, "k": k, "R_upper": rr})
            if len(fails) >= MAX_FAILS:
                break
    t_cover = time.time() - t0
    # cover check: cells of `done` are disjoint dyadic intervals; they must tile [0,1] exactly
    from fractions import Fraction
    tot = sum(Fraction(1, 2 ** k) for (i, k) in done)
    segs = sorted((Fraction(i, 2 ** k), Fraction(i + 1, 2 ** k)) for (i, k) in done)
    tiled = all(segs[x][1] == segs[x + 1][0] for x in range(len(segs) - 1)) and bool(segs) and segs[0][0] == 0 and segs[-1][1] == 1
    cover_ok = bool(not fails and not stack and tot == 1 and tiled)
    status = "PASS" if (cover_ok or closed_ok) else "FAIL"
    def sha(p):
        return hashlib.sha256(open(p, "rb").read()).hexdigest()
    cells = []
    for (ci, ck, rstr, fcase, ncomb) in sorted(cell_rec, key=lambda r: r[0] / 2 ** r[1]):
        cells.append({"u_lo": f"{ci}/{2 ** ck}", "u_hi": f"{ci + 1}/{2 ** ck}", "R_upper": rstr, "floor_case": fcase, "combos": ncomb})
    res = {
        "zeros_file_sha256": sha(zfile), "weights_file_sha256": sha(wspec) if wspec not in ("sine", "flat") else None,
        "script_sha256": sha(sys.argv[0]), "run_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "status": status, "conditional_on": "RH",
        "claim": f"every window of {L} consecutive n >= 1 contains both signs of c_n" if status == "PASS" else "NOT certified",
        "L": L, "M_troughs": M, "weights": wmode, "weights_mode": "single vector, all cells", "weights_int_over_2^50": a_int,
        "zero_interval_eps": "2^-20", "zeros_used": N, "z2000_hardy_Z_sign_changes_2000": True,
        "N_T_count_consistent_recorded_only": count_consistent,
        "W_upper": float(Wu), "P1": float(P1.mid()), "P1_rad": float(P1.rad()), "M_P1_upper": float((M * P1).upper()),
        "closed_form": {"R_upper": float(Rcf), "R_upper_str": Rcf.str(15, radius=False), "margin_1_minus_R": float(1 - Rcf), "pass": closed_ok},
        "cover": {"pass": cover_ok, "cells": len(done), "cells_evaluated": ncells, "ambiguous_cells": n_ambig, "combos_evaluated": n_combos,
                  "start_width": f"2^-{CELL_START_EXP}", "min_width": f"2^-{max_depth}", "max_allowed_depth": CELL_MAX_EXP,
                  "tiles_0_1_exactly": tiled, "failed_cells": fails,
                  "worst_cell": None if worst is None else {"i": worst[1], "k": worst[2], "u_lo": worst[1] / 2 ** worst[2], "u_hi": (worst[1] + 1) / 2 ** worst[2], "margin": worst[0], "R_upper": worst[3]},
                  "R_upper_max": None if worst is None else worst[3],
                  "min_margin_1_minus_R": None if worst is None else worst[0]},
        "cells": cells,
        "prec_bits": 128,
        "python_flint_version": flint.__version__, "python_version": sys.version, "argv": " ".join(sys.argv), "python_O": not __debug__,
        "time_zeros_s": t_zeros, "time_closed_s": t_closed, "time_cover_s": t_cover, "time_total_s": time.time() - t_start,
        "peak_rss_kb_self": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k not in ("cells", "weights_int_over_2^50")}))
    if status != "PASS":
        raise SystemExit("FAIL: neither the closed form nor the cover certifies R < 1 (see JSON)")

main()
