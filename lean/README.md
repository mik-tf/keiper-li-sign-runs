# keiper-comb: the comb argument for runs of Keiper-Li signs (step B1, L1)

A Lean 4 / Mathlib project. It proves the logic of the argument that, under the Riemann
Hypothesis, no run of equal signs among the Keiper-Li numbers `c n` (n >= 1) is longer than 621.

## What is proved

Theorem A' (`KeiperComb.theoremA'_of_LiFormula`, with the specialisations `theoremA'_622`,
`theoremA'_622_runs`, `theoremA'_711`): from the hypotheses below, every window of `L` consecutive
`n >= 1` contains an `n` with `c n > 0` and an `n` with `c n < 0`. For `L = 622` (seven troughs or
crests, 2000 zero intervals) that says every run of one sign has length at most 621.

Pieces: `Defs` (definitions), `Comb` (the finite-support comb: a nonnegative combination of shifted
terms forces a sign change), `Tail` (Li's formula under RH splits `c n` into the first `K` zeros,
a positive-weight tail and an error that the comb absorbs), `Statement` (the theorems),
`NegTests` (the guards are not vacuous), `Axioms` (`#print axioms`).

## Hypotheses (Props in the signatures, never `axiom`)

* `RiemannHypothesis` (Mathlib): every nontrivial zero of zeta has real part 1/2.
* `LiSecondDiff c`: Li's formula in the form `HasSum` over zeros of `m_rho (1 - 1/rho)^(n-1) / rho^2 = -c n`.
* `LiWeightSum`: `sum m_rho / (rho (1 - rho)) = 2 + gamma_E - log (4 pi)` (twice `lambda_1`).
* `ZeroIntervals K lo hi`: each of the `K` rational intervals contains the ordinate of a zero `1/2 + i gamma`. Nothing more.
* `IntervalsOrdered K lo hi`: the interval data is positive, well formed and disjoint in increasing order (decidable).
  For the concrete 622 and 711 data it is PROVED in Lean (`N622.intervalsOrdered`, `N711.intervalsOrdered`, by
  `decide +kernel` on the grid ordinates: consecutive ordinates differ by more than 2050 units of 2^-30), so
  the `_numerics` theorems no longer take it as a hypothesis.
* `CombNumerics K M L a V lo hi`: the finite numeric inequalities (theta in (0, pi/2), `M * period <= L`,
  the chain vectors lie in `V`, and the bound `Nbound < 2 w0 (sum a) cos (theta0/2)` on `V`), for every
  choice of zeros in the intervals.

`CombNumerics` carries all the numerics. Today Arb certifies them; step B2 discharges them in Lean.
The chain-in-`V` fact is part of this hypothesis, not proved here. No `sorry` anywhere
(`grep -rn sorry KeiperComb/` prints nothing). `#print axioms` of the theorems shows only
`propext`, `Classical.choice`, `Quot.sound`.

## Negative tests

`NegTests.lean` proves, as ordinary facts, that a too-short window fails the bound, the conclusion
fails for a toy comb outside its window, overlapping or non-positive intervals are refused by
`IntervalsOrdered`, and a good case is accepted.

## Build

Lean toolchain in `lean-toolchain`; Mathlib is pinned in `lake-manifest.json`.

    lake build

Measured (remote builder, `nice -n 19`, 4 threads, 10 GB cap, packages prebuilt): about 3 minutes
wall, about 105 s user CPU for Defs plus Comb, peak memory 6.8 GB. An incremental rebuild of
Tail, Statement, NegTests takes under 1 minute.

## Where it goes

This project lives in `papers/keiper-li-sign-runs/lean/` (moved from `lean/keiper-comb/` after v1.1 shipped).

## Step B2: the 711 numerics, proved in Lean (tier L = 711, runs at most 710)

Proved in Lean, with no `sorry`, no `native_decide`, and only the axioms `propext`, `Classical.choice`,
`Quot.sound`:

* the comb logic (step B1), and all the numerics of the 711 tier: the zero 1 facts, the chain of nine
  integer vectors, the tail bound, and the exact integer check of the bound `N(v) < 2 w1 S cos(theta1/2)`
  over the first 2000 zero intervals. `KeiperComb.N711.combNumerics_711` is `CombNumerics 2000 8 711` for
  the concrete data, with no hypothesis.
* `KeiperComb.N711.theoremA'_711_numerics`: every window of 711 consecutive `n >= 1` has a `c n > 0` and a
  `c n < 0`, so every run of one sign has length at most 710.

Hypotheses that remain (Props in the signature, not axioms): `RiemannHypothesis`, the Li formula identities
(`LiSecondDiff c`, `LiWeightSum`), the certified zero intervals (`ZeroIntervals 2000 loQ hiQ`) and their
ordering is now proved (`intervalsOrdered`), not assumed.

## Step B3: the 622 numerics, proved in Lean (paper 2's published bound)

Lean now checks paper 2's published bound: runs of equal sign of the Keiper-Li coefficients have length at most 621
(every window of 622 consecutive `n >= 1` has a `c n > 0` and a `c n < 0`), under RH, given the Li formula identities
and the certified zero intervals. `KeiperComb.N622.theoremA'_622_numerics` and `theoremA'_622_runs_numerics`
(`M = 7`, eight chain vectors, one weight vector); `#print axioms`: propext, Classical.choice, Quot.sound only.
The 711 tier (runs at most 710) of step B2 stays as is.

Build (from this directory, no `ulimit -v`):

    LEAN_NUM_THREADS=1 lake build KeiperComb.Numerics622Assembly

The 19 chunks `Numerics622C00` to `C18` took 36.5 CPU minutes in total (largest peak 9.25 GB, C00). The assembly alone
(chunks built): 385 s, 6.9 GB peak, on a loaded server (load about 110), one thread.

Build (the numerics modules are not in the default target; run from this directory):

    LEAN_NUM_THREADS=1 lake build KeiperComb.Numerics711Assembly

Do not set `ulimit -v`: Lean maps Mathlib and fails with "failed to create thread". Each chunk module
`Numerics711C00` to `C18` (100 zeros each) builds on its own and the assembly reuses their oleans.
Measured on a loaded 28-thread server, one thread: the assembly alone (chunks already built) takes 2 min 14 s
wall and 7.0 GB peak. The 19 chunks cost about 42 minutes of CPU in total (largest single module 10 GB peak,
most about 8.3 GB), so a clean build is about 45 minutes of CPU, roughly an hour of wall on one thread.

## Fidelity review r1 fixes (2026-11-24)

* F1: `intervalsOrdered` proved by kernel `decide` for both tiers; the `_numerics` theorems drop the ordering
  hypothesis. Remaining hypotheses: RH, `LiSecondDiff c`, `LiWeightSum`, `ZeroIntervals 2000 loQ hiQ`.
* F2: the Lean intervals are `[N_k - 1025, N_k + 1025] / 2^30` with `N_k = round(mu_k 2^30)` for the stored
  midpoints `mu_k` of `../code/z2000.json`; the paper's `I_k = [mu_k - 2^-20, mu_k + 2^-20]` (2^-20 = 1024 units)
  lies inside each, so Lemma 2(a) implies `ZeroIntervals 2000 loQ hiQ` (a wider interval is a weaker
  hypothesis). This link is checked in Python, not in Lean: `python3 check_intervals.py` (exact fractions,
  2000 containments, minimum gap 104692514 units).
* F3: `c` is a parameter pinned by `LiSecondDiff` and `LiWeightSum`; Li's formula and the closed form of
  lambda_1 stay on paper (paper Lemma 1). Read the theorem as "given Li's formula", not "from RH alone".
* F4: for 622 Lean checks `CombNumerics` by the chain route: eight integer vectors `eta(u)` and `Z_1` bounded
  below by `2 w1 S cos(theta1/2)`, a stronger inequality than the paper's 1024-cell cover. The constant
  0.982921 is the Python certificate's, not Lean's (Lean's own margin is the `final_nat` integer inequality).
* F5: `AxiomsNumerics.lean` prints the axioms of `intervalsOrdered` and the 622 and 711 `_numerics` theorems;
  it and `NegTestsNumerics` form the lake target `KeiperCombNumerics` (`lake build KeiperCombNumerics`), outside
  the default target. Build logs with the `#print axioms` lines are archived in `logs/`. `leancert` is required
  by the lakefile but imported by no module; it stays only to keep the manifest and toolchain pin of the spike.
* F6: `NegTestsNumerics.lean`: the window 621 is refused (`7 P > 621`), the batch checker refuses a zero bound
  `U = 0` and a witness `rho = 0` (each with a passing control), and `final_nat` fails with the tail bound
  loosened tenfold.

## What is machine-checked (final statement, plain words)

In Lean 4 with Mathlib (v4.36.0; kernel `decide` only, no `native_decide`; axioms `propext`,
`Classical.choice`, `Quot.sound`): if RH holds, if `c n` satisfies Li's formula in the form of paper Lemma 1
(the sum over zeros for `c n`, and `sum_rho w_rho = C`), and if each of 2000 rational intervals of radius
`1025 * 2^-30` about the stored midpoints contains the ordinate of a zero of `zeta(1/2 + it)`, then every window
of 622 (and of 711) consecutive `n >= 1` contains an `n` with `c n > 0` and an `n` with `c n < 0`. The
disjointness and order of the 2000 intervals is proved in Lean. On paper stay: Li's formula, and the zeros
claim (Lemma 2(a), Arb's sign changes of Hardy's Z, whose intervals lie inside these, checked by
`check_intervals.py`). For 622 Lean checks the comb hypothesis over the eight integer vectors with the
chain bound, stronger than the cell cover, so 0.982921 is the Python certificate's.

Comparator check (Lean core `lake comparator`, nanoda and default kernel) passes for the 622 and 711 theorems: see `COMPARATOR.md` and `comparator-output.txt`.
