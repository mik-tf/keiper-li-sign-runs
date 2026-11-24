# (a') torus run search (float, NOT certified)

Question: how long can a one-signed run of the model F_x(n) = sum_{g>0} 2 w_g cos(n th_g + x_g) be, over phases x on the torus?
(w_g = 1/(1/4+g^2), th_g = 2 arctan(1/(2g)), g = zeta zeros from `z1770.txt`, first 1770.) Under RH and LI_theta this torus
supremum is the worst case L_opt for c_n.

Robust run: window n = 0..L-1 (shift-equivalent: n -> n+m moves x_g by m th_g) with min_n F_K(n) > T_K,
T_K = 2 lam1 - sum_{k<=K} 2 w_k (lam1 = 1 + gamma_E/2 - log(4 pi)/2). Then F (all zeros) > 0 on the window whatever the tail phases.
"L_trunc" is the same without the tail (K-zero model only; not robust).

## Method
`torus.py`: sequential LP (linearise cos around x, trust region, maximise t with F_x(n) + J dx >= t on the window, scipy HiGHS).
`search.py`: starts (centred x=0 perturbed / random uniform / centred plus partial noise), SLP at L=100, grow L by 4 then 1 while
the max-min margin > 0, basin-hopping kicks (sigma 0.05/0.2/0.6) when growth fails. `collect.py` re-evaluates the stored phases from
scratch and writes `results.json`. Negative runs: x -> x + pi flips F -> -F, so on the torus the negative supremum equals the positive
one exactly; `sign=-1` runs (K=100, 300) confirm numerically (same values).

## Run
    python3 -m venv venv && venv/bin/pip install numpy scipy
    OMP_NUM_THREADS=1 venv/bin/python search.py K NSTARTS SEED out/pos_K$K.json 100 HOPS 1 NPROC   # sign=+1; -1 for negative
    python3 collect.py          # reads out/*.json, verifies, writes results.json

## Results (best robust run per K; `margin` = min F over run minus T_K, in absolute units; total mass 2 lam1 = 0.0462)
| K | gamma_K | tail T_K | L robust | L truncated model | margin | starts |
|---|---|---|---|---|---|---|
| 100 | 236.52 | 6.2e-3 | 208 | 315 | 5.6e-4 | 6 (+2 neg) |
| 150 | | 4.9e-3 | 224 | 325 | 2.1e-4 | 3 |
| 200 | | 4.1e-3 | 232 | 330 | 1.7e-4 | 3 |
| 250 | | 3.6e-3 | 304 | 398 | 7.0e-5 | 3 |
| 300 | | 3.2e-3 | 312 | 407 | 1.1e-4 | 3 (+2 neg, same) |
| 400 | | 2.7e-3 | 320 | 415 | 2.5e-4 | 3 |
| 500 | | 2.3e-3 | 324 | 477 | 4.4e-4 | 3 |
| 700 | | 1.8e-3 | 392 | 487 | 4.2e-5 | 1 |
| 1000 | | 1.4e-3 | 412 | 495 | 2.2e-5 | 1 |
| 1400 | 1871 | 1.1e-3 | 476 | 500 | 6.3e-5 | 1 |
| 1770 | | 1.0e-3 | not finished (killed after 2 h) | | | 1 |

Best: positive and negative run both 476 at K=1400 (negative by the x+pi symmetry). Phases: key `pos_K1400`, `x_robust` of `../../torus_results.json`
(1400 values, window n=0..475).

## Reading the results
The robust run grows with K because the worst-case tail bound T_K shrinks, not because the truncated model changes (L_trunc is 315 to 500).
A sharper tail bound that uses the fact that tail zeros have th < 1/gamma_K could raise the small-K numbers; not done.

## Caveats
All starts converged to the same value at each K (K<=500), but this is a search: a LOWER bound only. Search is greedy in L, K >= 700 had one start and one hop.
Float64, not certified: margins down to 2e-5 are far above rounding (1e-16) but nothing is interval-checked. The zero list `z1770.txt` is float, not certified.
