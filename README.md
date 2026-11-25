# Sign runs and the density of sign changes of Keiper-Li second differences

Author: Michaël Perreault

DOI: [10.5281/zenodo.24486137](https://doi.org/10.5281/zenodo.24486137) (all versions; v1.0 is [10.5281/zenodo.24486138](https://doi.org/10.5281/zenodo.24486138); v1.0.1 is [10.5281/zenodo.24487613](https://doi.org/10.5281/zenodo.24487613))

Let lambda_n be the Keiper-Li coefficients and c_n = lambda_(n+1) - 2 lambda_n + lambda_(n-1) their second differences. It is known unconditionally that c_n changes sign infinitely often. This paper asks how long a run of one sign can be and how often the sign changes. Every result is conditional; the conditions are stated with each result.

- **A.** Assuming the Riemann hypothesis (RH), every window of 622 consecutive indices contains both a positive and a negative c_n, so no run of one sign is longer than 621. (Versions 1.0 and 1.0.1 proved 1572.) Since version 1.2.1, the deduction of this theorem from RH, Li's formula and the certified zero intervals is also checked in Lean 4, see `lean/README.md`.
- **B.** Assuming RH, there are runs of at least 312 consecutive values of each sign (positive and negative), and they have positive lower density. Computer-assisted: two explicit witnesses are certified in ball arithmetic.
- **C.** Assuming RH and a linear independence hypothesis on the angles of the first 700 zeros, runs of 392 consecutive values of each sign occur with positive lower density; with the first 1400 zeros, runs of 476.
- **D.** Assuming RH and the independence of pi and all the angles over the rationals, the sign changes of c_n have a density, and its ratio to theta_1/pi lies in [0.969481285147, 0.971027176735], in particular below 1.

Paper: [sign-runs-and-the-density-of-sign-changes-of-keiper-li-second-differences.pdf](sign-runs-and-the-density-of-sign-changes-of-keiper-li-second-differences.pdf) (source: [paper.md](paper.md)). Appendix B of the paper lists every certificate and the command that reproduces it. This paper continues the [note on sign changes of Keiper-Li second differences](https://doi.org/10.5281/zenodo.24447746).

## Licences

- Text (`paper.md`, the PDF) and the archived certificates: CC BY 4.0, see [LICENSE-paper.md](LICENSE-paper.md).
- Code in `code/` and the figure scripts: MIT, see [LICENSE](LICENSE).

## Rebuild the PDF

The paper was built from `paper.md` with mdtexpdf, a Markdown-to-LaTeX converter (pdfLaTeX). Rebuilding the PDF is optional; the certificate code in `code/` runs on its own.

## Re-run the certificates

Python 3.12 with python-flint 0.9.0 (Arb, 128-bit balls), numpy 2.5.5 and scipy 1.18.1. Run from the repository root with `P=code`; each command writes to the directory `OUT`, never to the archived files in `code/`. An archived file differs from a re-run only in timing fields. The heaviest step, the density certificate, needs 16 GB of memory.

```
P=code; OUT=out; mkdir -p $OUT
python3 $P/zeros.py 2000 $OUT/z2000.json
python3 $P/certify_comb.py $P/z2000.json 622 7 $P/weights_622.json $OUT/cert_comb_622.json
python3 $P/certify_comb.py $P/z2000.json 711 8 sine $OUT/cert_comb_711.json
python3 $P/certify_witness.py $P $P/witness_pos312.txt 300 312 1 $OUT/cert_witness_pos312.json
python3 $P/certify_witness.py $P $P/witness_neg312.txt 300 312 -1 $OUT/cert_witness_neg312.json
python3 $P/certify_run.py $P/z2000.json $P/torus_results.json $OUT
python3 $P/certify_density.py $P/z2000.json $OUT/density_results.json --workers 16 --floatcheck $P
python3 $P/crosscheck_comb.py $P --json $OUT/crosscheck_comb.json
```

What each one certifies: `zeros.py` the zero list; the two `certify_comb.py` runs Theorem A (622 with seven troughs, and 711 for the closed form of the remark after it; about 90 s each); the two `certify_witness.py` runs Theorem B (about 90 s each); `certify_run.py` Theorem C (about 15 s); `certify_density.py` Theorem D (about 2 minutes on 16 workers); `crosscheck_comb.py` an independent floating point check of Theorem A. The optional search code that found the witnesses and phases is in `code/search/` (not part of any proof). Figure data: `python3 $P/make_figure_data.py` reads only the archived files.

## Cite as

Perreault, M. Sign runs and the density of sign changes of Keiper-Li second differences, version 1.2.1. https://github.com/mik-tf/keiper-li-sign-runs (DOI: [10.5281/zenodo.24486137](https://doi.org/10.5281/zenodo.24486137) (all versions; v1.0 is [10.5281/zenodo.24486138](https://doi.org/10.5281/zenodo.24486138))). See [CITATION.cff](CITATION.cff).
