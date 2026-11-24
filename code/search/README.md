# Search code (not part of the proof)

These scripts found the witness integers in `../witness_pos312.txt` and `../witness_neg312.txt`. The proof does not use them: `../certify_witness.py` reads only `z2000.json` and the witness file.

How it was run, from this directory, with python-flint:

- `w_targets.py TORUS_DIR OUT_DIR K` writes a float phase target for K zeros. It needs `torus.py` and `z1770.txt` from the Theorem C phase search, shipped in `torus/` (pass `torus` as TORUS_DIR).
- `w_lattice.py TARGET_DIR OUT_JSON K:D=1250:pos` (or `:neg`, which uses the target shifted by pi) builds the lattice and reduces it with LLL (python-flint `fmpz_mat.lll`). K = 300, D = 1250 digits gave both witnesses.
- `w1_negcheck.py OUT_JSON` counts the negative run length of a negative job.

Cost: about 3 to 4 CPU hours per witness.
