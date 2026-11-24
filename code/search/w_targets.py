"""W pilot step A: phase targets x* per K (float SLP search, not certified).
Usage: python w_targets.py TORUS_DIR OUT_DIR K [K ...]
TORUS_DIR holds torus.py and z1770.txt (the Theorem C phase-search module, in torus/).
K=100 is taken from cert_run_pos_K100.json by w_lattice.py; this script is for K<100 (and any other K).
Writes OUT_DIR/target_K{K}.json: x (floats), L, margin m = min F - T_K, tail."""
import sys, json, numpy as np
sys.path.insert(0, sys.argv[1]); import torus
out = sys.argv[2]
for K in map(int, sys.argv[3:]):
    g, a, th, tail = torus.setup(K, sys.argv[1] + '/z1770.txt')
    best = None
    for seed in range(6):
        rng = np.random.default_rng(seed)
        L0 = 40
        x = -(L0/2)*th + 0.3*rng.standard_normal(K)*(np.arange(K) < 20) if seed % 2 == 0 else rng.uniform(0, 2*np.pi, K)
        x, m = torus.slp(x, a, th, L0, 1)
        if m - tail <= 0: continue
        L, x, m = torus.grow(x, a, th, tail, L0, 1, step=4, Lmax=400, verbose=False)
        if best is None or L > best[0]: best = (L, x, m)
    if best is None:
        print(K, 'no robust run at L0=40'); continue
    L, x, m = best
    json.dump({'K': K, 'L': L, 'x': list(map(float, x)), 'margin': float(m - tail), 'tail': float(tail)}, open(f'{out}/target_K{K}.json', 'w'))
    print(K, 'L', L, 'margin', m - tail, flush=True)
