"""Collect out/*.json into results.json (best per K, sign) and verify x_rob independently."""
import json, glob, numpy as np
from torus import setup
out = {}; curve = []
for f in sorted(glob.glob('out/*.json')):
    res = json.load(open(f)); K = res[0]['K']; s = res[0]['sign']
    b = max(res, key=lambda r: r['L_rob'] or 0)
    g, a, th, tail = setup(K, 'z1770.txt')
    L = b['L_rob']; x = np.array(b['x_rob']); n = np.arange(L)
    F = s*(np.cos(np.outer(n, th)+x) @ a)
    row = dict(K=K, sign=s, tail=tail, L_robust=L, L_truncated_model=max(r['L_K'] or 0 for r in res),
               n_starts=len(res), min_F_over_run=float(F.min()), margin_over_tail=float(F.min()-tail),
               gamma_K=float(g[-1]), x_robust=b['x_rob'], window='n=0..L-1 (shift-equivalent)')
    out[f'{"pos" if s>0 else "neg"}_K{K}'] = row
    print(row['sign'], K, 'tail %.2e' % tail, 'L_rob', L, 'L_trunc', row['L_truncated_model'], 'verified margin %.2e' % row['margin_over_tail'])
json.dump(out, open('results.json', 'w'), indent=1)
