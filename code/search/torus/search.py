"""Run: python3 search.py K nstarts seed [out.json] [Lstart] [hops]
Per start: SLP at Lstart, then grow L by steps while margin > 0, with basin-hopping kicks at
each L (hops kicks, sigma random in {0.05,0.2,0.6}); records best L with margin>0 (K-truncated
model) and with margin>tail (robust).  Float, not certified."""
import numpy as np, sys, json, time
from torus import *
from multiprocessing import Pool

def run(args):
    K, st, seed, Ls, hops, s = args
    g, a, th, tail = setup(K, 'z1770.txt'); rng = np.random.default_rng(seed*1000+st)
    mode = st % 3
    if mode == 0: x = -(Ls/2)*th + 0.3*rng.standard_normal(K)*(np.arange(K) < 20)
    elif mode == 1: x = rng.uniform(0, 2*np.pi, K)
    else: x = -(Ls/2)*th + rng.uniform(-1, 1, K)*np.minimum(1, 0.05*np.arange(K))
    if s < 0 and mode != 1: x = x+np.pi
    L = Ls; x, m = slp(x, a, th, L, s, iters=80)
    bestrob = None; bestK = None; fails = 0; step = 4
    hist = []
    while L < 1500:
        # try to extend
        x2, m2 = slp(x, a, th, L+step, s, iters=80)
        for h in range(hops):
            if m2 > 0: break
            sig = rng.choice([0.05, 0.2, 0.6])
            xk = x + sig*rng.standard_normal(K)*np.minimum(1, 0.03*np.arange(1, K+1)[::-1]*0+1)
            xk, mk = slp(xk, a, th, L+step, s, iters=80)
            if mk > m2: x2, m2 = xk, mk
        if m2 <= 0:
            if step > 1: step = 1; continue
            break
        x, m, L = x2, m2, L+step
        hist.append((L, m-tail))
        if bestK is None or L > bestK[0]: bestK = (L, m, x.copy())
        if m > tail and (bestrob is None or L > bestrob[0]): bestrob = (L, m, x.copy())
        # also remember best robust x even if later margin below tail
    return dict(K=K, start=st, mode=mode, sign=s, tail=tail, L_K=bestK[0] if bestK else None,
                L_rob=bestrob[0] if bestrob else None,
                x_rob=bestrob[2].tolist() if bestrob else None, m_rob=bestrob[1]-tail if bestrob else None,
                x_K=bestK[2].tolist() if bestK else None, m_K=bestK[1] if bestK else None, hist=hist[-3:])

if __name__ == '__main__':
    K = int(sys.argv[1]); N = int(sys.argv[2]); seed = int(sys.argv[3]); out = sys.argv[4] if len(sys.argv) > 4 else None
    Ls = int(sys.argv[5]) if len(sys.argv) > 5 else 100; hops = int(sys.argv[6]) if len(sys.argv) > 6 else 3
    s = int(sys.argv[7]) if len(sys.argv) > 7 else 1; nproc = int(sys.argv[8]) if len(sys.argv) > 8 else 3
    t = time.time()
    with Pool(nproc) as p: res = p.map(run, [(K, i, seed, Ls, hops, s) for i in range(N)])
    for r in res: print(r['start'], r['mode'], 'L_K', r['L_K'], 'L_rob', r['L_rob'], 'm_rob', r['m_rob'], flush=True)
    print('K', K, 'best L_K', max(r['L_K'] or 0 for r in res), 'best L_rob', max(r['L_rob'] or 0 for r in res), 'time', round(time.time()-t))
    if out: json.dump(res, open(out, 'w'))
