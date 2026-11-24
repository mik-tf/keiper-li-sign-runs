"""(a') torus run search for F_x(n)=sum_{g>0} 2 w_g cos(n th_g + x_g), float (not certified).
Window is [0,L) WLOG (shift n -> n+m moves x_g by m*th_g).  A run is robust if
min_n F_K(n) > T_K = 2*lam1 - sum_{k<=K} 2 w_k  (sign=+1; sign=-1 uses -F).
Method: sequential LP (linearise cos around x, trust region, maximise t s.t. F+J dx >= t),
starts: x=0 window centred, perturbed, and random; then grow L.
"""
import numpy as np, sys, json, time
from scipy.optimize import linprog
LAM1 = 1 + np.euler_gamma/2 - 0.5*np.log(4*np.pi)

def setup(K, zfile):
    g = np.loadtxt(zfile)[:K]
    w = 1/(0.25+g**2); th = 2*np.arctan(1/(2*g))
    tail = 2*LAM1 - 2*w.sum()
    return g, 2*w, th, tail

def Fval(x, a, th, n, s=1):
    return s*(np.cos(np.outer(n, th)+x) @ a)

def slp(x, a, th, L, s=1, iters=60, tr=0.5, n0=0):
    """maximise min_{n in [n0,n0+L)} s*F_x(n) by sequential LP; returns x, margin."""
    n = np.arange(n0, n0+L); K = len(a)
    best = Fval(x, a, th, n, s).min(); bx = x.copy()
    for it in range(iters):
        ph = np.outer(n, th)+x
        F0 = s*(np.cos(ph) @ a)
        J = -s*np.sin(ph)*a            # dF/dx
        # vars: dx (K), t ; max t  s.t. F0 + J dx >= t
        c = np.zeros(K+1); c[-1] = -1
        A = np.hstack([-J, np.ones((L, 1))]); b = F0
        bnds = [(-tr, tr)]*K+[(None, None)]
        r = linprog(c, A_ub=A, b_ub=b, bounds=bnds, method='highs')
        if r.status != 0: tr /= 2; continue
        xn = x + r.x[:K]
        v = Fval(xn, a, th, n, s).min()
        if v > best + 1e-13:
            best, bx, x = v, xn.copy(), xn; tr = min(tr*1.5, 1.0)
        else:
            tr /= 2
            if tr < 1e-6: break
    return bx, best

def grow(x, a, th, tail, L, s, step=4, Lmax=2000, verbose=True):
    """grow window while robust margin > 0; returns (L, x, margin)"""
    x, m = slp(x, a, th, L, s)
    while m - tail > 0 and L < Lmax:
        x2, m2 = slp(x, a, th, L+step, s)
        if m2 - tail <= 0:
            # try a smaller step once
            x3, m3 = slp(x, a, th, L+1, s)
            if m3-tail <= 0: break
            x, m, L = x3, m3, L+1; continue
        x, m, L = x2, m2, L+step
        if verbose: print(f'  L={L} margin={(m-tail):.3e}', flush=True)
    return L, x, m

if __name__ == '__main__':
    K = int(sys.argv[1]); s = int(sys.argv[2]); L0 = int(sys.argv[3]); nstart = int(sys.argv[4]); seed = int(sys.argv[5])
    g, a, th, tail = setup(K, 'z1770.txt'); rng = np.random.default_rng(seed)
    print('K',K,'tail',tail,'a1',a[0])
    for st in range(nstart):
        mode = st % 3
        if mode == 0: x = -(L0/2)*th + 0.3*rng.standard_normal(K)*(np.arange(K) < 20)   # centred x=0 perturbed
        elif mode == 1: x = rng.uniform(0, 2*np.pi, K)
        else: x = -(L0/2)*th + rng.uniform(-1, 1, K)*np.minimum(1, 0.05*np.arange(K))
        if s < 0 and mode == 0: x = x+np.pi
        x, m = slp(x, a, th, L0, s)
        print('start', st, mode, 'L0 margin', m-tail, flush=True)
