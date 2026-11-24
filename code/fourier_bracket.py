"""Error-budgeted computation of delta_K = P(F(X)F(X+theta)<0) in the LI_theta model.

F0=F(X)=sum a_k cos x_k, F1=F(X+theta)=sum a_k cos(x_k+theta_k), a_k=2/(1/4+g_k^2).
(F0, D=F1-F0) has compact support |F0|<=Sx, |D|<=Sd, joint characteristic function
phi(s,t)=E exp(i(s F0 + t D)) = prod_k J0(a_k |s + t(e^{i th_k}-1)|)   (real, even).
delta = 2 P(T1), T1={(x,d): -Sd<d<0, 0<x<-d}.  Parseval + Poisson summation on the lattice
(h_s Z) x (h_t Z) gives P(T1)=(1/(2pi)^2) h_s h_t sum phi * Re That(s,t) EXACTLY (no aliasing)
when 2pi/h_s > Sx+Sd and 2pi/h_t > 2 Sd; the only errors are the tail outside a box and rounding.
"""
import numpy as np, json, sys, time
from scipy.special import j0

def load(K, path):
    g = np.loadtxt(path)[:K]
    a = 2/(0.25+g**2); th = 2*np.arctan(1/(2*g))
    return g, a, th

def gl_nodes(n):
    x, w = np.polynomial.legendre.leggauss(n)
    return (x+1)/2, w/2

def _E(z):
    """E(z)=(e^{iz}-1)/(iz), E(0)=1."""
    return np.exp(1j*z/2)*np.sinc(z/(2*np.pi))

def That_over_L2(sig, tau, y=None, wq=None):
    """g(sig,tau)=int_{0<x<y<1} e^{i sig x - i tau y} = [E(sig-tau)-E(-tau)]/(i sig); sig=0: int y e^{-i tau y}."""
    sig = np.asarray(sig, float); tau = np.asarray(tau, float)
    out = np.empty(sig.shape, dtype=complex)
    z = sig == 0
    sg = np.where(z, 1.0, sig)
    out[...] = (_E(sg-tau)-_E(-tau))/(1j*sg)
    if z.any():
        tz = tau[z]
        # int_0^1 y e^{-i tz y} dy ; Taylor for small |tz|, closed form otherwise
        small = np.abs(tz) < 0.05
        val = np.empty(tz.shape, dtype=complex)
        ts = tz[small]; acc = np.zeros(ts.shape, dtype=complex); term = np.ones(ts.shape, dtype=complex)
        from math import factorial
        for n in range(0, 14):
            acc += (-1j*ts)**n/factorial(n)/(n+2)
        val[small] = acc
        tb = tz[~small]
        val[~small] = (np.exp(-1j*tb)*(1+1j*tb)-1)/tb**2
        out[z] = val
    return out

def phi_grid(S, T, a, c, sn):
    # S: (ns,), T: (nt,) -> phi (ns,nt) ; |zeta_k|^2=(s-t(1-c))^2+t^2 sin^2
    out = np.ones((S.size, T.size))
    for jt in range(T.size):
        t = T[jt]
        z = np.sqrt((S[:, None]-t*(1-c)[None, :])**2 + (t*sn)[None, :]**2)
        out[:, jt] = np.prod(j0(a[None, :]*z), axis=1)
    return out

def tail_bound(a, th, Smax, Tmax, hs, ht, area, nsamp=200001):
    """Rigorous-in-form bound on (1/(2pi)^2) h_s h_t sum_{outside box, full plane} |phi||That|,
    using |J0(x)|<=min(1,sqrt(2/(pi x))) (Watson 13.74, checked numerically), |That|<=area,
    |zeta_k|>=L_k=max(|t| sin th, |s|-|t|(1-cos th)), L_k homogeneous of degree 1."""
    c = np.cos(th); sn = np.sin(th)
    # boundary of box: parametrise both edges
    u = np.linspace(0, 1, nsamp)
    pts = [(Smax*np.ones_like(u), Tmax*(2*u-1)), (Smax*(2*u-1), Tmax*np.ones_like(u))]
    Umax = 0.0; mmin = 10**9
    for s, t in pts:
        L = np.maximum(np.abs(t)[:, None]*sn[None, :], np.abs(s)[:, None]-np.abs(t)[:, None]*(1-c)[None, :])
        L = np.maximum(L, 1e-300)
        r = np.sqrt(2/(np.pi*a[None, :]*L))      # envelope factor
        f = np.minimum(1, r)
        U = np.exp(np.sum(np.log(f), axis=1))
        Umax = max(Umax, U.max()); mmin = min(mmin, int((r < 1).sum(axis=1).min()))
    p = mmin/2
    if p <= 2: return np.inf, Umax, mmin
    # sum over lattice points with box-norm lam>=1 of U <= Umax * sum lam^-p ; box-norm sup-norm shells
    npts = (Smax*Tmax)/(hs*ht)                 # lattice points per unit box-area scaling
    # lattice sum <= 2 * integral_{||y||_inf>1} 8 r^{1-p} dr * npts/4 ... (area of box is 4 Smax Tmax)
    shells = 2*(4*npts)*8/(p-2)/4*1.0          # factor 2 slack; integral over R^2 in box-units
    tot = Umax*shells*(hs*ht)/(2*np.pi)**2*area*(1/ (hs*ht)) * (hs*ht)
    # ^ simplify: (1/(2pi)^2) h_s h_t * [Umax * (#lattice-pt weight)] * area
    tot = (hs*ht)/(2*np.pi)**2 * area * Umax * 2*(Smax*Tmax/(hs*ht))*8/(p-2)
    return tot, Umax, mmin

def run(K, zpath, fs=0.5, ft=0.5, Smax=None, Tmax=None, ngl=3000, verbose=True):
    g, a, th = load(K, zpath)
    c = np.cos(th); sn = np.sin(th)
    Sx = a.sum(); Sd = (2*a*np.sin(th/2)).sum()
    hs = fs*2*np.pi/(Sx+Sd); ht = ft*2*np.pi/(2*Sd)
    area = Sd**2/2
    # choose box so that tail bound < 1e-13 (absolute on P(T1)~0.011)
    Sm = Smax or 3000.0; Tm = Tmax or 1e5
    for _ in range(12):
        tb, Umax, mmin = tail_bound(a, th, Sm, Tm, hs, ht, area)
        if tb < 1e-12: break
        Sm *= 1.5; Tm *= 1.5
    ns = int(np.ceil(Sm/hs)); nt = int(np.ceil(Tm/ht))
    S = hs*np.arange(-ns, ns+1); T = ht*np.arange(0, nt+1)
    t0 = time.time()
    ph = phi_grid(S, T, a, c, sn)
    yq, wq = gl_nodes(ngl)
    SS, TT = np.meshgrid(S, T, indexing='ij')
    L = Sd
    gh = That_over_L2(SS*L, TT*L, yq, wq)
    That = (L**2)*gh
    wt = np.where(T == 0, 1.0, 2.0)[None, :]
    terms = ph*That.real*wt
    P = hs*ht/(2*np.pi)**2 * np.sum(np.sort(terms.ravel()))
    absum = hs*ht/(2*np.pi)**2 * np.sum(np.abs(ph*That.real)*wt)
    # last-shell magnitude (empirical truncation check)
    inner = (np.abs(S)[:, None] <= 0.5*Sm) & (T[None, :] <= 0.5*Tm)
    P_half = hs*ht/(2*np.pi)**2 * np.sum(terms*inner)
    fp = (K+4)*3e-16*absum + 1e-16*terms.size*np.abs(P)   # a-priori rounding allowance
    res = dict(K=K, delta=2*P, P_T1=P, Sx=Sx, Sd=Sd, hs=hs, ht=ht, Smax=Sm, Tmax=Tm, npts=int(ph.size),
               tail_bound_P=tb, Umax_boundary=Umax, m_min=mmin, fp_allowance_P=fp,
               sum_abs_terms_P=absum, P_half_box_diff=P-P_half,
               ratio=2*P/(th[0]/np.pi), time_s=time.time()-t0)
    res['ratio_lo'] = 2*(P-tb-fp)/(th[0]/np.pi); res['ratio_hi'] = 2*(P+tb+fp)/(th[0]/np.pi)
    if verbose: print(json.dumps(res), flush=True)
    return res

if __name__ == '__main__':
    zp = sys.argv[1]; Ks = [int(x) for x in sys.argv[2].split(',')]
    fs = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5
    ft = float(sys.argv[4]) if len(sys.argv) > 4 else 0.5
    for K in Ks: run(K, zp, fs, ft)
