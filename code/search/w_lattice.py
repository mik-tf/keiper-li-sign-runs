"""W pilot step B: lattice reduction (python-flint fmpz_mat.lll, no BKZ) for inhomogeneous
simultaneous approximation  n*theta_k = x_k (mod 2 pi), weighted by a_k = 2 w_k.
Usage: python w_lattice.py TARGET_DIR OUT_JSON K:FACTOR[,FACTOR..] [...]   e.g. 40:0.9,1.0,1.2
Digits D = ceil(FACTOR * Dh) with Dh = log10 of the Gaussian-heuristic N for budget m.
Target is read from TARGET_DIR/cert_run_pos_K{K}.json if present (K=100,150,...), others from target_K{K}.json.
Per run it records: lattice build time, LLL time, n (digits), exact weighted l1 error E = sum a_k dist(n th_k - x_k, 2 pi Z)
(ball arithmetic), the run length reached by the K-zero sum F_K(n+j) > T_K (j = 0,1,...), and total lattice entry bits."""
import sys, json, time, math
from fractions import Fraction
from flint import ctx, arb, acb, fmpz, fmpq, fmpz_mat

def zeros_theta(K, prec):
    ctx.prec = prec
    t0 = time.time(); g = [acb.zeta_zero(k).imag for k in range(1, K+1)]; tz = time.time() - t0
    th = [2*(1/(2*x)).atan() for x in g]
    a = [2/(arb(1)/4 + x*x) for x in g]
    return g, th, a, tz

def toint(v):  # nearest integer of arb
    return int((v + arb(1)/2).floor().unique_fmpz())

def run(K, f, tgt, zcache, Dfix=None, neg=False):
    x = [Fraction(*p) if isinstance(p, list) else Fraction(p) for p in tgt['x']]
    if neg:  # negative runs: target x* + pi (pi as a 400-bit rational, error far below m)
        ctx.prec = 600
        pq = Fraction(int((arb.pi()*arb(2)**400).floor().unique_fmpz()), 2**400)
        x = [v + pq for v in x]
    m = tgt['margin']
    # Gaussian-heuristic digits
    ctx.prec = 200
    gl, thl, al, _ = zeros_theta(K, 200)
    la = sum(math.log10(float(v)) for v in al)
    Dh = K*math.log10(2*math.pi) + math.lgamma(K+1)/math.log(10) + la - K*math.log10(2*m)
    D = Dfix if Dfix else math.ceil(f*Dh)
    P = int((D + math.log10(1/m) + 12)*3.3219) + 1     # scale bits
    prec = P + 200
    key = (K, prec)
    g, th, a, tz = zeros_theta(K, prec)
    N = fmpz(10)**D
    S = fmpz(2)**P
    twopi = 2*arb.pi()
    t0 = time.time()
    n_ = K + 2
    omega = max(1, int((arb(S)*arb(m)/arb(N)).floor().unique_fmpz()))
    M = max(1, int((arb(S)*arb(m)/4).floor().unique_fmpz()))
    rows = []
    r0 = [omega] + [toint(a[k]*th[k]*arb(S)) for k in range(K)] + [0]
    rows.append(r0)
    for k in range(K):
        r = [0]*(K+2); r[1+k] = toint(a[k]*twopi*arb(S)); rows.append(r)
    rows.append([0] + [toint(-a[k]*arb(fmpq(x[k].numerator, x[k].denominator))*arb(S)) for k in range(K)] + [M])
    B = fmpz_mat(rows)
    tb = time.time() - t0
    t0 = time.time(); R = B.lll(); tl = time.time() - t0
    best = None
    for i in range(R.nrows()):
        last = int(R[i, K+1])
        if abs(last) != int(M): continue
        n = int(R[i, 0]) // omega * (1 if last > 0 else -1)
        # error vector in true arithmetic
        E = arb(0)
        for k in range(K):
            ph = arb(n)*th[k] - arb(fmpq(x[k].numerator, x[k].denominator))
            q = (ph/twopi + arb(1)/2).floor()
            e = ph - q*twopi
            E += a[k]*abs(e)
        Ef = float(E.mid())
        if best is None or Ef < best[0]: best = (Ef, n)
    res = {'K': K, 'factor': f, 'Dh': Dh, 'D': D, 'P_bits': P, 'm': m, 'L_target': tgt['L'], 'time_build_s': tb, 'time_lll_s': tl,
           'time_zeros_s': tz, 'entry_bits': P + 10}
    if best:
        Ef, n = best
        res.update({'n': str(n), 'n_digits': len(str(abs(n))), 'E': Ef, 'E_over_m': Ef/m, 'log10_n': math.log10(abs(n)) if n else 0, 'n_sign': 1 if n > 0 else -1})
        # run length of F_K(n+j) - T_K > 0 from j=0 (even symmetry of c_n makes negative n usable)
        lam1 = 1 + arb.const_euler()/2 - (4*arb.pi()).log()/2
        TK = 2*lam1 - sum(a)
        ph = [arb(n)*th[k] - twopi*((arb(n)*th[k]/twopi).floor()) for k in range(K)]
        L = 0
        while L < 3000:
            F = sum(a[k]*(ph[k] + L*th[k]).cos() for k in range(K))
            if not (F - TK > 0): break
            L += 1
        res['run_len_certlike'] = L
    else:
        res['E'] = None
    return res

if __name__ == '__main__':
    tdir, out = sys.argv[1], sys.argv[2]
    results = []
    for spec in sys.argv[3:]:
        # W1 form: K:D=1000:pos|neg (D digits given directly); old form: K:f1,f2
        K, fs = spec.split(':', 1); K = int(K)
        Dfix = None; neg = False
        if fs.startswith('D='):
            dd, sg = fs[2:].split(':'); Dfix = int(dd); neg = (sg == 'neg'); fs = '1.0'
        import os
        if os.path.exists(f'{tdir}/cert_run_pos_K{K}.json'):
            c = json.load(open(f'{tdir}/cert_run_pos_K{K}.json'))
            tgt = {'x': c['x_num_den'], 'margin': c.get('m_lo_float', c['float_margin']), 'L': c['L']}
        else:
            tgt = json.load(open(f'{tdir}/target_K{K}.json'))
        for f in map(float, fs.split(',')):
            r = run(K, f, tgt, None, Dfix, neg); r['sign_target'] = 'neg' if neg else 'pos'; results.append(r)
            print(json.dumps(r), flush=True)
            json.dump(results, open(out, 'w'), indent=1)
