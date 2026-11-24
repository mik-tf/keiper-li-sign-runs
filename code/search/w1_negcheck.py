"""W1: ball-checked NEGATIVE run length for a job from w_lattice.py (target x*+pi):
counts j with F_K(n+j) + T_K < 0 from j=0. Usage: python w1_negcheck.py OUT_JSON  (run next to w_lattice.py)"""
import sys, json
from flint import ctx, arb
from w_lattice import zeros_theta
r = json.load(open(sys.argv[1]))[0]
K, n = r['K'], int(r['n'])
prec = r['P_bits'] + 200
g, th, a, _ = zeros_theta(K, prec)
twopi = 2*arb.pi()
lam1 = 1 + arb.const_euler()/2 - (4*arb.pi()).log()/2
TK = 2*lam1 - sum(a)
ph = [arb(n)*th[k] - twopi*((arb(n)*th[k]/twopi).floor()) for k in range(K)]
L = 0
while L < 3000:
    F = sum(a[k]*(ph[k] + L*th[k]).cos() for k in range(K))
    if not (F + TK < 0): break
    L += 1
print(json.dumps({'K': K, 'D': r['D'], 'neg_run_len': L}))
