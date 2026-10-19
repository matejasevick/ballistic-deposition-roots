import sympy as sp, pickle
from constants import a_const, P2, P3, b_const
from fractions import Fraction as Fr
n = sp.Symbol('n', positive=True, integer=True); T = sp.Symbol('T'); W = sp.Function('W')
a_cf, P2_cf, P3_cf = pickle.load(open('closed_b.pkl', 'rb'))
def ev(e, k):
    v = e.subs(W(n), sp.Integer(4)**k*sp.factorial(k)**2/sp.factorial(2*k+1)).subs(T, sp.Integer(2)**k).subs(n, k)
    v = sp.nsimplify(sp.expand(v), rational=True) if not v.is_Rational else v
    return sp.Rational(v)
bad = 0
for k in range(1, 26):
    for e, f in ((a_cf, a_const), (P2_cf, P2), (P3_cf, P3)):
        v = sp.simplify(e.subs(W(n), sp.Integer(4)**k*sp.factorial(k)**2/sp.factorial(2*k+1)).subs(T, sp.Integer(2)**k).subs(n, k))
        x = f(k)
        if not (v.is_Rational and v == sp.Rational(x.numerator, x.denominator)): bad += 1; print('bad', k, v, x)
print('mismatches:', bad)
