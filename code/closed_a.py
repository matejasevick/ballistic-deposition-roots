import sympy as sp
from constants import a_const, P2, P3
from fractions import Fraction as Fr
s, t, u, n = sp.symbols('s t u n', positive=True)
i = sp.symbols('i', integer=True, positive=True)

def I1_num(k):
    return sp.integrate(sp.integrate(s*t*(s+t)**k, (s, 0, 1)), (t, 0, 1))
# closed form of I1 via antiderivatives, symbolic in n
F = (1+s)**(n+2)/(n+2) - s*(1+s)**(n+1)/(n+1) - s**(n+2)/(n+2) + s**(n+2)/(n+1)
# int_0^1 s*(1+s)^p ds and s^2 (1+s)^p ds
def J1(p): return (2**(p+2)-1)/(p+2) - (2**(p+1)-1)/(p+1)
def J2(p): return (2**(p+3)-1)/(p+3) - 2*(2**(p+2)-1)/(p+2) + (2**(p+1)-1)/(p+1)
I1 = J1(n+2)/(n+2) - J2(n+1)/(n+1) - 1/((n+2)*(n+4)) + 1/((n+1)*(n+4))
I1s = sp.factor(sp.simplify(I1))
print('I1(n) =', I1s)
I2 = 2/((n+1)*(n+2)*(n+4))
a_expr = sp.factor(sp.simplify((I1 - I2)/2))
print('i! a_i =', a_expr)
for k in range(1, 15):
    val = sp.Rational(a_expr.subs(n, k)) / sp.factorial(k)
    assert val == sp.Rational(a_const(k).numerator, a_const(k).denominator), k
    assert sp.simplify(I1.subs(n, k) - I1_num(k)) == 0
print('closed form for a_i verified for i=1..14')
