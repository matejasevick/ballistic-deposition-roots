import sympy as sp
from fractions import Fraction as Fr
from cross_check import P2x, P3x
t, x = sp.symbols('t x')
def A(i): return ((1+t)**(i+2) - (1-t)**(i+2))/(i+2) - t*((1+t)**(i+1) + (1-t)**(i+1))/(i+1)
def B(i): return sp.integrate(A(i), (t, x, 1))
ok = True
for i in range(1, 6):
    for j in range(i, 6):
        p2 = sp.integrate(sp.expand(A(i)*A(j)), (t, 0, 1))/(4*sp.factorial(i)*sp.factorial(j))
        p3 = sp.integrate(sp.expand(B(i)*B(j)), (x, 0, 1))/(4*sp.factorial(i)*sp.factorial(j))
        e2, e3 = P2x(i, j), P3x(i, j)
        ok &= (p2 == sp.Rational(e2.numerator, e2.denominator)) and (p3 == sp.Rational(e3.numerator, e3.denominator))
print('integral representations of P2(i,j), P3(i,j) verified for 1<=i<=j<=5:', ok)
# generating function of a_i
z = sp.symbols('z')
s_, u_ = sp.symbols('s u', positive=True)
Gz = sp.integrate(sp.integrate(s_*u_*sp.exp(z*u_)*sp.sinh(z*s_), (s_, 0, u_)), (u_, 0, 1))*2
Gz = sp.simplify(Gz)
ser = sp.series(Gz, z, 0, 8).removeO()
from task34_numbers import a_cf
print('GF series coefficients match a_i:', all(sp.nsimplify(ser.coeff(z, k)) == sp.Rational(a_cf(k).numerator, a_cf(k).denominator) for k in range(1, 8)))
print('Sum a_i z^i =', sp.simplify(sp.expand(Gz.rewrite(sp.exp))))
