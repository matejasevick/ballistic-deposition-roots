from fractions import Fraction as Fr
from math import factorial, sqrt, pi
from constants import a_const, P2, P3, b_const
import sympy as sp
# exact closed forms as typeset in the report
def a_cf(i): return Fr(i * 2**(i+1), (i+1)*(i+2)*(i+4)*factorial(i))
def P2_cf(i):
    return Fr(2*4**i*(2*i**3+5*i**2+4*i+2), factorial(i)**2*(i+1)**2*(i+2)**2*(2*i+3)*(2*i+5)) \
         - Fr(4**i, factorial(2*i)*(i+1)*(2*i+3)*(2*i+5))
def P3_cf(i):
    return Fr(4*4**i*(2*i-1)*(2*i**2+7*i+4), factorial(i)**2*(i+1)**2*(i+2)**2*(i+4)*(2*i+5)*(2*i+7)) \
         + Fr(2*4**i, factorial(2*i+1)*(i+1)*(i+2)*(2*i+5)*(2*i+7))
def b_cf(i): return a_cf(i) - (2*i+7)*a_cf(i)**2 + 2*P2_cf(i) + 2*P3_cf(i)
assert all(a_cf(i) == a_const(i) and P2_cf(i) == P2(i) and P3_cf(i) == P3(i) for i in range(1, 31))
print('typeset closed forms == exact DP for i=1..30')
ok1 = all(b_cf(i) >= Fr(2, 3)*a_cf(i) for i in range(1, 201))
ok2 = all((2*i+7)*a_cf(i) <= Fr(11, 9) for i in range(1, 201))
ok3 = all((6*i+19)*a_cf(i) <= Fr(31, 9) for i in range(1, 201))
print('b_i >= (2/3)a_i:', ok1, ' (2i+7)a_i <= 11/9:', ok2, ' (6i+19)a_i <= 31/9:', ok3)
print('max (2i+7)a_i =', max(float((2*i+7)*a_cf(i)) for i in range(1, 50)), ' max (6i+19)a_i =', max(float((6*i+19)*a_cf(i)) for i in range(1, 50)))
print('min b_i/a_i =', min(float(b_cf(i)/a_cf(i)) for i in range(1, 100)))
print(' i   a_i          b_i/a_i     eps_i       eps_i/((5i/2+9)a_i)   K with a_i K = 1')
for i in list(range(1, 16)) + [20, 30]:
    a = a_cf(i); e = (2*i+7)*a + 2*(P2_cf(i)+P3_cf(i))/a
    print(f"{i:2d}  {float(a):.4e}  {float(b_cf(i)/a):.6f}  {float(e):.4e}  {float(e/((Fr(5,2)*i+9)*a)):.4f}   {float(1/a):.3e}")
# Wasserstein constant
G = 5
C = 2*G**2*(1.5)**1.5 + sqrt(94/pi)*G*1.5
print('C_W =', C)
