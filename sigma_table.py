from fractions import Fraction as Fr
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cross_check import c
    from task34_numbers import a_cf, b_cf, P2_cf, P3_cf
from math import sqrt
print('c_ij exact:')
for i in range(1, 5): print(i, [str(c(i, j)) for j in range(1, 5)])
print('Sigma_ij:')
for i in range(1, 5): print(i, ['%.4f' % (float(c(i, j))/sqrt(float(c(i, i))*float(c(j, j)))) for j in range(1, 5)])
for i in (10, 20, 40, 80, 160):
    a = a_cf(i); print(i, 'P2/(i a^2)=%.4f' % float(P2_cf(i)/(i*a*a)), ' P3/a^2=%.4f' % float(P3_cf(i)/(a*a)), ' (b-a)/(i a^2)=%.4f' % float((b_cf(i)-a)/(i*a*a)))
