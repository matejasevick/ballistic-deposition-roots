from fractions import Fraction as Fr
from constants import count_word, excursions, a_const, b_const
from math import factorial
def prob(words):
    return Fr(sum(count_word(w) for w in words), factorial(len(words[0]) + 1))
def P2x(i, j): return prob(['D' + e + f + 'U' for e in excursions(i+1) for f in excursions(j+1)])
def P3x(i, j): return prob(['D' + e + 'UD' + f + 'U' for e in excursions(i+1) for f in excursions(j+1)])
def c(i, j):  # long-run covariance sum_h Cov(Y_0^{(i+1)}, Y_h^{(j+1)})
    s = 2*P2x(i, j) + 2*P3x(i, j) - (i + j + 7)*a_const(i)*a_const(j)
    return s + (a_const(i) if i == j else 0)
assert all(c(i, i) == b_const(i) for i in range(1, 8))
assert all(P2x(i, j) == P2x(j, i) and P3x(i, j) == P3x(j, i) for i in range(1, 6) for j in range(1, 6))
for K in (9, 10, 11, 12, 13):
    S1 = {}; S2 = {}
    for line in open(f'cross_{K}.txt'):
        p = line.split()
        if p[0] == 'K': N = int(p[2])
        elif p[0] == 'S1': S1[int(p[1])] = Fr(int(p[2]), N)
        else: S2[(int(p[1]), int(p[2]))] = Fr(int(p[3]), N)
    res = []
    for i in range(1, 4):
        for j in range(i+1, 5):
            cov = S2[(i, j)] - S1[i]*S1[j]
            res.append(f"({i},{j}) K>={i+j+7}:{'Y' if K >= i+j+7 else 'n'} match={cov == K*c(i, j)}")
    print(K, ' '.join(res))
print('Sigma_12 =', float(c(1, 2)/(b_const(1)*b_const(2))**0.5), ' Sigma_13 =', float(c(1, 3)/(b_const(1)*b_const(3))**0.5), ' Sigma_23 =', float(c(2, 3)/(b_const(2)*b_const(3))**0.5))
print('c(1,2) =', c(1, 2), ' c(1,3) =', c(1, 3), ' c(2,3) =', c(2, 3))
