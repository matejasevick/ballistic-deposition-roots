"""Closed forms for P2(i), P3(i) and hence b_i, derived symbolically in n=i.
A_n(t) = [(1+t)^{n+2}-(1-t)^{n+2}]/(n+2) - t[(1+t)^{n+1}+(1-t)^{n+1}]/(n+1)
a_n  = (1/(2 n!)) int_0^1 t A_n(t) dt
P2_n = (1/(4 n!^2)) int_0^1 A_n(t)^2 dt
P3_n = (1/(4 n!^2)) int_0^1 B_n(x)^2 dx,  B_n(x) = int_x^1 A_n(t) dt
"""
import sympy as sp
from math import comb, factorial
from constants import a_const, P2, P3, b_const
n = sp.Symbol('n', positive=True, integer=True)
W = sp.Function('W')   # W(n) = int_0^1 (1-t^2)^n dt = 4^n n!^2/(2n+1)!
two = sp.Symbol('T')   # T = 2^n
# a term: (coef, j, (pa,pb), (qa,qb)) = coef * t^j (1+t)^{pa n+pb} (1-t)^{qa n+qb}
def mul(x, y):
    out = []
    for c1, j1, P1, Q1 in x:
        for c2, j2, P2_, Q2 in y:
            out.append((c1*c2, j1+j2, (P1[0]+P2_[0], P1[1]+P2_[1]), (Q1[0]+Q2[0], Q1[1]+Q2[1])))
    return out
def pow2(N):  # 2^(a n + b) with a in {0,1,2}
    a, b = N
    return two**a * sp.Integer(2)**b
def Wshift(c):  # W(n+c) in terms of W(n)
    r = sp.Integer(1)
    for s in range(1, c+1): r *= (2*n+2*s)/(2*n+2*s+1)
    return W(n)*r
def integ(term):
    c, j, P, Q = term
    if P == (0, 0) and Q == (0, 0):
        return c*sp.Rational(1, j+1)
    if Q == (0, 0):   # int t^j (1+t)^N
        N = P[0]*n + P[1]
        tot = 0
        for k in range(j+1):
            M = N + k
            tot += comb(j, k)*(-1)**(j-k)*(2*pow2((P[0], P[1]+k)) - 1)/(M+1)
        return c*tot
    if P == (0, 0):   # Beta
        N = Q[0]*n + Q[1]
        den = sp.Integer(1)
        for r in range(1, j+2): den *= (N+r)
        return c*factorial(j)/den
    assert P[0] == Q[0] == 1, term
    Mb = min(P[1], Q[1]); e = abs(P[1]-Q[1]); sign = 1 if P[1] >= Q[1] else -1
    M = n + Mb
    tot = 0
    for k in range(e+1):  # (1 + sign t)^e
        r = j + k; ck = comb(e, k)*sign**k
        if r % 2 == 1:
            rho = (r-1)//2; den = sp.Integer(2)
            for s in range(1, rho+2): den *= (M+s)
            tot += ck*factorial(rho)/den
        else:
            rho = r//2; fac = sp.Integer(1)
            for s in range(1, rho+1): fac *= sp.Integer(2*s-1)/(2*M+2*s+1)
            tot += ck*Wshift(Mb)*fac
    return c*tot
A = [(1/(n+2), 0, (1, 2), (0, 0)), (-1/(n+2), 0, (0, 0), (1, 2)),
     (-1/(n+1), 1, (1, 1), (0, 0)), (-1/(n+1), 1, (0, 0), (1, 1))]
# B(x) = int_x^1 A = G(1) - G(x), G antiderivative
G = [(1/((n+2)*(n+3)), 0, (1, 3), (0, 0)), (1/((n+2)*(n+3)), 0, (0, 0), (1, 3)),
     (-1/((n+1)*(n+3)), 0, (1, 3), (0, 0)), (1/((n+1)*(n+2)), 0, (1, 2), (0, 0)),
     (1/((n+1)*(n+2)), 0, (0, 0), (1, 2)), (-1/((n+1)*(n+3)), 0, (0, 0), (1, 3))]
def evalG1():  # G at x=1: (1-1)^... = 0 terms vanish (n>=1)
    tot = 0
    for c, j, P, Q in G:
        if Q == (0, 0): tot += c*pow2(P)
    return tot
B = [(evalG1(), 0, (0, 0), (0, 0))] + [(-c, j, P, Q) for c, j, P, Q in G]
def total(terms): return sp.simplify(sum(integ(t) for t in terms))
tA = total(mul([(sp.Integer(1), 1, (0, 0), (0, 0))], A))
a_cf = sp.simplify(tA/(2*sp.factorial(n)))
P2_cf = total(mul(A, A))/(4*sp.factorial(n)**2)
P3_cf = total(mul(B, B))/(4*sp.factorial(n)**2)
def num(expr, k):
    v = expr.subs(two, 2**k).subs(W(n), sp.Integer(4)**n*sp.factorial(n)**2/sp.factorial(2*n+1)).subs(n, k)
    return sp.nsimplify(sp.simplify(v))
ok = True
for k in range(1, 16):
    for name, e, f in (('a', a_cf, a_const), ('P2', P2_cf, P2), ('P3', P3_cf, P3)):
        v = num(e, k); ex = f(k)
        if v != sp.Rational(ex.numerator, ex.denominator): ok = False; print('FAIL', name, k, v, ex)
print('closed forms agree with exact DP for i=1..15:', ok)
def pretty(e):
    e = sp.expand(e*4*sp.factorial(n)**2)
    return sp.collect(sp.simplify(e), [two**2, two, W(n)], sp.factor)
print('4 n!^2 P2 =', pretty(P2_cf))
print('4 n!^2 P3 =', pretty(P3_cf))
import pickle; pickle.dump((a_cf, P2_cf, P3_cf), open('closed_b.pkl', 'wb'))
