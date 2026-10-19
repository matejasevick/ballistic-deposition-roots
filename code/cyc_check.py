from fractions import Fraction as Fr
from math import factorial
from constants import a_const, b_const
import re
data = {}; K = None
for line in open('cyc_out.txt'):
    m = re.match(r'K=(\d+) orders=(\d+)', line)
    if m: K = int(m.group(1)); N = int(m.group(2)); assert N == factorial(K-1); continue
    m = re.match(r'i=(\d+) sum=(\d+) sumsq=(\d+)', line)
    if m:
        i, s1, s2 = map(int, m.groups()); E = Fr(s1, N); V = Fr(s2, N) - E*E
        data[(i, K)] = (E, V)
for (i, K), (E, V) in sorted(data.items()):
    m = i + 4
    if K < i + 3: continue
    a, b = a_const(i), b_const(i)
    print(f"i={i} K={K:2d} (2m-1={2*m-1:2d})  E==aK:{E==a*K}  Var==bK:{V==b*K}   Var/K={float(V/K):.6f} b={float(b):.6f}")
