import random, itertools
from fractions import Fraction as Fr
from math import factorial
from constants import a_const, b_const
random.seed(20260929)

# (A) deposition simulation: roots == cyclic local minima of first-arrival times
def deposition_roots(K, seq):
    H = [0]*K; roots = set()
    for j in seq:
        h = 1 + max(H[(j-1) % K], H[j], H[(j+1) % K]); H[j] = h
        if h == 1: roots.add(j)
    return roots
def first_arrival_rule(K, seq):
    first = {}
    for t, j in enumerate(seq): first.setdefault(j, t)
    return {j for j in range(K) if first[j] < first[(j-1) % K] and first[j] < first[(j+1) % K]} if K >= 3 else \
           {j for j in range(K) if all(first[j] <= first[x] for x in range(K))}
bad = 0; trials = 0
for K in range(3, 16):
    for _ in range(20000):
        seq = []; seen = set()
        while len(seen) < K:
            j = random.randrange(K); seq.append(j); seen.add(j)
        seq += [random.randrange(K) for _ in range(3*K)]   # later arrivals cannot create roots
        trials += 1
        if deposition_roots(K, seq) != first_arrival_rule(K, seq): bad += 1
print(f"(A) deposition vs first-arrival rule: {trials} random runs, mismatches={bad}")

# (B) good-block patterns and exhaustive conditional variance of H
def roots_segment(vals):  # vals indexed 0..2g, anchors at 0 and 2g (fixed roots)
    L = len(vals); r = [0]
    for k in range(1, L-1):
        if vals[k] < vals[k-1] and vals[k] < vals[k+1]: r.append(k)
    r.append(L-1); return r
def H_of(vals, g):
    r = roots_segment(vals); return sum(1 for x, y in zip(r, r[1:]) if y - x == g)
ok = True
for g in range(2, 51):
    q = 2*g - 1
    inc = [0.0] + [0.3 + 0.6*k/q for k in range(1, q+1)] + [0.0]
    pat = [0.0] + [0.5 + 0.4*k/g for k in range(1, g)] + [0.26] + [0.5 + 0.4*(q+1-k)/g for k in range(g+1, q+1)] + [0.0]
    ok &= H_of(inc, g) == 0 and H_of(pat, g) == 2 and roots_segment(pat) == [0, g, 2*g]
print("(B1) patterns give H=0 and H=2 (roots exactly {0,g,2g}) for g=2..50:", ok)
for g in range(2, 6):
    q = 2*g - 1; dist = {}
    for perm in itertools.permutations(range(1, q+1)):
        h = H_of([0] + list(perm) + [0], g); dist[h] = dist.get(h, 0) + 1
    N = factorial(q); E = Fr(sum(h*c for h, c in dist.items()), N); V = Fr(sum(h*h*c for h, c in dist.items()), N) - E*E
    print(f"(B2) g={g}: law of H = { {h: Fr(c, N) for h, c in sorted(dist.items())} }, Var(H)={V} >= 4/(q!)^2: {V >= Fr(4, N*N)}")

# (C) decomposition D = C + sum_b H_b with C unaffected by resampling good interiors
def D_cycle(U, g):
    K = len(U); r = [j for j in range(K) if U[j] < U[j-1] and U[j] < U[(j+1) % K]]
    return sum(1 for k in range(len(r)) if ((r[(k+1) % len(r)] - r[k]) % K or K) == g)
bad = 0; tests = 0
for g in (2, 3, 4, 5):
    L = 2*g + 3
    for _ in range(300):
        nb = random.randint(2, 5); K = nb*L + random.randint(0, L-1)
        U = [random.random() for _ in range(K)]
        good = []
        for b in range(nb):
            if random.random() < 0.6:   # force block b good
                s = b*L
                U[s] = 0.8 + 0.2*random.random(); U[s+2*g+2] = 0.8 + 0.2*random.random()
                U[s+1] = 0.25*random.random(); U[s+2*g+1] = 0.25*random.random()
                for k in range(s+2, s+2*g+1): U[k] = 0.25 + 0.75*random.random()
                good.append(s)
        base = None
        for _ in range(20):
            for s in good:
                for k in range(s+2, s+2*g+1): U[k] = 0.25 + 0.75*random.random()
            C = D_cycle(U, g) - sum(H_of(U[s+1:s+2*g+2], g) for s in good)
            base = C if base is None else base; tests += 1
            if C != base: bad += 1
print(f"(C) D - sum_b H_b invariant under resampling good interiors: {tests} tests, failures={bad}")

# (D) explicit lower bound (7) versus exact b_i
for i in range(1, 11):
    g = i + 1
    lb = Fr(1, 64) * Fr(3, 4)**(2*g-1) / ((2*g+3) * factorial(2*g-1)**2)
    print(f"(D) i={i}: b_i={float(b_const(i)):.4e}  bound (7)={float(lb):.4e}  ok={b_const(i) >= lb}")
