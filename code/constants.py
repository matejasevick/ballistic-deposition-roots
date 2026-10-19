"""Exact constants a_i, b_i for gaps of length g=i+1 between local minima of an iid sequence.
Method: count permutations with a prescribed up/down word (exact integer DP)."""
from fractions import Fraction as Fr
from math import factorial

def count_word(w):
    """# permutations of [len(w)+1] whose consecutive comparisons follow w ('U' = rise, 'D' = fall)."""
    f = [1]
    for c in w:
        j = len(f)
        pre = [0]
        for x in f: pre.append(pre[-1] + x)
        if c == 'U':   # new last element has rank k in 0..j, need previous rank < k
            f = [pre[k] for k in range(j + 1)]
        else:
            f = [pre[j] - pre[k] for k in range(j + 1)]
    return sum(f)

def prob_words(words):
    n = len(words[0]) + 1
    return Fr(sum(count_word(w) for w in words), factorial(n))

def excursions(g):
    return ['U' * a + 'D' * (g - a) for a in range(1, g)]

def a_const(i):
    g = i + 1
    return prob_words(['D' + e + 'U' for e in excursions(g)])

def P2(i):
    g = i + 1
    return prob_words(['D' + e + f + 'U' for e in excursions(g) for f in excursions(g)])

def P3(i):
    g = i + 1
    return prob_words(['D' + e + 'UD' + f + 'U' for e in excursions(g) for f in excursions(g)])

def b_const(i):
    a = a_const(i)
    return a - (2 * i + 7) * a * a + 2 * P2(i) + 2 * P3(i)

if __name__ == '__main__':
    known = {1: (Fr(2, 15), Fr(1772, 14175)), 2: (Fr(1, 9), Fr(32, 405)), 3: (Fr(2, 35), Fr(119732, 2837835)),
             4: (Fr(1, 45), Fr(12154, 637875)), 5: (Fr(4, 567), Fr(649555688, 97692469875)),
             6: (Fr(1, 525), Fr(5967328, 3192564375)), 7: (Fr(2, 4455), Fr(191501338988, 428772250281375))}
    for i in range(1, 13):
        a, b = a_const(i), b_const(i)
        tag = ''
        if i in known:
            tag = 'MATCH' if (a, b) == known[i] else f'MISMATCH known={known[i]}'
        print(i, a, b, float(b / a), tag)
    # sanity: sum_i a_i = 1/3 (density of local minima), sum (i+1) a_i = 1
    s = sum(a_const(i) for i in range(1, 30)); t = sum((i + 1) * a_const(i) for i in range(1, 30))
    print('sum a_i ~', float(s), ' sum (i+1) a_i ~', float(t))
