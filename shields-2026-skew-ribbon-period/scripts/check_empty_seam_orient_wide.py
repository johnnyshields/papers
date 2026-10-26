r"""Paper section `app:empty` (Empty overlaps and zero span remainder).

Wide search for the nonline/nonline case of the seam orientation (`lem:empty-seams`).

When neither A_0 nor B_0 is a line, the row multiset of D o A_0 depends only on A_0 and the row
count k_D of D, and its column multiset only on A_0^t and the row count of D^t, which is
mu B - k_D + 1.  This first checks that column formula against brute force, then searches
A_0, k_D, B_0, k_C for equal row and column multisets.
"""
import itertools
import random
from collections import Counter
from math import gcd
import sys
sys.path.insert(0, '.')
from check_empty_seam_orient import compositions, comp, conj, closed_rows

random.seed(5)
for _ in range(3000):
    D = tuple(random.randint(1, 4) for _ in range(random.randint(1, 5)))
    beta = tuple(random.randint(1, 4) for _ in range(random.randint(1, 5)))
    cols = Counter(conj(comp(D, beta)))
    assert cols == closed_rows(conj(D), conj(beta)), (D, beta)
print('column multiset = closed rows of D^t o beta^t: 3000 random cases pass')


def sig(beta, k, S):
    D = (1,) * (k - 1) + (S - k + 1,)
    Dt = conj(D)
    return (tuple(sorted(closed_rows(D, beta).items())),
            tuple(sorted(closed_rows(Dt, conj(beta)).items())))


bad, boxes = [], 0
for B in range(3, 9):
    for A in range(B + 1, 14):
        if gcd(A, B) != 1:
            continue
        for mu in (1, 2, 3):
            boxes += 1
            S, T = mu * B, mu * A
            left = {}
            for A0 in compositions(A):
                if len(A0) == 1 or len(conj(A0)) == 1:
                    continue
                for k in range(1, S + 1):
                    left.setdefault(sig(A0, k, S), []).append((A0, k))
            for B0 in compositions(B):
                if len(B0) == 1 or len(conj(B0)) == 1:
                    continue
                for k in range(1, T + 1):
                    for hit in left.get(sig(B0, k, T), []):
                        bad.append((A, B, mu, hit, (B0, k)))
print(f'nonline/nonline: {boxes} boxes, {len(bad)} coincidences')
for b in bad[:10]:
    print('  ', b)
assert not bad
