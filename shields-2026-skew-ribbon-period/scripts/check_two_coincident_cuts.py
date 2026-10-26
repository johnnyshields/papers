r"""Paper section `app:coincident` (Positive coincident attachment phases).

Two-coincident class indicators (lem:mark-pair, eq:two-coincident-counts).

For coprime A > B >= 2 and L = m A = j B (so A B divides L, m = mu B, j = mu A, mu >= 1),
enumerate every cut set C on (0, L) that is A-periodic away from the multiples of A and every
cut set C' that is B-periodic, and every pair with ribQ(C, L) = ribQ(C', L) (compared as
polynomials in the independent h_i, by evaluation at random points modulo a prime).
Assert that in every such pair C is empty (all positions of the class absent) or every
position of (0, L) lies in C -- the conclusion of coprime_cuts_whole, now in the regime
k = 0 -- and report which of the two occurs.
"""
import itertools
import math
import random

P = (1 << 61) - 1
random.seed(1)


def ribq(cuts, L, h):
    pts = [0] + sorted(cuts)
    D = {0: 1}
    for c in pts[1:]:
        D[c] = (-sum(D[c2] * h[c - c2] for c2 in pts if c2 < c)) % P
    return sum(D[c] * h[L - c] for c in pts) % P


def sets(L, per, seam):
    pos = list(range(1, L))
    # classes of positions under i ~ i + per (restricted to the allowed range)
    parent = {i: i for i in pos}

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    for i in pos:
        if i + per < L and (not seam or i % per != 0):
            parent[find(i)] = find(i + per)
    cls = {}
    for i in pos:
        cls.setdefault(find(i), []).append(i)
    reps = list(cls.values())
    for bits in itertools.product([0, 1], repeat=len(reps)):
        yield frozenset(i for b, r in zip(bits, reps) if b for i in r)


total = 0
outcomes = {}
for A in range(3, 8):
    for B in range(2, A):
        if math.gcd(A, B) != 1:
            continue
        for mu in (1, 2):
            L = A * B * mu
            hs = [[0] + [random.randrange(P) for _ in range(L)] for _ in range(3)]
            Cs = list(sets(L, A, True))
            Cps = list(sets(L, B, False))
            if len(Cs) * len(Cps) > 400000:
                continue
            tab = {}
            for Cp in Cps:
                tab.setdefault(tuple(ribq(Cp, L, h) for h in hs), []).append(Cp)
            for C in Cs:
                key = tuple(ribq(C, L, h) for h in hs)
                if key in tab:
                    total += 1
                    allpos = len(C) == L - 1
                    assert not C or allpos, (A, B, L, sorted(C), tab[key])
                    outcomes[(A, B, mu, 'empty' if not C else 'full')] = 1
print(total, "equal pairs;", sorted(outcomes))
print("PASS")
