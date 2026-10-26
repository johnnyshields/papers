r"""Paper section `app:coincident` (Positive coincident attachment phases).

Two-coincident band geometry (lem:mark-pair, eq:two-coincident-counts, prop:two-coincident).

Combinatorial content of the clauses of TwoCoincidentBandGeometry that a script can reach.

(a) Counterpart periodic only OFF its seams is too weak.  For coprime A > B >= 2, L = m A = j B,
    a cut set C that is A-periodic away from the multiples of A against a cut set C' that is
    B-periodic away from the multiples of B, with ribQ(C, L) = ribQ(C', L): the pair
    a pair neither empty nor whole (e.g. A, B, mu = 3, 2, 2) is a counterexample to "empty or whole",
    asserted below.  So the counterpart clause needs B-periodicity AT the seams too, i.e. a
    line counterpart outer; it cannot be replaced by the seam-excluded form.
(b) Whole class at the seams: when C is whole, every seam t A is in C (so the reading of the
    outer steps at the seams applies for every mu).
(c) mu >= 2: both whole-or-empty conclusions occur for mu = 2, i.e. the seam-periodic
    form cannot by itself exclude mu >= 2; that exclusion is lower key invariance, which
    this script does not model (no diagram-level search is attempted).
"""
import itertools
import math
import random

P = (1 << 61) - 1
random.seed(2)


def ribq(cuts, L, h):
    pts = [0] + sorted(cuts)
    D = {0: 1}
    for c in pts[1:]:
        D[c] = (-sum(D[c2] * h[c - c2] for c2 in pts if c2 < c)) % P
    return sum(D[c] * h[L - c] for c in pts) % P


def sets(L, per, seam):
    pos = list(range(1, L))
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
seen = {}
bad = {}
for A in range(3, 6):
    for B in range(2, A):
        if math.gcd(A, B) != 1:
            continue
        for mu in (1, 2):
            L = A * B * mu
            hs = [[0] + [random.randrange(P) for _ in range(L)] for _ in range(3)]
            Cs = list(sets(L, A, True))
            Cps = list(sets(L, B, True))
            if len(Cs) * len(Cps) > 100000:
                continue
            tab = {}
            for Cp in Cps:
                tab.setdefault(tuple(ribq(Cp, L, h) for h in hs), []).append(Cp)
            for C in Cs:
                key = tuple(ribq(C, L, h) for h in hs)
                if key in tab:
                    total += 1
                    whole = len(C) == L - 1
                    if C and not whole:
                        bad[(A, B, mu)] = sorted(C)
                    seen[(A, B, mu, 'whole' if whole else 'empty')] = 1
print(total, "equal pairs;", sorted(seen))
assert bad, "expected a seam-excluded counterexample"
print("seam-excluded counterpart: counterexamples", bad)

# the full-periodic counterpart clause (the form used by coprime_cuts_whole_zero)
for A in range(3, 6):
    for B in range(2, A):
        if math.gcd(A, B) != 1:
            continue
        for mu in (1, 2):
            L = A * B * mu
            hs = [[0] + [random.randrange(P) for _ in range(L)] for _ in range(3)]
            Cs = list(sets(L, A, True))
            Cps = list(sets(L, B, False))
            if len(Cs) * len(Cps) > 100000:
                continue
            tab = {}
            for Cp in Cps:
                tab.setdefault(tuple(ribq(Cp, L, h) for h in hs), []).append(Cp)
            for C in Cs:
                if tuple(ribq(C, L, h) for h in hs) in tab:
                    assert not C or len(C) == L - 1, (A, B, mu, sorted(C))
                    if C:
                        assert all(t * A in C for t in range(1, L // A))
print("PASS")
