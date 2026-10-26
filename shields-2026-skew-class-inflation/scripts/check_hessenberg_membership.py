#!/usr/bin/env python3
"""Paper section `sec:preliminaries` (Profiles, cuts, and ribbon substitution);
result `lem:hessenberg-membership`.

Check the Hessenberg-membership lemma on every small connected profile.

For each connected profile the full Jacobi--Trudi determinant is expanded over
all permutations, and the coefficient of the largest generator h_N is read off
it.  That coefficient, with sign (-1)^(n-1), must equal the separately expanded
cofactor det(h_{x_{i+1}-y_j}).  The cofactor is a monomial exactly when the full
board vanishes below its first subdiagonal, exactly when r_i > g_{i-1} + g_i for
2 <= i <= n-1, and in that case it equals the product of the h_{g_i}.  Controls
show that the strict inequality, the index pattern and the sign are each
exercised by the sweep.
"""

from collections import defaultdict
from itertools import permutations, product

# Largest row length tried at each row count; every connected profile within
# these bounds is enumerated.
ROW_BOUND = {1: 7, 2: 7, 3: 7, 4: 6, 5: 5}


def profiles(n, bound):
    for rows in product(range(1, bound + 1), repeat=n):
        ranges = [range(min(rows[i], rows[i + 1])) for i in range(n - 1)]
        for gaps in product(*ranges):
            yield rows, gaps


def beta_lists(rows, gaps):
    """Full strict beta lists with y_n = 0, by the recursion of the paper."""
    n = len(rows)
    x, y = [0] * n, [0] * n
    x[-1], y[-1] = rows[-1], 0
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    assert all(x[i] > x[i + 1] and y[i] > y[i + 1] for i in range(n - 1))
    assert all(rows[i] == x[i] - y[i] for i in range(n))
    assert all(gaps[i] == x[i + 1] - y[i] for i in range(n - 1))
    return x, y


def sign(perm):
    s, seen = 1, [False] * len(perm)
    for i in range(len(perm)):
        if seen[i]:
            continue
        j, length = i, 0
        while not seen[j]:
            seen[j], j, length = True, perm[j], length + 1
        if length % 2 == 0:
            s = -s
    return s


def determinant(index):
    """Collected determinant of (h_{index(i,j)}); h_0 = 1, h_k = 0 for k < 0.

    A monomial is the sorted tuple of its positive indices.
    """
    m = len(index)
    poly = defaultdict(int)
    for perm in permutations(range(m)):
        labels = [index[i][perm[i]] for i in range(m)]
        if min(labels, default=0) < 0:
            continue
        poly[tuple(sorted(k for k in labels if k > 0))] += sign(perm)
    return {mon: c for mon, c in poly.items() if c}


def main():
    tested = monomial = nonmonomial = 0
    nonstrict_fires = shifted_fires = unsigned_fires = 0
    for n, bound in ROW_BOUND.items():
        for rows, gaps in profiles(n, bound):
            x, y = beta_lists(rows, gaps)
            tested += 1

            full = determinant([[x[i] - y[j] for j in range(n)] for i in range(n)])
            top = x[0] - y[-1]
            extracted = defaultdict(int)
            for mon, c in full.items():
                if top in mon:
                    rest = list(mon)
                    rest.remove(top)
                    assert top not in rest
                    extracted[tuple(rest)] += c
            extracted = {mon: c for mon, c in extracted.items() if c}

            cofactor = determinant(
                [[x[i + 1] - y[j] for j in range(n - 1)] for i in range(n - 1)])
            signed = {mon: (-1) ** (n - 1) * c for mon, c in extracted.items()}
            assert signed == cofactor, (rows, gaps)
            assert cofactor, (rows, gaps)
            if n % 2 == 0 and extracted != cofactor:
                unsigned_fires += 1

            is_monomial = len(cofactor) == 1
            board = all(x[i] - y[j] < 0
                        for i in range(n) for j in range(n) if i >= j + 2)
            inequality = all(rows[i] > gaps[i - 1] + gaps[i]
                             for i in range(1, n - 1))
            assert is_monomial == board == inequality, (rows, gaps)
            if is_monomial:
                monomial += 1
                expected = tuple(sorted(g for g in gaps if g > 0))
                assert cofactor == {expected: 1}, (rows, gaps)
            else:
                nonmonomial += 1

            nonstrict = all(rows[i] >= gaps[i - 1] + gaps[i]
                            for i in range(1, n - 1))
            if nonstrict != is_monomial:
                nonstrict_fires += 1
            shifted = all(rows[i] > gaps[i - 1] + gaps[i - 1]
                          for i in range(1, n - 1))
            if shifted != is_monomial:
                shifted_fires += 1

    print("connected profiles tested: %d" % tested)
    print("monomial cofactors: %d   non-monomial: %d" % (monomial, nonmonomial))
    print("control, non-strict inequality disagrees on: %d" % nonstrict_fires)
    print("control, wrong gap index disagrees on: %d" % shifted_fires)
    print("control, dropped sign disagrees on: %d" % unsigned_fires)
    assert monomial > 0 and nonmonomial > 0
    assert nonstrict_fires > 0 and shifted_fires > 0 and unsigned_fires > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
