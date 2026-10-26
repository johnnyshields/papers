#!/usr/bin/env python3
"""Exact connected-profile census in areas eight through thirteen.

Translation classes are full profiles (row lengths; adjacent overlaps minus one).
We enumerate every positive composition of each area and every legal gap word,
then quotient only by 180-degree rotation.  Overlap invariants discard groups
that cannot contain a nonrotation equality.  Full Jacobi--Trudi determinants,
computed by signed column-subset expansion with collected generator indices,
decide equality within each remaining group.  Disconnected diagrams are not
included.  A counted class is one Schur-function fiber containing at least two
rotation orbits, not a pair of diagrams or a presentation.

The advertised allocation is tested rather than assumed in the enumeration.
The six residual representatives are independently located in the resulting
fibers; 'residual' here means neither in the manuscript's classification domain
nor a ribbon, not absence of a legal marked presentation.
"""

from collections import defaultdict
from functools import lru_cache
from itertools import product


@lru_cache(None)
def compositions(n):
    if not n:
        return ((),)
    return tuple((a,) + tail for a in range(1, n + 1)
                 for tail in compositions(n - a))


def rotate(profile):
    rows, gaps = profile
    return rows[::-1], gaps[::-1]


def canonical(profile):
    return min(profile, rotate(profile))


def board(profile):
    rows, gaps = profile
    n = len(rows)
    y = [0] * n
    for i in range(n - 2, -1, -1):
        y[i] = y[i + 1] + rows[i + 1] - gaps[i]
    x = [y[i] + rows[i] for i in range(n)]
    return tuple(tuple(a - b for b in y) for a in x)


def signature(mat):
    n = len(mat)
    # Every k-row intersection multiset, including its zero entries.
    overlaps = tuple(tuple(sorted(max(0, mat[j + k - 1][j] + k - 1)
                                  for j in range(n - k + 1)))
                     for k in range(1, n + 1))
    common_betas = sum(v == 0 for row in mat for v in row)
    return n, mat[0][-1], common_betas, overlaps


def determinant(mat):
    """Subset Laplace expansion, with h_0=1 and h_j=0 for j<0."""
    n = len(mat)
    states = {0: {(): 1}}
    for row in mat:
        following = {}
        for mask, poly in states.items():
            for j, index in enumerate(row):
                if index < 0 or mask & (1 << j):
                    continue
                newmask = mask | (1 << j)
                out = following.setdefault(newmask, defaultdict(int))
                sign = -1 if (mask >> (j + 1)).bit_count() % 2 else 1
                for monomial, coefficient in poly.items():
                    key = tuple(sorted(monomial + (index,))) if index else monomial
                    out[key] += sign * coefficient
        states = {mask: {m: c for m, c in poly.items() if c}
                  for mask, poly in following.items()}
    return tuple(sorted(states[(1 << n) - 1].items()))


def negative_shape(mat):
    return tuple(sum(v < 0 for v in row) for row in mat[::-1]
                 if any(v < 0 for v in row))


def category(profile):
    shape = negative_shape(board(profile))
    minimum = 1 + max((part + i for i, part in enumerate(shape, 1)), default=0)
    if (sum(shape) <= 6 or (sum(shape) <= 9 and minimum >= 7)
            or (sum(shape) == 10 and minimum >= 7)):
        return 'classified'
    if all(z == 0 for z in profile[1]):
        return 'ribbon'
    return 'residual'


def main():
    groups = defaultdict(list)
    profile_count = 0
    orbit_count = 0
    for area in range(8, 14):
        for rows in compositions(area):
            choices = [range(min(a, b)) for a, b in zip(rows, rows[1:])]
            for gaps in product(*choices):
                profile = rows, gaps
                profile_count += 1
                if canonical(profile) != profile:
                    continue
                orbit_count += 1
                mat = board(profile)
                groups[signature(mat)].append(profile)

    classes = []
    candidate_count = 0
    for candidates in groups.values():
        if len(candidates) < 2:
            continue
        fibers = defaultdict(list)
        for profile in candidates:
            candidate_count += 1
            fibers[determinant(board(profile))].append(profile)
        classes.extend(tuple(sorted(fiber)) for fiber in fibers.values()
                       if len(fiber) > 1)

    allocation = defaultdict(int)
    residual = []
    for fiber in classes:
        kinds = {category(profile) for profile in fiber}
        assert len(kinds) == 1, ('category not invariant on observed class', fiber, kinds)
        kind = kinds.pop()
        allocation[kind] += 1
        if kind == 'classified':
            diagrams = {p for profile in fiber for p in (profile, rotate(profile))}
            assert len(diagrams) == 4, ('classified class not a quartet', fiber)
        if kind == 'residual':
            residual.append(fiber)

    expected_representatives = (
        ((1, 1, 2, 1, 2, 2, 2), (0, 0, 0, 0, 1, 0)),
        ((1, 2, 2, 2, 2, 3), (0, 0, 0, 0, 1)),
        ((1, 2, 2, 2, 3, 2), (0, 0, 0, 1, 0)),
        ((1, 2, 2, 2, 3, 3), (0, 0, 0, 1, 1)),
        ((1, 2, 2, 3, 2, 3), (0, 0, 1, 0, 1)),
        ((1, 1, 2, 1, 2, 2, 3, 1), (0, 0, 0, 0, 1, 1, 0)),
    )
    located = []
    for representative in expected_representatives:
        hits = [i for i, fiber in enumerate(residual)
                if canonical(representative) in fiber]
        assert len(hits) == 1, ('residual representative not found uniquely', representative, hits)
        located.extend(hits)
    assert len(set(located)) == len(residual) == 6
    assert len(classes) == 18, ('class count', len(classes), dict(allocation))
    assert dict(allocation) == {'classified': 9, 'ribbon': 3, 'residual': 6}, dict(allocation)

    # Two separate signed-permutation identities provide a small control on DP.
    from itertools import permutations
    for profile in (((2, 3), (1,)), ((1, 2, 2, 3), (0, 0, 1)),
                    ((3, 4, 3, 2, 1), (1, 2, 1, 0))):
        mat = board(profile)
        n = len(mat)
        direct = defaultdict(int)
        for perm in permutations(range(n)):
            entries = [mat[i][perm[i]] for i in range(n)]
            if any(j < 0 for j in entries):
                continue
            sign = (-1) ** sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
            direct[tuple(sorted(j for j in entries if j))] += sign
        assert determinant(mat) == tuple(sorted((m, c) for m, c in direct.items() if c))

    print('profiles:', profile_count, 'rotation orbits:', orbit_count,
          'determinants compared:', candidate_count)
    print('nonrotation connected Schur classes:', len(classes), dict(allocation))
    print('six residual representatives: located in six distinct complete finite-area fibers')
    print('ALL PASS')


if __name__ == '__main__':
    main()
