#!/usr/bin/env python3
"""Check negative masks, bordering coefficients, and parameter boundaries.

The unbounded split exclusion is proved by cross-block counts in the paper.
This script enumerates the five-negative masks through twelve rows and checks
that inventory independently of diagram polynomials.  Exact determinant checks
then target the first bordering step, endpoint directions, and unit boundaries.
"""

from collections import Counter
from itertools import product

from check_opening_coefficient_contacts import (
    coefficient, determinant, family_set, lists, neg, rotate, top,
)


def from_lists(x, y):
    return (tuple(a-b for a, b in zip(x, y)),
            tuple(x[i+1]-y[i] for i in range(len(x)-1)))


def matrix(profile):
    x, y = lists(*profile)
    return tuple(tuple(a-b for b in y) for a in x)


def negatives(profile):
    return {(i, j) for i, row in enumerate(matrix(profile))
            for j, v in enumerate(row) if v < 0}


def valid(profile):
    r, z = profile
    return all(v > 0 for v in r) and all(0 <= v < min(r[i], r[i+1])
                                         for i, v in enumerate(z))


def border(profile, u, v):
    x, y = lists(*profile)
    return from_lists((x[0]+u,) + x, y + (-v,))


def endpoint(profile, t, upper):
    r, z = profile
    rr = list(r)
    rr[0 if upper else -1] += t
    return tuple(rr), z


def gamma(profile):
    return tuple(2*r+1 for r in profile[0]), tuple(2*z+1 for z in profile[1])


def cofactor(profile):
    x, y = lists(*profile)
    return from_lists(x[1:], y[:-1])


def masks(n, total):
    def go(prefix, left):
        i = len(prefix)
        if i == n:
            if left == 0:
                yield prefix
            return
        low = prefix[-1] if prefix else 0
        for c in range(low, min(max(0, i-1), left)+1):
            yield from go(prefix+(c,), left-c)
    yield from go((), total)


def split_inventory(counts):
    for n in range(5, 13):
        actual = set()
        for rowcounts in masks(n, 5):
            sites = {(i, j) for i, c in enumerate(rowcounts) for j in range(c)}
            # Source indices are zero-based.  The child's subdiagonal at k
            # is the source site (k+2,k), and a negative there is a split.
            splits = [k+1 for k in range(n-2) if (k+2, k) in sites]
            cuts = [0] + splits + [n-1]
            sizes = tuple(cuts[i+1]-cuts[i] for i in range(len(cuts)-1))
            crossing = sum(sizes[i]*sizes[j] for i in range(len(sizes))
                           for j in range(i+1, len(sizes)))
            assert crossing <= 5
            if len(sizes) >= 3:
                assert crossing >= 2*n-5
            if len(sizes) > 1:
                actual.add((sizes, 5-crossing))
            counts['five-negative masks'] += 1
        if n == 6:
            assert actual == {((1, 4), 1), ((4, 1), 1)}, actual
        elif n == 7:
            assert actual == {((1, 5), 0), ((5, 1), 0)}, actual
        elif n >= 8:
            assert not actual, (n, actual)
    for n in range(6, 13):
        sites = {(i, j) for i in range(n) for j in range(n) if i-j >= n-3}
        assert len(sites) == 6
        child_sites = {(i-1, j) for i, j in sites}
        expected = {(i, j) for i in range(n-1) for j in range(n-1)
                    if i-j >= n-4}
        assert child_sites == expected
        assert all((k+2, k) not in sites for k in range(n-2))
        counts['connected staircase shifts'] += 1


def first_border_checks(counts):
    for b, g, q in ((1, 2, 1), (2, 3, 1), (2, 3, 2), (3, 5, 1), (3, 5, 3)):
        for second in (False, True):
            members = family_set(b, g, q, second)
            assert len(members) == 4
            polys = [determinant(*p) for p in members]
            assert all(p == polys[0] for p in polys)
            for raw in members:
                assert valid(raw) and len(negatives(raw)) == 5
                for t in range(1, 4):
                    assert negatives(endpoint(raw, t, True)) == negatives(raw)
                    assert negatives(endpoint(raw, t, False)) == negatives(raw)
                    assert determinant(*endpoint(raw, t, True)) != determinant(*endpoint(raw, t, False))
                    counts['endpoint comparisons'] += 1
                child = gamma(raw)
                assert negatives(child) == negatives(raw)
                assert all(v != 0 for row in matrix(child) for v in row)
                for u, v in product(range(1, 4), repeat=2):
                    parent = border(child, u, v)
                    assert valid(parent) and len(negatives(parent)) == 5
                    assert cofactor(parent) == child
                    assert gamma(border(raw, u, v)) == border(child, 2*u, 2*v)
                    N = lists(*parent)[0][0]
                    S = lists(*child)[0][0]
                    poly = determinant(*parent)
                    assert coefficient(poly, N) == neg(determinant(*child))
                    rem = {m: c for m, c in poly.items() if N not in m}
                    M = N-min(u, v)
                    assert top(rem) == M
                    if u != v:
                        assert coefficient(rem, M) == determinant(*endpoint(child, min(u, v), u < v))
                        assert S+min(u, v) < M
                    else:
                        square = determinant(*cofactor(child))
                        assert square and coefficient(rem, M, 2) == square
                    counts['border marker comparisons'] += 1
            # The two orbits remain distinct after every tested border.
            representatives = sorted({min(p, rotate(p)) for p in members})
            assert len(representatives) == 2
            for u, v in product(range(1, 4), repeat=2):
                left = determinant(*border(representatives[0], u, v))
                for other in (representatives[1], rotate(representatives[1])):
                    for uu, vv in {(u, v), (v, u)}:
                        assert left != determinant(*border(other, uu, vv))
                        counts['cross-orbit border separations'] += 1


def parameter_boundaries(counts):
    # At b=g the displayed diagrams are still valid (q<g), but have only
    # three negatives; the shifted-column identity no longer applies.
    b, g, q = 2, 2, 1
    x = tuple(b+k*g for k in range(4, -1, -1))
    first = from_lists(x, (3*g, g+q, g, q, 0))
    second = from_lists(x, (2*g+q, 2*g, g, q, 0))
    assert valid(first) and valid(second)
    assert len(negatives(first)) == len(negatives(second)) == 3
    assert determinant(*first) != determinant(*second)
    counts['excluded b=g boundary'] += 1
    # At q=0 the columns repeat, not an admissible full diagram.
    y = (6, 2, 2, 0, 0)
    assert len(set(y)) < len(y)
    # At q>b a last overlap is negative, so connectedness is lost.
    x = (9, 7, 5, 3, 1)
    assert not valid(from_lists(x, (6, 4, 2, 2, 0)))
    counts['invalid q boundaries'] += 2


def rejecting_coefficient_control():
    # Replace the extractor by one that drops its whole coefficient.  The
    # production contact comparison must detect this on a valid mixed pair.
    import check_opening_coefficient_contacts as contact
    source = ('M', 3, 6, 3, 1, 0, 3, 1, 0, 0)
    target = ('E', 3, 6, 3, 1, 0, 1, 3, 0, 0)
    contact.check_pair(source, target, Counter())
    saved = contact.coefficient
    contact.coefficient = lambda *args, **kwargs: {}
    try:
        try:
            contact.check_pair(source, target, Counter())
        except AssertionError as exc:
            assert exc.args[0][0] == 'contact coefficient', exc
            print('CONTROL FIRED: production comparison rejects a dropped collected coefficient')
        else:
            raise AssertionError('coefficient corruption was not rejected')
    finally:
        contact.coefficient = saved


def main():
    counts = Counter()
    split_inventory(counts)
    first_border_checks(counts)
    parameter_boundaries(counts)
    rejecting_coefficient_control()
    for key, value in sorted(counts.items()):
        print(key + ':', value)
    print('ALL PASS')


if __name__ == '__main__':
    main()
