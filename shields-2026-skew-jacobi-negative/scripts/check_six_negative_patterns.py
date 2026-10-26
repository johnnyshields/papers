#!/usr/bin/env python3
"""Check the six-negative pattern denominator from strict beta interleavings.

The enumeration does not use a minimum-row formula as an admission predicate.
Every strict endpoint order is represented by consecutive integers.  Negative
positions depend only on that order; common-beta orders embed by odd/even
homogenization.  No finite enumeration is used as a rigidity proof.
"""
from collections import Counter
from itertools import combinations


def partitions(n, ceiling=None):
    if n == 0:
        yield ()
        return
    for first in range(min(n, ceiling or n), 0, -1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


def conjugate(rho):
    return tuple(sum(x >= j for x in rho) for j in range(1, rho[0] + 1))


def connected(A, B):
    return (len(A) == len(B) and all(a > b for a, b in zip(A, B))
            and all(A[i + 1] >= B[i] for i in range(len(A) - 1)))


def negative_partition(A, B):
    return tuple(c for c in reversed([sum(a < b for b in B) for a in A]) if c)


def overlap_readings(A, B):
    n = len(A)
    parts = [tuple(sorted((max(0, A[j + k - 1] - B[j] + k - 1)
                           for j in range(n - k + 1)), reverse=True))
             for k in range(1, n + 1)]
    negative_count = sum(sum(t <= k - 2 for t in parts[k - 1])
                         for k in range(2, n + 1))
    bad = [k for k in range(2, n + 1) if min(parts[k - 1]) <= k - 2]
    return negative_count, (n + 3 - min(bad) if bad else 1)


def strict_words(n):
    for aset in combinations(range(1, 2 * n - 1), n - 1):
        A = tuple(sorted(aset + (2 * n - 1,), reverse=True))
        B = tuple(sorted(set(range(2 * n)) - set(A), reverse=True))
        if connected(A, B):
            yield A, B


def components(A, B):
    cuts = [0] + [i + 1 for i in range(len(A) - 1) if A[i + 1] < B[i]] + [len(A)]
    return [(A[i:j], B[i:j]) for i, j in zip(cuts, cuts[1:])]


def border(A, B, u=2, v=3):
    return (A[0] + u,) + A, B + (B[-1] - v,)


def expect_failure(test, description):
    try:
        test()
    except AssertionError:
        print('CONTROL REJECTED:', description)
        return
    raise AssertionError('Control failed to reject: ' + description)


def main():
    first, witnesses = {}, {}
    checked = Counter()
    for n in range(1, 9):
        for A, B in strict_words(n):
            rho = negative_partition(A, B)
            if sum(rho) != 6:
                continue
            checked[n] += 1
            first.setdefault(rho, n)
            witnesses.setdefault(rho, (A, B))
            assert overlap_readings(A, B) == (6, first[rho])
    all_parts = set(partitions(6))
    assert set(first) == all_parts and len(all_parts) == 11
    orbits = sorted({min(rho, conjugate(rho)) for rho in all_parts}, reverse=True)
    assert len(orbits) == 6
    for rho in all_parts:
        assert first[rho] == 1 + max(x + i for i, x in enumerate(rho, 1))
        assert first[rho] == first[conjugate(rho)]
    expected_open = {(4, 2), (2, 2, 1, 1), (4, 1, 1), (3, 1, 1, 1),
                     (3, 3), (2, 2, 2)}
    open_parts = {rho for rho in all_parts if first[rho] == 6}
    assert open_parts == expected_open
    signatures = Counter()
    for rho in sorted(open_parts):
        A, B = witnesses[rho]
        assert len(A) == 6
        child = components(A[1:], B[:-1])
        sizes = tuple(len(C) for C, _ in child)
        internal = tuple(sum(negative_partition(C, D)) for C, D in child)
        cross = sum(sizes[i] * sizes[j] for i in range(len(sizes))
                    for j in range(i + 1, len(sizes)))
        assert 6 == cross + sum(internal)
        assert (sorted(sizes), sum(internal)) in [([1, 4], 2), ([2, 3], 0)]
        signatures[(tuple(sorted(sizes)), sum(internal))] += 1
        for n in range(6, 13):
            assert len(A) == n and connected(A, B)
            assert negative_partition(A, B) == rho
            assert overlap_readings(A, B) == (6, 6)
            A, B = border(A, B)
    budget = []
    for orders in partitions(5):
        if len(orders) < 2:
            continue
        cross = sum(a * b for i, a in enumerate(orders) for b in orders[i + 1:])
        if cross <= 6:
            budget.append((orders, cross, 6 - cross))
    assert set(budget) == {((4, 1), 4, 2), ((3, 2), 6, 0)}

    def false_minimum_formula():
        assert all(first[rho] == max(x + i for i, x in enumerate(rho, 1))
                   for rho in all_parts)

    def false_six_rows_only():
        A, B = border(*witnesses[(4, 2)])
        assert not (len(A) == 7 and negative_partition(A, B) in open_parts)

    def false_cross_only_budget():
        assert all(cross == 6 for _, cross, _ in budget)

    expect_failure(false_minimum_formula, 'minimum-row formula with the terminal +1 omitted')
    expect_failure(false_six_rows_only, 'the open patterns occur only at six actual rows')
    expect_failure(false_cross_only_budget, 'six negatives are entirely cross-component')
    print('Six-negative strict endpoint words by row count:', dict(sorted(checked.items())))
    print('Partition orbits and directly realized minima:')
    for rho in orbits:
        print(' ', rho, '/', conjugate(rho), 'minimum', first[rho])
    print('Minimum-six component signatures:', dict(signatures))
    print('All six residual patterns realized and overlap-checked at every row count 6..12')
    print('ALL PASS')


if __name__ == '__main__':
    main()
