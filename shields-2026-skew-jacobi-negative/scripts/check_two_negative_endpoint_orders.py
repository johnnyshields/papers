#!/usr/bin/env python3
"""Exact endpoint checks on connected zero-free cores with at most two negatives.

Enumerate every strict endpoint order in the stated span windows, then compare
complete endpoint determinants with the collected cofactor expansion.  A subset
recurrence and signed permutations are distinct determinant computations.  The
finite checks corroborate the proof; they do not prove the every-order law.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations
from math import comb


def add(P, Q, scale=1):
    out = dict(P)
    for mon, value in Q.items():
        out[mon] = out.get(mon, 0) + scale * value
    return {mon: value for mon, value in out.items() if value}


def mul(P, Q):
    out = Counter()
    for m, a in P.items():
        for n, b in Q.items():
            out[tuple(sorted(m + n))] += a * b
    return {mon: value for mon, value in out.items() if value}


def h(index):
    return {} if index < 0 else {(() if index == 0 else (index,)): 1}


@lru_cache(maxsize=256)
def _determinant(A, B):
    layer = {0: {(): 1}}
    for a in A:
        following = {}
        for mask, poly in layer.items():
            for j, b in enumerate(B):
                if mask & (1 << j) or a < b:
                    continue
                sign = (-1) ** (mask >> (j + 1)).bit_count()
                target = mask | (1 << j)
                following[target] = add(following.get(target, {}), mul(poly, h(a - b)), sign)
        layer = following
    return tuple(sorted(layer.get((1 << len(A)) - 1, {}).items()))


def determinant(A, B):
    assert len(A) == len(B)
    return dict(_determinant(tuple(A), tuple(B)))


@lru_cache(maxsize=10)
def signed_permutations(n):
    return tuple((p, (-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n)))
                 for p in permutations(range(n)))


def determinant_permutations(A, B):
    out = Counter()
    for p, sign in signed_permutations(len(A)):
        indices = [A[i] - B[j] for i, j in enumerate(p)]
        if min(indices, default=0) < 0:
            continue
        out[tuple(sorted(index for index in indices if index))] += sign
    return {mon: value for mon, value in out.items() if value}


def normalize(A, B):
    return tuple(a - B[-1] for a in A), tuple(b - B[-1] for b in B)


def rotate(A, B):
    A, B = normalize(A, B)
    return tuple(A[0] - b for b in reversed(B)), tuple(A[0] - a for a in reversed(A))


def connected(A, B):
    return (len(A) == len(B) and all(a > b for a, b in zip(A, B))
            and all(A[i + 1] >= B[i] for i in range(len(A) - 1)))


def negative_shape(A, B):
    return tuple(count for count in reversed([sum(a < b for b in B) for a in A]) if count)


def top(P):
    return max((max(mon, default=0) for mon in P), default=0)


def coefficient(P, label, power=1):
    return {tuple(index for index in mon if index != label): value
            for mon, value in P.items() if mon.count(label) == power}


def minor(A, B, i, j):
    return determinant(A[:i] + A[i + 1:], B[:j] + B[j + 1:])


def up(A, B, t):
    return (A[0] + t,) + A[1:], B


def down(A, B, t):
    return A, B[:-1] + (B[-1] - t,)


def response(A, B, t):
    return add(determinant(*up(A, B, t)), determinant(*down(A, B, t)), -1)


def level_expansion(A, B, t, omit_last_column_level=False):
    n = len(A)
    out = {}
    for j in range(n - 1 - int(omit_last_column_level)):
        out = add(out, mul(h(A[0] - B[j] + t), minor(A, B, 0, j)), (-1) ** j)
    for i in range(1, n):
        out = add(out, mul(h(A[i] - B[-1] + t), minor(A, B, i, n - 1)), (-1) ** (i + n))
    return out


def strict_words(n):
    for inner in combinations(range(1, 2 * n - 1), n - 1):
        A = tuple(sorted(inner + (2 * n - 1,), reverse=True))
        B = tuple(sorted(set(range(2 * n)) - set(A), reverse=True))
        if connected(A, B) and sum(negative_shape(A, B)) <= 2:
            yield A, B


def cores(n, span):
    words = list(strict_words(n))
    for endpoints in combinations(range(1, span + 1), 2 * n - 1):
        values = (0,) + endpoints
        for A, B in words:
            yield tuple(values[a] for a in A), tuple(values[b] for b in B)


def expect_rejected(test, name):
    try:
        test()
    except AssertionError:
        print('CONTROL REJECTED:', name)
        return
    raise AssertionError('Control failed: ' + name)


def main():
    counts = Counter()
    by_order = Counter()
    by_branch = Counter()
    native_strata = set()
    for n in range(2, 9):
        box = list(cores(n, 2 * n))
        patterns = 1 if n == 2 else 2 if n == 3 else 4
        assert len(box) == patterns * comb(2 * n, 2 * n - 1)
        for A, B in box:
            assert connected(A, B) and not set(A) & set(B)
            nu = sum(negative_shape(A, B))
            symmetric = rotate(A, B) == (A, B)
            if nu == 2:
                assert n >= 4 and not symmetric
            kappa = max(A[1], A[0] - B[-2])
            assert 0 < kappa < A[0]
            branch = ('tie' if A[1] == A[0] - B[-2]
                      else 'row' if A[1] > A[0] - B[-2] else 'column')
            counts['cores'] += 1
            counts['two-negative cores'] += nu == 2
            counts['symmetric cores'] += symmetric
            by_order[n] += 1
            by_branch[(nu, branch)] += 1
            expected = {}
            if A[0] - B[-2] == kappa:
                expected = add(expected, minor(A, B, 0, n - 2), (-1) ** n)
            if A[1] == kappa:
                expected = add(expected, minor(A, B, 1, n - 1), (-1) ** (n + 1))
            assert bool(expected) == (not symmetric)
            assert top(expected) <= kappa
            if nu == 2 and n >= 5:
                R, T = A[1:], B[:-1]
                assert connected(R, T) and sum(negative_shape(R, T)) == 2
                if branch == 'tie':
                    child_response = response(R, T, B[-2])
                    assert expected == {mon: (-1) ** (n + 1) * c for mon, c in child_response.items()}
                    assert child_response
                    counts['higher-order tied child comparisons'] += 1
            strata = (n, nu, branch, symmetric)
            native = n <= 6 or strata not in native_strata
            native_strata.add(strata)
            for t in (1, 2, 5):
                actual = response(A, B, t)
                assert actual == level_expansion(A, B, t)
                if symmetric:
                    assert not actual
                else:
                    assert top(actual) == kappa + t
                    assert coefficient(actual, kappa + t) == expected
                    assert max(mon.count(kappa + t) for mon in actual) == 1
                for extended in (up(A, B, t), down(A, B, t)):
                    assert connected(*extended) and not set(extended[0]) & set(extended[1])
                    assert negative_shape(*extended) == negative_shape(A, B)
                    if native:
                        assert determinant(*extended) == determinant_permutations(*extended)
                        counts['permutation cross-checks'] += 1
                counts['endpoint differences'] += 1

    # The mutation is tested beyond the four-row base and within the exact-two-negative domain.
    A, B = (9, 8, 7, 5, 4), (6, 3, 2, 1, 0)
    assert connected(A, B) and not set(A) & set(B) and sum(negative_shape(A, B)) == 2
    assert len(A) == 5 and A[1] == A[0] - B[-2]
    def missing_endpoint_level():
        assert response(A, B, 1) == level_expansion(A, B, 1, omit_last_column_level=True)
    expect_rejected(missing_endpoint_level, 'omitting paper column m-1 on an admitted five-row two-negative core')
    def false_zero_at_tie():
        assert not coefficient(response(A, B, 1), 9)
    expect_rejected(false_zero_at_tie, 'canceling both top minors at an admitted higher-order tie')
    assert counts['cores'] == 256 and counts['two-negative cores'] == 120
    assert counts['endpoint differences'] == 768
    print('Counts:', dict(counts))
    print('Complete core windows, order n and span <=2n:', dict(by_order))
    print('Negative-count / top-branch counts:', dict(by_branch))
    print('Higher-order control coefficient:', coefficient(response(A, B, 1), 9))
    print('ALL PASS')


if __name__ == '__main__':
    main()
