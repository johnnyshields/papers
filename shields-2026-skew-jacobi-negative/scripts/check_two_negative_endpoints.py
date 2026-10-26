#!/usr/bin/env python3
"""Exact four-row/two-negative endpoint-leading verification.

Full permutation determinants are compared with a column-subset recurrence.
The claimed endpoint expansion and its tied disconnected-child coefficient are
then compared with the actual complete-function polynomial difference.  The
finite box corroborates, and does not replace, the range-free proof.
"""
from collections import Counter
from itertools import combinations, permutations
from functools import lru_cache


def clean(P):
    return {m: c for m, c in P.items() if c}


def add(P, Q, scale=1):
    out = dict(P)
    for mon, c in Q.items():
        out[mon] = out.get(mon, 0) + scale * c
    return clean(out)


def multiply(P, Q):
    out = Counter()
    for m, a in P.items():
        for n, b in Q.items():
            out[tuple(sorted(m + n))] += a * b
    return clean(out)


def h(k):
    return {} if k < 0 else {(() if k == 0 else (k,)): 1}


@lru_cache(maxsize=16)
def signed_permutations(n):
    return tuple((p, (-1) ** sum(p[i] > p[j] for i in range(n)
                                for j in range(i + 1, n)))
                 for p in permutations(range(n)))


def determinant(A, B):
    assert len(A) == len(B)
    out = Counter()
    for p, sign in signed_permutations(len(A)):
        indices = tuple(A[i] - B[p[i]] for i in range(len(A)))
        if min(indices, default=0) < 0:
            continue
        mon = tuple(sorted(k for k in indices if k))
        out[mon] += sign
    return clean(out)


def determinant_dp(A, B):
    n = len(A)
    layers = {0: {(): 1}}
    for a in A:
        following = {}
        for mask, polynomial in layers.items():
            for j, b in enumerate(B):
                if mask >> j & 1 or a < b:
                    continue
                sign = (-1) ** (mask >> (j + 1)).bit_count()
                new_mask = mask | (1 << j)
                term = multiply(polynomial, h(a - b))
                following[new_mask] = add(following.get(new_mask, {}), term, sign)
        layers = following
    return layers.get((1 << n) - 1, {})


def coefficient(P, label, power=1):
    return {tuple(k for k in mon if k != label): c for mon, c in P.items()
            if mon.count(label) == power}


def top(P):
    return max((max(mon, default=0) for mon in P), default=0)


def normalize(A, B):
    shift = B[-1]
    return tuple(a - shift for a in A), tuple(b - shift for b in B)


def rotate(A, B):
    A, B = normalize(A, B)
    return tuple(A[0] - b for b in reversed(B)), tuple(A[0] - a for a in reversed(A))


def endpoint(A, B, t):
    return add(determinant((A[0] + t,) + A[1:], B),
               determinant(A, B[:-1] + (B[-1] - t,)), -1)


def connected(A, B):
    return all(a > b for a, b in zip(A, B)) and all(
        A[i + 1] >= B[i] for i in range(len(A) - 1))


def negative_partition(A, B):
    return tuple(c for c in reversed([sum(a < b for b in B) for a in A]) if c)


def components(A, B):
    cuts = [0] + [i + 1 for i in range(len(A) - 1) if A[i + 1] < B[i]] + [len(A)]
    return [(A[i:j], B[i:j]) for i, j in zip(cuts, cuts[1:])]


def minor(A, B, i, j):
    return determinant(A[:i] + A[i + 1:], B[:j] + B[j + 1:])


def expect_failure(test, description):
    try:
        test()
    except AssertionError:
        print('CONTROL REJECTED:', description)
        return
    raise AssertionError('Control did not reject: ' + description)


def all_cores(span):
    for As in combinations(range(1, span + 1), 4):
        for Bs in combinations(sorted(set(range(1, span)) - set(As)), 3):
            A, B = tuple(reversed(As)), tuple(reversed(Bs)) + (0,)
            if connected(A, B) and sum(negative_partition(A, B)) == 2:
                yield A, B


def main():
    counts = Counter()
    polynomials = 0
    for A, B in all_cores(11):
        counts['cores'] += 1
        assert not set(A) & set(B)
        assert rotate(A, B) != (A, B)
        assert determinant(A, B) == determinant_dp(A, B)
        kappa = max(A[1], A[0] - B[-2])
        assert 0 < kappa < A[0]
        tied = A[1] == A[0] - B[-2]
        case = 'tie' if tied else ('row-dominant' if A[1] > A[0] - B[-2] else 'column-dominant')
        counts[case] += 1
        expected = {}
        if A[0] - B[-2] == kappa:
            expected = add(expected, minor(A, B, 0, 2))
        if A[1] == kappa:
            expected = add(expected, minor(A, B, 1, 3), -1)
        assert expected
        if tied:
            R, T = A[1:], B[:-1]
            child = components(R, T)
            assert sorted(len(C) for C, _ in child) == [1, 2]
            assert all(not negative_partition(C, D) for C, D in child)
            assert expected == {m: -c for m, c in endpoint(R, T, B[-2]).items()}
            singleton = next(C[0] - D[0] for C, D in child if len(C) == 1)
            # Reduction modulo the singleton variable directly sees the nonzero coefficient.
            assert {m: c for m, c in expected.items() if singleton not in m}
            counts['singleton-first' if len(child[0][0]) == 1 else 'singleton-last'] += 1
        for t in (1, 2, 5):
            delta = endpoint(A, B, t)
            actual_dp = add(determinant_dp((A[0] + t,) + A[1:], B),
                            determinant_dp(A, B[:-1] + (-t,)), -1)
            assert delta == actual_dp
            assert top(delta) == kappa + t
            assert max(mon.count(kappa + t) for mon in delta) == 1
            assert coefficient(delta, kappa + t) == expected
            expansion = {}
            for j in range(3):
                expansion = add(expansion, multiply(h(A[0] - B[j] + t),
                                                   minor(A, B, 0, j)), (-1) ** j)
            for i in range(1, 4):
                expansion = add(expansion, multiply(h(A[i] + t),
                                                   minor(A, B, i, 3)), (-1) ** i)
            assert expansion == delta
            polynomials += 1

    A, B = (7, 6, 4, 3), (5, 2, 1, 0)
    assert connected(A, B) and not set(A) & set(B)
    assert sum(negative_partition(A, B)) == 2
    assert A[1] == A[0] - B[-2]
    delta = endpoint(A, B, 1)

    def omit_second_tied_minor():
        assert coefficient(delta, 7) == minor(A, B, 0, 2)

    def omit_extension_from_top():
        assert top(delta) == max(A[1], A[0] - B[-2])

    expect_failure(omit_second_tied_minor,
                   'one-minor coefficient at a tied top, on an admitted two-negative core')
    expect_failure(omit_extension_from_top,
                   'unshifted top index, on the same admitted core')
    assert counts == Counter({'cores': 660, 'tie': 296, 'singleton-first': 148,
                              'singleton-last': 148, 'row-dominant': 182,
                              'column-dominant': 182})
    assert polynomials == 1980
    assert coefficient(delta, 7) == {(1, 2, 3): 2, (1, 1, 4): -1, (2, 2, 2): -1}
    print('Four-row, two-negative zero-free cores of span <=11:', dict(counts))
    print('Endpoint differences at t=1,2,5:', polynomials)
    print('All coefficients are nonzero, independent of t, and agree with two determinant routes')
    print('Control coefficient [h_7] Delta for (7,6,4,3)/(5,2,1,0):', coefficient(delta, 7))
    print('ALL PASS')


if __name__ == '__main__':
    main()
