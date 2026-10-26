#!/usr/bin/env python3
"""Check singleton-context identities and saturated-column recovery exactly.

The context window uses representatives of each order, negative partition,
symmetry, and top-index regime.  Independent full-board enumeration exercises
common betas and zero-length raw singleton rows.  No finite window proves the
uniform rigidity theorem.
"""
import sys
sys.dont_write_bytecode = True
from collections import Counter
from hashlib import sha256
from itertools import combinations

from check_two_negative_endpoint_orders import (
    add, coefficient, connected, cores, determinant, determinant_permutations,
    down, expect_rejected, h, mul, negative_shape, normalize, response, rotate, top,
)


def parent(A, B, s, u, v, g):
    z = v + A[0] + g
    return ((z + s + u, z + s) + tuple(v + a for a in A),
            (z,) + tuple(v + b for b in B) + (0,))


def phi(A, B, u, v):
    return determinant((A[0] + u,) + A, B + (-v,))


def gamma(A, B):
    return tuple(2 * a + 1 for a in A), tuple(2 * b for b in B)


def gamma_polynomial(P, rows):
    return {tuple(sorted((1,) * (rows - len(mon)) + tuple(2 * i + 1 for i in mon))): c
            for mon, c in P.items()}


def orbit(A, B):
    return min(normalize(A, B), rotate(A, B))


def intrinsic(A, B, minimum_rows=6):
    if len(A) < minimum_rows or not connected(A, B):
        return False
    return (sum(a < B[0] for a in A) == len(A) - 2
            and sum(a < b for a in A for b in B[1:]) <= 2)


def recover(A, B):
    A, B = normalize(A, B)
    v = B[-2]
    Q = tuple(a - v for a in A[2:]), tuple(b - v for b in B[1:-1])
    return Q, (A[1] - B[0], A[0] - A[1], v, B[0] - A[2])


def representative_cores():
    selected = {}
    for n in range(2, 7):
        for A, B in cores(n, 2 * n):
            left, right = A[1], A[0] - B[-2]
            regime = 'tie' if left == right else 'row' if left > right else 'column'
            key = n, negative_shape(A, B), rotate(A, B) == (A, B), regime
            selected.setdefault(key, (A, B))
    return list(selected.values())


def check_class(records, groups=None):
    if groups is None:
        groups = {}
    for (A, B), polynomial in records:
        # Hashes only locate candidates.  Every collision gets full polynomial comparison.
        key = sha256(repr(tuple(sorted(polynomial.items()))).encode()).digest()
        bucket = groups.setdefault(key, [])
        for old in bucket:
            if determinant(*old) == polynomial:
                assert orbit(*old) == orbit(A, B)
                break
        else:
            bucket.append((A, B))
    return sum(map(len, groups.values()))


def moving_margin(A, B, s, u, vminus, native=False):
    left = parent(A, B, s, u, vminus, 2)
    Ar, Br = rotate(A, B)
    right = parent(Ar, Br, s, u, vminus + 1, 1)
    assert left[0][0] == right[0][0]
    N, S = left[0][0], A[0]
    K = max(N - vminus, S + vminus + 1)
    right_polynomial, left_polynomial = determinant(*right), determinant(*left)
    if native:
        assert right_polynomial == determinant_permutations(*right)
        assert left_polynomial == determinant_permutations(*left)
    delta = add(right_polynomial, left_polynomial, -1)
    epsilon = (-1) ** (len(A) + 1)
    expected = {}
    product = mul(h(s), determinant(*down(A, B, vminus)))
    RA, RB = right
    T = RA[:2] + RA[3:], RB[:-1]
    assert connected(*T)
    complement = determinant(*T)
    assert top(product) < K and top(complement) < K
    if K == N - vminus:
        expected = add(expected, product, epsilon)
    if K == S + vminus + 1:
        expected = add(expected, complement, epsilon)
    assert expected and coefficient(delta, K) == expected
    assert top(delta) == K
    regime = 'tie' if N - vminus == S + vminus + 1 else (
        'upper' if N - vminus > S + vminus + 1 else 'lower')
    return regime, coefficient(delta, K), product, complement, epsilon


def full_boards(n, span):
    for xx in combinations(range(1, span + 1), n):
        A = xx[::-1]
        for yy in combinations(range(1, span), n - 1):
            B = yy[::-1] + (0,)
            if intrinsic(A, B):
                yield A, B


def from_partitions(lam, mu):
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return normalize(tuple(a - i for i, a in enumerate(lam, 1)),
                     tuple(b - i for i, b in enumerate(mu, 1)))


def transpose(part):
    return tuple(sum(a >= j for a in part) for j in range(1, max(part, default=0) + 1))


def cell_set(lam, mu):
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return {(i, j) for i, (a, b) in enumerate(zip(lam, mu)) for j in range(b + 1, a + 1)}


def covered_by_scalar_cutoffs(A, B):
    rho = negative_shape(A, B)
    nu = sum(rho)
    minimum = 1 + max((part + i for i, part in enumerate(rho, 1)), default=0)
    return nu <= 6 or (nu <= 9 and minimum >= 7) or (nu == 10 and minimum >= 8)


def main():
    selected = representative_cores()
    counts = Counter()
    regimes = Counter()
    fixtures = [(1, 1, 1, 1), (1, 1, 2, 1), (1, 2, 1, 1),
                (1, 1, 3, 1), (1, 1, 4, 1), (2, 2, 6, 1), (1, 2, 2, 2)]
    class_groups = {}
    class_count = 0
    for A, B in selected:
        n, S = len(A), A[0]
        f = determinant(A, B)
        records = []
        for s, u, v, g in fixtures:
            F = parent(A, B, s, u, v, g)
            assert connected(*F) and not set(F[0]) & set(F[1])
            assert sum(negative_shape(*F)) == n + sum(negative_shape(A, B))
            if n >= 4:
                assert intrinsic(*F)
            P = determinant(*F)
            a = s + g
            explicit = add(mul(h(s + u), phi(A, B, a, v)),
                           mul(h(s), phi(A, B, a + u, v)), -1)
            assert P == explicit
            N, q = F[0][0], min(u, v)
            epsilon = (-1) ** (n + 1)
            assert coefficient(P, N) == {mon: epsilon * c for mon, c in mul(h(s), f).items()}
            marker = {}
            if u <= v:
                marker = add(marker, mul(h(s + q), f))
            if v <= u:
                marker = add(marker, mul(h(s), determinant(*down(A, B, q))))
            assert coefficient(P, N - q) == {mon: -epsilon * c for mon, c in marker.items()}
            assert top(marker) < N - q and not coefficient(P, N - q, 2)
            div_s = all(s in mon for mon in marker)
            div_shift = all(s + q in mon for mon in marker)
            assert (div_s, div_shift) == ((False, True) if u < v else (True, False) if v < u else (False, False))
            regimes['top-small' if u < v else 'bottom-small' if v < u else 'equal'] += 1
            if (s, u, v, g) == fixtures[0]:
                assert determinant(*rotate(*F)) == P
                records.append((rotate(*F), P))
                counts['rotation checks'] += 1
                if n <= 5:
                    assert P == determinant_permutations(*F)
                    counts['native parent checks'] += 1
            records.append((F, P))
            if v > a + u and rotate(A, B) != (A, B):
                reversed_core = parent(*rotate(A, B), s, u, v, g)
                defect = add(P, determinant(*reversed_core), -1)
                inner = add(mul(h(s + u), response(A, B, a)),
                            mul(h(s), response(A, B, a + u)), -1)
                assert coefficient(defect, S + v) == {mon: epsilon * c for mon, c in inner.items()}
                kappa = max(A[1], S - B[-2])
                assert top(inner) == kappa + a + u < S + v
                counts['shared-outer-leader reflection checks'] += 1
            counts['parent identities'] += 1
        class_count = check_class(records, class_groups)
        for vminus in (2, 3, 4):
            regime, *_ = moving_margin(A, B, 1, 1, vminus)
            regimes['moving-' + regime] += 1
            counts['moving-margin comparisons'] += 1

    assert class_count == counts['parent identities']
    A, B = (9, 8, 7, 5, 4), (6, 3, 2, 1, 0)
    F = parent(A, B, 1, 1, 4, 1)
    H = parent(*rotate(A, B), 1, 1, 4, 1)
    PF, PH = determinant(*F), determinant(*H)
    assert PF == determinant_permutations(*F) and PH == determinant_permutations(*H)
    assert intrinsic(*F) and intrinsic(*H) and orbit(*F) != orbit(*H)
    assert PF != PH
    assert coefficient(PF, F[0][0]) == coefficient(PH, H[0][0])
    assert coefficient(PF, F[0][0] - 1) == coefficient(PH, H[0][0] - 1)
    expect_rejected(lambda: check_class([(F, PF), (H, PF)]),
                    'injected nonrotation equality on two admitted seven-row contexts')
    regime, actual, product, complement, epsilon = moving_margin(A, B, 1, 1, 3, native=True)
    counts['native calibration parents'] = 4
    assert regime == 'tie'
    def wrong_tied_sign():
        assert actual == {mon: epsilon * c for mon, c in add(product, complement, -1).items()}
    expect_rejected(wrong_tied_sign, 'subtracting the tied complementary term instead of adding it')

    geometry = Counter()
    sampled = Counter()
    for n in range(6, 10):
        for X, Y in full_boards(n, 2 * n - 4):
            geometry[(n, 'sources')] += 1
            Q, (s, u, v, g) = recover(X, Y)
            assert parent(*Q, s, u, v, g) == (X, Y)
            assert s >= 0 and min(u, v, g) > 0
            GX, GY = gamma(X, Y)
            GQ, gp = recover(GX, GY)
            assert GQ == gamma(*Q)
            assert gp == (2 * s + 1, 2 * u, 2 * v, 2 * g - 1)
            assert connected(*GQ) and not set(GQ[0]) & set(GQ[1])
            assert len(GQ[0]) == n - 2 and sum(negative_shape(*GQ)) <= 2
            assert parent(*GQ, *gp) == (GX, GY)
            assert intrinsic(GX, GY)
            if s == 0:
                geometry[(n, 'zero raw singleton')] += 1
            stratum = n, sum(negative_shape(*GQ)), s == 0
            if sampled[stratum] < 2:
                assert determinant(GX, GY) == gamma_polynomial(determinant(X, Y), n)
                sampled[stratum] += 1
                geometry[(n, 'full polynomial homogenizations')] += 1

    rawQ = (6, 5, 3, 2), (4, 2, 1, 0)
    raw = parent(*rawQ, 0, 1, 1, 1)
    assert intrinsic(*raw) and set(raw[0]) & set(raw[1])
    def wrong_gap_covariance():
        assert gamma(*raw) == parent(*gamma(*rawQ), 1, 2, 2, 2)
    expect_rejected(wrong_gap_covariance, 'using 2g rather than 2g-1 on an admitted unit-bearing source')

    family = Counter()
    for m in range(4, 29):
        lam = (m + 2, m + 2) + (m + 1,) * (m - 1) + (m - 1,)
        mu = (m, 1, 1) + (0,) * (m - 1)
        X, Y = from_partitions(lam, mu)
        assert intrinsic(X, Y) and not set(X) & set(Y)
        assert negative_shape(X, Y) == (3,) + (1,) * (m - 1)
        assert sum(negative_shape(X, Y)) == m + 2
        assert sum(lam) - sum(mu) == m * m + 2 * m
        Q, params = recover(X, Y)
        assert sum(negative_shape(*Q)) == 2 and params == (1, 1, 1, 1)
        LT, MT = transpose(lam), transpose(mu)
        assert from_partitions(LT, MT) == rotate(X, Y)
        cells = cell_set(lam, mu)
        assert {(j - 1, i + 1) for i, j in cells} == {
            (m + 1 - i, m + 3 - j) for i, j in cells}
        if m >= 9:
            assert not covered_by_scalar_cutoffs(X, Y)
            assert not covered_by_scalar_cutoffs(*from_partitions(LT, MT))
            family['beyond both-axis scalar cutoffs'] += 1
        family['members'] += 1

    # Sharpness of the height assumption is additional boundary evidence.
    X = (14, 11, 8, 5, 2)
    YF, YH = (9, 4, 3, 1, 0), (7, 6, 3, 1, 0)
    assert intrinsic(X, YF, minimum_rows=5) and not intrinsic(X, YF)
    assert determinant(X, YF) == determinant(X, YH)
    assert orbit(X, YF) != orbit(X, YH)
    def false_five_row_extension():
        assert not intrinsic(X, YF, minimum_rows=5) or orbit(X, YF) == orbit(X, YH)
    expect_rejected(false_five_row_extension, 'dropping the six-row lower bound from the intrinsic theorem')

    assert all(geometry[(n, 'zero raw singleton')] > 0 for n in range(6, 10))
    assert counts['shared-outer-leader reflection checks'] > 0
    print('Representative cores:', len(selected))
    print('Context counts:', dict(counts), 'exact class groups:', class_count)
    print('Marker regimes:', dict(regimes))
    print('Complete full-board geometry windows (rows n, span <=2n-4):', dict(geometry))
    print('Unbounded-family checks, m=4..28:', dict(family))
    print('ALL PASS')


if __name__ == '__main__':
    main()
