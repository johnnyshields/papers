#!/usr/bin/env python3
"""Corroborate six-negative/minimum-six rigidity and full-board transport.

Two finite windows are completely enumerated and grouped by exact polynomials:
zero-free six-row boards of span at most 14, and all full six-row boards of
span at most 9.  These are finite corroboration, not arbitrary-mate proofs.
Controls use admitted sources and reject top-two-marker equality as full
Schur equality, and deleting genuine h_0 entries in homogenization.
"""
import sys
sys.dont_write_bytecode = True
from collections import Counter
from itertools import combinations

from check_two_negative_endpoints import (
    add, coefficient, connected, determinant, determinant_dp, expect_failure,
    negative_partition, normalize, rotate, signed_permutations, top,
)
from check_six_negative_patterns import strict_words


def minimum(rho):
    return 1 + max(x + i for i, x in enumerate(rho, 1)) if rho else 1


def admitted(A, B):
    rho = negative_partition(A, B)
    return connected(A, B) and sum(rho) == 6 and minimum(rho) == 6


def polynomial_key(P):
    return tuple(sorted(P.items()))


def orbit(A, B):
    return min(normalize(A, B), normalize(*rotate(A, B)))


def full_boards(span):
    for As in combinations(range(1, span + 1), 6):
        for Bs in combinations(range(1, span), 5):
            A, B = tuple(reversed(As)), tuple(reversed(Bs)) + (0,)
            if admitted(A, B):
                yield A, B


def zero_free_boards(span):
    words = [(A, B) for A, B in strict_words(6) if admitted(A, B)]
    assert len(words) == 6
    for endpoints in combinations(range(1, span + 1), 11):
        values = (0,) + endpoints
        for A, B in words:
            yield tuple(values[a] for a in A), tuple(values[b] for b in B)


def gamma(A, B):
    return tuple(2 * a + 1 for a in A), tuple(2 * b for b in B)


def homogenized(P, n):
    out = Counter()
    for mon, c in P.items():
        out[tuple(sorted((1,) * (n - len(mon)) + tuple(2 * k + 1 for k in mon)))] += c
    return {m: c for m, c in out.items() if c}


def border(A, B, u, v):
    return normalize((A[0] + u,) + A, B + (-v,))


def singleton_parent(A, B, s, u, v, g):
    z = v + A[0] + g
    return ((z + s + u, z + s) + tuple(v + a for a in A),
            (z,) + tuple(v + b for b in B) + (0,))


def drop_units_determinant(A, B):
    out = Counter()
    for p, sign in signed_permutations(len(A)):
        indices = tuple(A[i] - B[p[i]] for i in range(len(A)))
        if min(indices) <= 0:
            continue
        out[tuple(sorted(indices))] += sign
    return {m: c for m, c in out.items() if c}


def check_window(boards, name, transport=False):
    groups, actual = {}, set()
    counts, patterns = Counter(), Counter()
    example = None
    for A, B in boards:
        assert admitted(A, B)
        assert B[-1] == 0
        assert (A, B) not in actual
        actual.add((A, B))
        patterns[negative_partition(A, B)] += 1
        counts['sources'] += 1
        P = determinant_dp(A, B)
        assert P and top(P) == A[0]
        assert P == determinant(A, B)
        key = polynomial_key(P)
        canonical = orbit(A, B)
        assert groups.setdefault(key, canonical) == canonical
        assert rotate(A, B) != (A, B)
        assert determinant_dp(*rotate(A, B)) == P
        units = len(set(A) & set(B))
        assert max(map(len, P)) == 6
        assert min(map(len, P)) == 6 - units
        if units:
            counts['unit_sources'] += 1
            example = (A, B, P)
        if transport:
            GA, GB = gamma(A, B)
            assert admitted(GA, GB) and not set(GA) & set(GB)
            assert negative_partition(GA, GB) == negative_partition(A, B)
            assert determinant_dp(GA, GB) == homogenized(P, 6)
            assert normalize(*rotate(GA, GB)) == normalize(*gamma(*rotate(A, B)))
            counts['homogenizations'] += 1
    assert len(patterns) == 6
    assert len(actual) == 2 * len(groups)
    assert all(rotate(A, B) in actual for A, B in actual)
    print(name, dict(counts), 'rotation classes', len(groups))
    print('  counts by negative partition:', dict(sorted(patterns.items())))
    return example, actual


def main():
    _, zero_window = check_window(zero_free_boards(14), 'Zero-free six-row span <=14:')
    unit_example, full_window = check_window(full_boards(9), 'Full six-row span <=9:', transport=True)
    assert unit_example is not None
    assert len(zero_window) == 6 * 364
    assert len(full_window) == 50
    assert all(set(A) & set(B) for A, B in full_window)

    Q = (7, 6, 4, 3), (5, 2, 1, 0)
    F = singleton_parent(*Q, s=1, u=1, v=2, g=1)
    H = singleton_parent(*rotate(*Q), s=1, u=1, v=2, g=1)
    assert F in zero_window and H in zero_window
    assert F != H and rotate(*F) != H
    P, R = determinant(*F), determinant(*H)
    assert top(P) == top(R) == 12
    assert coefficient(P, 12) == coefficient(R, 12)
    assert coefficient(P, 11) == coefficient(R, 11)
    assert P != R
    witness_monomial = (1, 2, 4, 6, 6, 6)
    assert P.get(witness_monomial, 0) - R.get(witness_monomial, 0) == 1

    def false_top_two_suffice():
        assert P == R

    expect_failure(false_top_two_suffice,
                   'full equality inferred from equal top two markers, on two admitted sources')
    first_separator = next((mon, c - R.get(mon, 0)) for mon, c in P.items()
                           if c != R.get(mon, 0))
    print('Admitted marker-only false positive:', F, 'versus', H)
    print('  exact nonzero difference coefficient:', first_separator)

    A, B, original = unit_example

    def false_units_are_zeros():
        assert drop_units_determinant(A, B) == original

    expect_failure(false_units_are_zeros,
                   'h_0 set to zero on an admitted full-board source used by homogenization')
    print('Admitted unit control:', (A, B), 'common betas', sorted(set(A) & set(B)))

    border_count = Counter()
    for A, B in strict_words(6):
        if not admitted(A, B):
            continue
        for n in (7, 8):
            for u, v in ((1, 2), (2, 1), (2, 2)):
                C, D = border(A, B, u, v)
                assert len(C) == n and admitted(C, D)
                assert negative_partition(C, D) == negative_partition(A, B)
                P = determinant_dp(C, D)
                swapped = determinant_dp(*border(A, B, v, u))
                if u != v:
                    assert P != swapped
                    border_count['strict_swaps_separated'] += 1
                else:
                    M = C[0] - u
                    assert coefficient(P, M, 2)
                    border_count['tied_squares_nonzero'] += 1
                assert coefficient(P, C[0]) == {
                    mon: (-1) ** (n - 1) * c for mon, c in determinant_dp(A, B).items()}
                border_count['parents'] += 1
                if (u, v) == (1, 2):
                    assert P == determinant(C, D)
                    border_count['permutation_cross_checks'] += 1
            A, B = border(A, B, 1, 2)
    print('Connected bordering at seven and eight actual rows:', dict(border_count))
    assert border_count == Counter({'parents': 36, 'strict_swaps_separated': 24,
                                    'tied_squares_nonzero': 12,
                                    'permutation_cross_checks': 12})
    print('No sampled nonrotation equality; no finite window is used as the uniform proof')
    print('ALL PASS')


if __name__ == '__main__':
    main()
