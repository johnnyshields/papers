#!/usr/bin/env python3
"""Exact high-derivative, cap, and arbitrary-profile checks for power rigidity.

The finite sweeps are cross-checks, not substitutes for the uniform proof.
Arbitrary mates are enumerated from the recovered row and gap multisets;
no excess vector is imposed on a candidate.
"""
from itertools import permutations, product
from profile_tools import (add, admitted, balanced_positions, betas, boundary, cap,
                           coefficient, derivative, excesses, from_excess, hessenberg, inner,
                           monomial, mul, power, rotate, scale, schur)


def denominator_complement(all_gaps, *parts):
    remaining = list(all_gaps)
    for part in parts:
        for q in part:
            remaining.remove(q)
    return monomial(remaining)


def high_identity(D):
    n = len(D[0])
    N = betas(D)[0][0]
    f = schur(D)
    assert f == hessenberg(D), D
    for v in range(N - max(D[1])):
        rhs = {}
        for i in range(n):
            A, L, q = boundary(D, 'left', i)
            for j in range(n-i):
                B, R, r = boundary(D, 'right', j)
                if A + B == v:
                    term = mul(mul(L, R), denominator_complement(D[1], q, r))
                    rhs = add(rhs, term)
        assert scale(derivative(f, N-v), (-1)**(n-1)) == rhs, (D, v)
    # Before only one row remains, at least one unread boundary is safe.
    for l in range(1, n):
        for r in range(1, n-l+1):
            A = boundary(D, 'left', l)[0]
            B = boundary(D, 'right', r)[0]
            assert min(A, B) < N - max(D[1]), (D, l, r)


def cap_identity(D, l, H, G):
    rows, gaps = D
    base = rows[:l-1] + (rows[l-1]-gaps[l-1],)
    lo = base[:-1] + (base[-1]+H,), gaps[:l-1]
    hi = base[:-1] + (base[-1]+G,), gaps[:l-1]
    J = cap(D, l, H, G)
    assert schur(J) == add(mul(monomial((G,)), schur(lo)),
                           scale(mul(monomial((H,)), schur(hi)), -1))


def prefix_separator(g, p, m, j):
    d = next(i+1 for i, (a, b) in enumerate(zip(g, g[::-1])) if a != b)
    l = j*len(g)+d
    D = power(inner(g, p), m)
    assert 2*l <= len(D[0])
    G, H = sorted((g[d-1], g[-d]), reverse=True)
    JL, JR = cap(D, l, H, G), cap(rotate(D), l, H, G)
    assert sorted(JL[1]) == sorted(JR[1])
    S = betas(inner(g, p))[0][0]
    zeta = sum(g[:d-1])+d*p
    N = betas(JL)[0][0]
    assert N == j*S+zeta+G
    assert j*S+G > max(JL[1])
    # Determinant derivatives versus independent interval prefix expansion.
    lhs = scale(derivative(add(schur(JL), scale(schur(JR), -1)), j*S+G), (-1)**l)
    _, L, q = boundary(JL, 'left', d)
    _, R, r = boundary(JR, 'left', d)
    rhs = add(mul(L, denominator_complement(JL[1], q)),
              scale(mul(R, denominator_complement(JR[1], r)), -1))
    assert lhs == rhs and rhs, (g, p, m, j)
    assert boundary(JL, 'right', d+1)[0] == zeta+G+p
    assert boundary(JR, 'right', d+1)[0] == zeta+G+p


def arbitrary_mates(D):
    target = schur(D)
    assert hessenberg(D) == target
    found = set()
    tested = 0
    gap_orders = set(permutations(D[1]))
    for rows in set(permutations(D[0])):
        for gaps in gap_orders:
            C = rows, gaps
            if min(excesses(C)) <= 0:
                continue
            tested += 1
            if hessenberg(C) == target:
                found.add(C)
    assert found == {D, rotate(D)}, (D, found)
    return tested


def main():
    derivative_cases = 0
    # Nonpalindromic excesses and repeated/contaminated labels are included.
    for n in range(2, 5):
        for gaps in product((1, 2), repeat=n-1):
            for e in product((1, 2), repeat=n):
                high_identity(from_excess(gaps, e))
                derivative_cases += 1
    for D in (inner((1, 3, 2), 1), power(inner((1, 2), 1), 2)):
        high_identity(D)
        for l in range(1, len(D[0])):
            for H, G in ((1, 2), (2, 3)):
                cap_identity(D, l, H, G)
    contaminated = schur(inner((1, 3, 2), 1))
    assert coefficient(contaminated, (2, 2)) == add(monomial((5, 7), -1), monomial((3, 9)))
    assert coefficient(contaminated, (3, 3)) == add(monomial((2, 8), -1), monomial((1, 9)))
    cap_cases = 0
    for g in ((1, 2, 3, 1), (1, 1, 2, 3, 1, 1), (2, 1, 3, 2, 1, 2)):
        assert admitted(g)
        for p in (1, 2):
            prefix_separator(g, p, 3, 1)
            cap_cases += 1
    for K in range(1, 6):
        assert all(admitted(g) for g in product((1, 2, 3), repeat=K))
    obstruction = (1, 2, 3, 2, 1, 2, 3, 1)
    assert balanced_positions(obstruction) == {1, 3, 5}
    assert not admitted(obstruction)
    D = inner(obstruction, 1)
    JL, JR = cap(D, 4, 1, 2), cap(rotate(D), 4, 1, 2)
    assert JL == rotate(JR) and schur(JL) == schur(JR)
    checked = sources = 0
    for K in range(1, 5):
        for g in product((1, 2, 3), repeat=K):
            for p in (1, 2):
                for m in range(1, 4//K+1):
                    D = power(inner(g, p), m)
                    checked += arbitrary_mates(D)
                    sources += 1
    for g, m in (((1, 3, 2), 2), ((1, 2, 3, 1), 1), ((1, 2, 2, 1), 1)):
        checked += arbitrary_mates(power(inner(g, 1), m))
        sources += 1
    print(f"High-derivative identity: {derivative_cases+2} profiles, all safe deficits PASS")
    print(f"Balanced-prefix cap separators: {cap_cases} exact identities PASS")
    print(f"Arbitrary-profile search: {sources} sources, {checked} legal candidates PASS")
    print("Contaminated endpoints and excluded rotated-cap obstruction: PASS")
    print("ALL PASS")


if __name__ == '__main__':
    main()
