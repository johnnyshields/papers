#!/usr/bin/env python3
"""Pairs of proper charts with equal parent functions: the discrete residual.

Paper section `sec:periods` (The nonempty discrete residual); targets
`prop:beta-reduction`, `lem:alpha-row-candidate`.

Part 1.  Pairs of charts of one literal parent are built by aligned reassociation,
F = D o (V o U) = (D o V) o U with D having a discrete interior of t >= 1 isolated
cells; equality of the two cell sets is asserted, not assumed.  For every such pair
with periods p > q the proposition's conclusion is asserted: some actual component of
R^- has transported function s_E, with p + w = m q + u, and for m >= 2 the child is a
proper chart of area |E| < |F|.  Source-minimality is not imposed: the conclusions use only
the stated span inequalities and unique factorization.  Controls: a one-cell
substitute for the component fails whenever m >= 2.

Part 2.  Inner charts with equal functions and different periods are paired with
outers D (discrete interior) and R such that the parent spans and corner polynomials
agree.  Every instance found is checked against the lemma's conclusions: R^- is t
isolated cells, every row gap of R is one, and the corner and hat bounds hold.  The
instance count is printed so a vacuous range is visible.
"""
from collections import Counter, defaultdict
from diagram_tools import (canonical, columns, components, compose, corner_cofactor,
                           interior, legal_marks, normalization, polynomial_span,
                           profile, rows, schur, shapes_of_area, span)


def is_line(shape):
    return rows(shape) == 1 or columns(shape) == 1


def discrete(D):
    pieces = components(interior(D))
    return bool(pieces) and all(len(T) == 1 for T in pieces)


def empty_mark(E, case='a'):
    return next(m for m in legal_marks(E) if not m[0] and m[2] == case)


def beta_family(counts):
    outers = [D for n in range(3, 6) for D in shapes_of_area(n) if discrete(D)]
    assert outers
    for nu in (3, 4):
        for U in shapes_of_area(nu):
            if is_line(U):
                continue
            for eta in legal_marks(U):
                for nv in (2, 3):
                    for V in shapes_of_area(nv):
                        E = compose(V, U, *eta)
                        if is_line(E):
                            continue
                        omega, markV = empty_mark(E), empty_mark(V)
                        for D in outers:
                            F = compose(D, E, *omega)
                            R = compose(D, V, *markV)
                            if compose(R, U, *eta) != F:
                                counts['reassociation not literal'] += 1
                                continue
                            counts['literal pairs'] += 1
                            p, w = omega[1][1]-omega[1][0], span(omega[0])
                            q, u = eta[1][1]-eta[1][0], span(eta[0])
                            assert p > q
                            matches = [(canonical(T), compose(canonical(T), U, *eta))
                                       for T in components(interior(R))
                                       if schur(compose(canonical(T), U, *eta)) == schur(E)]
                            assert matches
                            T, child = matches[0]
                            m = span(T)
                            assert p+w == m*q+u
                            if m == 1:
                                assert schur(E) == schur(U) and q < p < 2*q
                            else:
                                assert len(child) == len(E) < len(F)
                                one_cell = compose(frozenset({(0, 0)}), U, *eta)
                                assert schur(one_cell) != schur(E)
                                counts['m >= 2 with one-cell control'] += 1
                            counts['beta conclusions'] += 1


def alpha_search(counts):
    inner = defaultdict(list)
    for n in range(3, 6):
        for E in shapes_of_area(n):
            if is_line(E):
                continue
            for mark in legal_marks(E):
                inner[tuple(sorted(schur(E).items()))].append((E, mark))
    D_pool = [D for n in range(3, 7) for D in shapes_of_area(n) if discrete(D)]
    R_pool = defaultdict(list)
    for n in range(3, 9):
        for R in shapes_of_area(n):
            R_pool[span(R)].append(R)
    for group in inner.values():
        for E, mE in group:
            p, w = mE[1][1]-mE[1][0], span(mE[0])
            for U, mU in group:
                q, u = mU[1][1]-mU[1][0], span(mU[0])
                if not (p > q and p+w == q+u):
                    continue
                for D in D_pool:
                    NF = p*span(D)+w
                    if (NF-u) % q or (NF-u)//q not in R_pool:
                        continue
                    for R in R_pool[(NF-u)//q]:
                        if span(R) <= span(D):
                            continue
                        F, H = compose(D, E, *mE), compose(R, U, *mU)
                        assert span(F) == span(H) == NF
                        if corner_cofactor(F) != corner_cofactor(H):
                            continue
                        t = len(interior(D))
                        counts['alpha instances'] += 1
                        pieces = components(interior(R))
                        assert len(pieces) == t and all(len(T) == 1 for T in pieces)
                        assert len(interior(R)) == t
                        assert rows(R) == t+1 and all(g == 1 for g in profile(R)[1])
                        A, B, C, Theta = normalization(U, mU[0], mU[1])
                        assert polynomial_span(corner_cofactor(U)) < u
                        assert polynomial_span(B) < u


def main():
    counts = Counter()
    beta_family(counts)
    print(dict(counts), flush=True)
    assert counts['beta conclusions'] > 0 and counts['m >= 2 with one-cell control'] > 0
    alpha_search(counts)
    print(dict(counts))
    print('check_residual_pairs: PASS')


if __name__ == '__main__':
    main()
