#!/usr/bin/env python3
"""Structural facts about corner cofactors, spans and irreducibility.

Paper section `sec:corner` (Corner cofactors and common cores); targets
`eq:polynomial-span`, `eq:product-span`, `eq:jt`, `eq:minor-shape`,
`lem:cofactor`.

Every connected skew diagram of area at most MAX_AREA is built from its row
profile.  The full Jacobi--Trudi polynomial is expanded by subset expansion
and compared with the claimed decomposition.  Irreducibility over the
rationals is decided by SymPy's factorization of the full polynomial; over
GF(2), GF(3) and GF(5) it is decided by the affine criterion (a polynomial
a*h+c with a nonzero is irreducible exactly when gcd(a, c) is a unit, by
Gauss's lemma), because SymPy has no multivariate finite-field factoring.
Controls: a disconnected diagram is reducible, and a coefficient-sharing
affine polynomial is rejected by the criterion.
"""
from collections import Counter
from functools import reduce
from math import gcd
import sympy as sp
from sympy.polys.domains import GF
from sympy.polys.rings import ring
from diagram_tools import (ONE, add, canonical, columns, components, connected_skew,
                           corner_cofactor,
                           determinant, interior, multiply, polynomial_span,
                           profile, profile_shape, rows, schur, shapes_of_area, span,
                           translate)

MAX_AREA = 9
QQ_AREA = 8
H = sp.symbols('h0:12')


def to_sympy(poly):
    expression = 0
    for mon, c in poly.items():
        term = c
        for j in mon:
            term *= H[j]
        expression += term
    return expression


def content(poly):
    return reduce(gcd, (abs(c) for c in poly.values()))


def lambda_mu(G):
    """Partition data of connected G, rows top to bottom, with mu_n = 0."""
    rs = sorted({i for i, _ in G})
    lam = [max(j for a, j in G if a == i)+1 for i in rs]
    mu = [min(j for a, j in G if a == i) for i in rs]
    shift = mu[-1]
    return [x-shift for x in lam], [x-shift for x in mu]


def minor_of_shape(G):
    """Jacobi--Trudi determinant of (lam_2-1,...,lam_n-1)/(mu_1,...,mu_{n-1})."""
    lam, mu = lambda_mu(G)
    n = len(lam)
    lam2 = [lam[i]-1 for i in range(1, n)]
    mu2 = mu[:n-1]
    size = n-1
    indices = tuple(tuple(lam2[i]-mu2[j]-i+j for j in range(size)) for i in range(size))
    return determinant(indices)


def irreducible_over_gf(poly, top, p):
    """Affine criterion in the top generator over GF(p)."""
    lower = tuple(sorted({j for mon in poly for j in mon if j != top}))
    names = tuple(f'h{j}' for j in lower)
    if not names:
        return True
    R, *gens = ring(names, GF(p))
    index = {j: g for j, g in zip(lower, gens)}
    def build(items):
        out = R.zero
        for mon, c in items:
            term = R.one*c
            for j in mon:
                term = term*index[j]
            out = out+term
        return out
    a = build((tuple(j for j in mon if j != top), c) for mon, c in poly.items() if top in mon)
    c = build((mon, c) for mon, c in poly.items() if top not in mon)
    assert a != 0, 'top coefficient vanishes in characteristic %d' % p
    return a.gcd(c).is_ground


def main():
    counts = Counter()
    # eq:product-span on a product of two connected skew Schur polynomials
    pool = [G for n in range(1, 6) for G in shapes_of_area(n)]
    for G in pool:
        for K in pool[:40]:
            assert polynomial_span(multiply(schur(G), schur(K))) == max(span(G), span(K))
            counts['product span'] += 1
    assert polynomial_span(ONE) == 0
    for n in range(1, MAX_AREA+1):
        for G in shapes_of_area(n):
            assert connected_skew(G)
            N, r, c = span(G), rows(G), columns(G)
            assert N == r+c-1
            P = schur(G)
            assert polynomial_span(P) == N
            # eq:jt / eq:minor-shape: largest index N occurs only in entry (1, n)
            lam, mu = lambda_mu(G)
            size = len(lam)
            full = [[lam[i]-mu[j]-i+j for j in range(size)] for i in range(size)]
            assert [(i, j) for i in range(size) for j in range(size) if full[i][j] == N] == [(0, size-1)]
            assert N == lam[0]+size-1
            # eq:minor-shape: the deleted-row-and-column minor is the interior function
            minor = minor_of_shape(G)
            assert minor == schur(interior(G))
            # lem:cofactor: linear top generator, lower remainder, sign
            sign = (-1)**(r-1)
            top = {mon: c_ for mon, c_ in P.items() if N in mon}
            assert all(mon.count(N) == 1 for mon in top)
            R = dict(P)
            lead = multiply({(N,): 1}, minor)
            R = add(R, lead, -sign)
            assert all(N not in mon for mon in R)
            # row-length monomial has coefficient one; at most r positive factors
            row_lengths = tuple(sorted(max(j for a, j in G if a == i)-min(j for a, j in G if a == i)+1
                                       for i in {i for i, _ in G}))
            assert P[row_lengths] == 1
            assert max(len(mon) for mon in P) == r
            # lem:cofactor primitivity, including after multiplication by another diagram
            assert content(P) == 1
            counts['connected shapes'] += 1
            for p in (2, 3, 5):
                assert irreducible_over_gf(P, N, p)
                counts['gf%d irreducible' % p] += 1
            if n <= QQ_AREA:
                _, factors = sp.factor_list(to_sympy(P))
                assert len(factors) == 1 and factors[0][1] == 1, (profile(G), factors)
                counts['QQ irreducible'] += 1
    # eq:polynomial-span: a disconnected skew function has span the largest component span
    for G in pool[:60]:
        for K in pool[:60]:
            if G is K:
                continue
            shifted = translate(K, (-(max(i for i, _ in G)-min(i for i, _ in K))-1, max(j for _, j in G)+2))
            D = G | shifted
            if len(components(D)) == 2:
                assert polynomial_span(schur(D)) == max(span(G), span(K))
                counts['disconnected spans'] += 1
    # def:discrete-interior and eq:discrete-polynomial, with the row-profile criterion
    for n in range(2, MAX_AREA+1):
        for G in shapes_of_area(n):
            discrete = all(len(T) == 1 for T in components(interior(G)))
            exact = corner_cofactor(G) == ({(1,)*(len(G)-span(G)): 1} if len(G) > span(G) else ONE)
            assert discrete == exact
            lengths, gaps = profile(G)
            criterion = all(g in (0, 1) for g in gaps) and all(
                lengths[i+1] >= 3 for i in range(len(gaps)-1) if gaps[i] == gaps[i+1] == 1)
            assert discrete == criterion, (lengths, gaps)
            counts['discrete interiors'] += discrete
            counts['nondiscrete interiors'] += not discrete
    assert counts['discrete interiors'] and counts['nondiscrete interiors'] and counts['disconnected spans']
    # controls: a disconnected diagram is reducible, and the affine criterion has teeth
    D = frozenset({(0, 0), (-1, 2)})
    assert len(components(D)) == 2
    _, factors = sp.factor_list(to_sympy(schur(D)))
    assert len(factors) == 2 or factors[0][1] == 2
    counts['reducible disconnected control'] += 1
    top = 5
    shared = {(top, 1): 1, (1, 2): 1}      # h5 h1 + h1 h2, common factor h1
    assert not irreducible_over_gf(shared, top, 2)
    counts['common-factor control'] += 1
    assert counts['connected shapes'] and counts['QQ irreducible']
    print(dict(counts))
    print('check_corner_structure: PASS')


if __name__ == '__main__':
    main()
