"""Exact composition, row-amalgamation, and normalization-span checks.

Legal end marks are enumerated by subsets and conditions I--IV.  The left
side is a minor of the parent's Jacobi--Trudi matrix; the right side uses
independent four-neighbor component geometry.  Every accepted mark on
inners of two through eight cells is tested with every connected outer of
two through five cells.  Inners through four cells are also tested with
the three-by-three square.
"""
from collections import Counter
from diagram_tools import (canonical, columns, components, compose, corner_cofactor,
                           interior, legal_marks, mark_sets, multiply, nonadjacent,
                           normalization, polynomial_span, power, profile_shape,
                           rows, schur, shapes_of_area, span, translate)


def check_mark(E, W, v, case, counts):
    p, w = v[1]-v[0], span(W)
    O, What, Ohat = mark_sets(E, W, v)
    caps = interior(E)-Ohat
    A, B, C, Theta = normalization(E, W, v)
    assert polynomial_span(A) <= w < p
    assert polynomial_span(B) <= w
    assert polynomial_span(C) <= max(0, p-w-2)
    assert polynomial_span(Theta) <= max(0, w-1)
    assert corner_cofactor(E) == multiply(C, Theta)
    assert Theta == schur(caps)
    counts['marks'] += 1
    counts['case '+case] += 1
    counts['nonempty hatted marks'] += bool(What)
    counts['B bound lowered control'] += w > 0 and polynomial_span(B) == w
    counts['middle bound lowered control'] += p-w-2 > 0 and polynomial_span(C) == p-w-2
    counts['cap bound lowered control'] += w > 1 and polynomial_span(Theta) == w-1
    for m in range(1, 5):
        F = compose(profile_shape((m,), ()), E, W, v, case)
        expected = multiply(Theta, multiply(power(C, m), power(B, m-1)))
        assert corner_cofactor(F) == expected
        assert schur(interior(F)) == expected
        counts['row identities'] += 1
        counts['wrong B exponent control'] += expected != multiply(expected, B)
        counts['omit caps control'] += expected != multiply(power(C, m), power(B, m-1))
        minus = frozenset(z for z in interior(E) if z[1]-z[0] < w)
        plus = frozenset(z for z in interior(E) if z[1]-z[0] >= p)
        pieces = [minus, translate(plus, ((m-1)*v[0], (m-1)*v[1]))]
        pieces += [translate(Ohat, (j*v[0], j*v[1])) for j in range(m)]
        pieces += [translate(What, (j*v[0], j*v[1])) for j in range(1, m)]
        assert all(nonadjacent(a, b) for i, a in enumerate(pieces) for b in pieces[i+1:])
        assert canonical(frozenset().union(*pieces)) == canonical(interior(F))


def check_transport(D, E, W, v, case, counts):
    p, w = v[1]-v[0], span(W)
    F = compose(D, E, W, v, case)
    children = components(interior(D))
    rho = sum(rows(T) for T in children)
    chi = sum(columns(T) for T in children)
    L = sum(span(T) for T in children)
    exponents = rows(D)-1-rho, columns(D)-1-chi, span(D)-L
    assert min(exponents) >= 0 and exponents[2] >= 2
    assert span(F) == p*span(D)+w
    A, B, C, Theta = normalization(E, W, v)
    expected = multiply(Theta, multiply(power(A, exponents[0]),
                                       multiply(power(B, exponents[1]), power(C, exponents[2]))))
    for T in children:
        child = compose(canonical(T), E, W, v, case)
        assert span(child) == p*span(T)+w
        assert span(child) <= span(F)-2*p
        assert len(child) < len(F)
        expected = multiply(expected, schur(child))
        counts['proper children'] += len(T) >= 2
    actual = corner_cofactor(F)
    assert actual == expected, (D, E, W, v, case, exponents)
    counts['transport identities'] += 1
    counts['nonempty outer interiors'] += bool(children)
    counts['A exponent control'] += actual != multiply(expected, A)
    counts['B exponent control'] += actual != multiply(expected, B)


def main():
    counts = Counter()
    outers = [D for n in range(2, 6) for D in shapes_of_area(n)]
    for n in range(2, 9):
        tested_outers = outers + ([profile_shape((3, 3, 3), (2, 2))] if n <= 4 else [])
        for E in shapes_of_area(n):
            for W, v, case in legal_marks(E):
                check_mark(E, W, v, case, counts)
                for D in tested_outers:
                    check_transport(D, E, W, v, case, counts)
        print('inner area', n, dict(counts), flush=True)
    assert all(counts['case '+case] for case in 'abcd')
    for key in ('B bound lowered control', 'middle bound lowered control',
                'cap bound lowered control', 'wrong B exponent control',
                'omit caps control', 'A exponent control', 'B exponent control'):
        assert counts[key], key
    E = profile_shape((2, 1), (0,))
    W, v, case = next(mark for mark in legal_marks(E) if mark[2] == 'd')
    D = profile_shape((1, 1), (0,))
    full = compose(D, E, W, v, case)
    omitted = compose(D, E, W, v, case, supplemental=False)
    assert full != omitted and corner_cofactor(full) != corner_cofactor(omitted)
    print('mixed supplemental-copy control fired')
    print('verify_transport: PASS')


if __name__ == '__main__':
    main()
