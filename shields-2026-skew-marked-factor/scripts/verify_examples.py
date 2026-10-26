"""Verify the displayed ordinary and mixed examples from exact cell geometry."""

from itertools import product

import sympy as sp

from schur_tools import (antitranspose, compose, decode, dimensions, from_profile,
                         h, hats, legal_marks, normalize, rotate, schur, shapes,
                         standard_tableaux, translate)
from _weighted_readout import composition_map, decode_mixed, elementary, weighted


def ordinary_two_row(x, y, d, w):
    E = from_profile((x, y), (d,))
    p = x + y - d - w
    marks = [(W, v, case) for W, v, case in legal_marks(E)
             if case == 'a' and v[1] - v[0] == p]
    assert len(marks) == 1
    return E, marks[0]


def main():
    total = 0
    for d, w, increment_x, increment_y in product(range(2), repeat=4):
        x, y = d + w + 1 + increment_x, d + w + 1 + increment_y
        E, (W, v, case) = ordinary_two_row(x, y, d, w)
        p = v[1] - v[0]
        expected_E = h(x) * h(y) - h(d) * h(x + y - d)
        assert schur(E) == sp.expand(expected_E)
        for size in range(2, 5):
            for D in shapes(size):
                P = schur(compose(D, E, W, v, case))
                a, inner, outer, T, U, ratios = decode(P, p)
                r, c, M = dimensions(D)
                f = standard_tableaux(D)
                assert T == sp.expand((-1) ** a * f * h(d) ** M * h(w) ** r)
                assert U == sp.expand((-1) ** (a - 1) * f * h(d) ** (M - 1)
                                     * h(w) ** (r - 1) * expected_E)
                total += 1
    E, (W, v, case) = ordinary_two_row(4, 5, 1, 2)
    D = from_profile((3, 2, 2), (1, 1))
    F, H = (compose(outer, E, W, v, case) for outer in (D, rotate(D)))
    assert F == from_profile((4, 7, 7, 8, 7, 8, 7, 5), (1, 1, 4, 5, 4, 5, 1))
    assert H == from_profile((4, 7, 8, 7, 8, 7, 7, 5), (1, 4, 5, 4, 5, 1, 1))
    assert len(F) == len(H) == 53 and F != H and F != rotate(H)
    P = schur(F)
    assert P == schur(H)
    a, inner, outer, T, U, ratios = decode(P, 6)
    assert a == 7 and standard_tableaux(D) == 21 and dimensions(D) == (3, 3, 5)
    assert T == -21 * h(1) ** 5 * h(2) ** 3
    assert U == sp.expand(21 * h(1) ** 4 * h(2) ** 2 * (h(4) * h(5) - h(1) * h(8)))
    expected_outer = (h(3) * h(2) ** 2 - h(3) ** 2 * h(1) - h(4) * h(2) * h(1)
                      + h(4) * h(3) + h(5) * h(1) ** 2 - h(5) * h(2))
    assert outer == sp.expand(expected_outer)
    print('Two-row terminal-formula checks:', total)
    print('53-cell pair: equal, nonrotation; outer tableau number 21; both tails and outer recovered')
    # The gauge example also fires if the involution is deliberately omitted.
    E = from_profile((2, 1), (0,))
    row = from_profile((2,), ())
    F = compose(row, E, frozenset(), (-1, 2), 'a')
    G = compose(antitranspose(row), E, frozenset(), (-2, 1), 'b')
    assert F == G
    decoded_outer = decode(schur(F), 3)[2]
    assert decoded_outer == h(2) and decoded_outer != schur(antitranspose(row))
    print('CONTROL: vertical example recovers h2, not e2')
    # eq:mixed-example: the actual marked hook, not an abstract substitution.
    E = normalize(frozenset({(0, 0), (0, 1), (1, 0)}))
    W = frozenset({(0, 0)})
    v, case = (-1, 1), 'd'
    assert (W, v, case) in list(legal_marks(E))
    O, What, Ohat = hats(E, W, v)
    assert O == frozenset({(-1, 0)}) and not What and not Ohat
    row = from_profile((2,), ())
    F = compose(row, E, W, v, case)
    assert F == normalize(E | translate(E, v))
    assert F == from_profile((2, 2, 1), (0, 0))
    P = schur(F)
    expected = h(1) * h(2) ** 2 - h(2) * h(3) - h(1) * h(4) + h(5)
    assert P == sp.expand(expected)
    assert weighted(P, 2) == sp.expand(-3 * (h(1) * h(2) - h(3)))
    assert weighted(weighted(P, 2), 2) == 3 * h(1)
    assert weighted(weighted(weighted(P, 2), 2), 2) == 0
    assert weighted(P, 4) == h(1)
    got = decode_mixed(P, 2)
    assert got['area'] == 2 and got['inner'] == schur(E)
    assert got['rho'] == 1 and got['chi'] == -h(1) and got['outer'] == h(2)
    assert got['ratios'] == {(2,): sp.Rational(1, 3), (1, 1): sp.Integer(1)}
    assert composition_map(h(2), E, W, v, case) == sp.expand(h(1) * P)
    column = from_profile((1, 1), (0,))
    column_parent = compose(column, E, W, v, case)
    assert column_parent == from_profile((3, 2, 1), (1, 0))
    assert len(column_parent) == len(F) + 1
    assert composition_map(elementary(2), E, W, v, case) == -schur(column_parent)
    assert composition_map(elementary(2), E, W, v, case) != schur(column_parent)
    print('PASS: legal mixed hook, exact weighted tail, full outer readout, and supplemental domino sign')
    print('ALL PASS')


if __name__ == '__main__':
    main()
