"""Verify factor recovery from cell-built ordinary marked compositions.

Default box: every connected inner of 2--5 cells and every I--IV ordinary
end mark, with every connected outer of 2--4 cells.  Jacobi--Trudi minors
are expanded by recursive Laplace expansion; the decoder sees only P and p.
"""

import argparse
from collections import Counter

import sympy as sp

from schur_tools import (apply, compose, decode, delta, dimensions, hats, legal_marks,
                         partitions, schur, shapes, standard_tableaux,
                         transpose)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-inner', type=int, default=5)
    parser.add_argument('--max-outer', type=int, default=4)
    args = parser.parse_args()
    outers = [D for n in range(2, args.max_outer + 1) for D in shapes(n)]
    counts = Counter()
    gauge_control = wrong_period_control = 0
    for n in range(2, args.max_inner + 1):
        for E in shapes(n):
            e_poly = schur(E)
            for W, v, case in legal_marks(E):
                if case not in ('a', 'b'):
                    continue
                counts['marks'] += 1
                p = v[1] - v[0]
                O, What, Ohat = hats(E, W, v)
                A, B, C = schur(W), schur(What), schur(Ohat)
                Xi = delta(e_poly, p)
                sign = sp.cancel(Xi / (A * B * C))
                assert sign in (-1, 1), (E, W, v, case, Xi, A, B, C)
                assert all(delta(Q, k * p) == 0 for Q in (A, B, C)
                           for k in range(1, n // p + 1))
                for D in outers:
                    F = compose(D, E, W, v, case)
                    P = schur(F)
                    a, got_E, got_D, T, U, ratios = decode(P, p)
                    expected_D = schur(D if case == 'a' else transpose(D))
                    assert a == len(D)
                    assert got_E == e_poly
                    assert got_D == expected_D, (D, E, case, got_D, expected_D)
                    r, c, M = dimensions(D)
                    f = standard_tableaux(D)
                    assert T == sp.expand(sign ** a * f * A ** r * B ** c * C ** M)
                    assert U == sp.expand(sign ** (a - 1) * f * A ** (r - 1)
                                          * B ** (c - 1) * C ** (M - 1) * e_poly)
                    assert sp.expand(U * Xi - T * e_poly) == 0
                    for nu in partitions(a):
                        assert ratios[nu] == apply(expected_D, nu) / f
                        counts['character_ratios'] += 1
                    counts['charts'] += 1
                    counts['case_' + case] += 1
                    counts['nonribbon'] += any((i + 1, j) in D and (i, j + 1) in D
                                               and (i + 1, j + 1) in D for i, j in D)
                    if case == 'b' and expected_D != schur(D):
                        assert got_D != schur(D)
                        gauge_control += 1
                    if wrong_period_control < 10:
                        try:
                            wrong = decode(P, p + 1)[:3]
                        except (ValueError, AssertionError):
                            wrong = None
                        if wrong != (a, e_poly, expected_D):
                            wrong_period_control += 1
        print(f'inner area {n}: {counts["charts"]} cumulative charts PASS', flush=True)
    assert counts['case_a'] and counts['case_b'] and counts['nonribbon']
    assert gauge_control > 0 and wrong_period_control == 10
    # Connectedness is necessary for the irreducible-numerator argument.
    assert sp.gcd(schur(next(shapes(2))) ** 2, schur(next(shapes(2)))) != 1
    print('EXTRACTION', dict(sorted(counts.items())))
    print('CONTROLS: omitted involution', gauge_control, '; wrong period', wrong_period_control)
    print('ALL PASS')


if __name__ == '__main__':
    main()
