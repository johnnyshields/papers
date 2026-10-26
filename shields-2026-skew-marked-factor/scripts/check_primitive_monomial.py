"""Paper section `sec:extraction` (Recovering the factors); results `lem:primitive` and `cor:two-row`.

Every connected skew diagram of at most eight cells: the row-length monomial of `s_D` has
coefficient +1 and is the unique monomial of least sum of squared subscripts, and `prim(q s_D) = s_D`
for rational `q` of both signs.  Two-row profiles `(x, y; d)` of up to fourteen cells: `s_D` is the
displayed two-term form, and the minimum-square monomial reads off the row-length multiset and the
second term reads off `d`, so only the interchange of `x, y` (a rotation) remains.  Uses sympy; the
Jacobi-Trudi expansion is `schur_tools.schur`, the row-length monomial is built from the diagram.
"""

from fractions import Fraction

import sympy as sp

from schur_tools import h, primitive, schur, shapes


def least_square_terms(poly):
    variables = sorted(poly.free_symbols, key=lambda x: int(x.name[1:]))
    terms = sp.Poly(poly, *variables).terms()
    cost = [(sum(e * int(v.name[1:]) ** 2 for e, v in zip(mon, variables)), mon, c)
            for mon, c in terms]
    low = min(c for c, _, _ in cost)
    return variables, [(mon, c) for k, mon, c in cost if k == low]


def main():
    diagrams = 0
    for n in range(1, 9):
        for D in shapes(n):
            diagrams += 1
            P = schur(D)
            rows = sorted(sum(1 for (i, j) in D if i == r) for r in {i for i, j in D})
            expected = sp.expand(sp.prod([h(k) for k in rows]))
            variables, low = least_square_terms(P)
            assert len(low) == 1, (sorted(D), low)
            (mon, coeff), = low
            assert coeff == 1, (sorted(D), coeff)
            monomial = sp.prod([v ** e for v, e in zip(variables, mon)])
            assert monomial == expected, (sorted(D), monomial, expected)
            for q in (Fraction(-3, 7), Fraction(5), Fraction(-1), Fraction(1, 4)):
                assert primitive(sp.Rational(q.numerator, q.denominator) * P) == P
    assert diagrams == sum(len(list(shapes(n))) for n in range(1, 9))
    two_row = 0
    for x in range(1, 8):
        for y in range(1, 8):
            for d in range(min(x, y)):
                D = next(s for s in shapes(x + y)
                         if sorted(sum(1 for (i, j) in s if i == r) for r in {i for i, j in s})
                         == sorted((x, y))
                         and len({i for i, j in s}) == 2
                         and len({j for i, j in s if i == min(a for a, b in s)}
                                 & {j for i, j in s if i == max(a for a, b in s)}) == d + 1
                         ) if x + y <= 12 else None
                if D is None:
                    continue
                P = schur(D)
                assert P == sp.expand(h(x) * h(y) - h(d) * h(x + y - d)), (x, y, d)
                variables, low = least_square_terms(P)
                (mon, coeff), = low
                assert coeff == 1 and sp.prod([v ** e for v, e in zip(variables, mon)]) == sp.expand(h(x) * h(y))
                rest = sp.expand(P - h(x) * h(y))
                assert rest == -sp.expand(h(d) * h(x + y - d))
                two_row += 1
    assert two_row > 20
    print(f'row-length monomial unique minimum, coefficient +1, prim(q s_D) = s_D: {diagrams} diagrams')
    print(f'two-row profiles with the displayed two-term form: {two_row}')
    print('ALL PASS')


if __name__ == '__main__':
    main()
