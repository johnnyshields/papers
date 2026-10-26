#!/usr/bin/env python3
"""Paper section `sec:lcm` (Primitive least-common-multiple comparison); targets
`lem:positive-endpoints` and `lem:class-correlation`.

Exact local checks used by the direct primitive comparison.

Positive-block endpoint correlations are compared with raw top determinants.
Two-block zero joins are checked against both independent permutation expansion
and the contraction identity.  This is not a census of source-minimal charts.
"""
from itertools import product
import sympy as sp
from check_window_recognition import jt as permutation_jt


def beta(rows, gaps):
    n = len(rows)
    y, x = [0] * n, [0] * n
    x[-1] = rows[-1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return x, y


def main():
    h = sp.symbols('h0:31')
    z = sp.Symbol('z')
    fixtures = [((2,), ()), ((3,), ())]
    fixtures += [(rows, (g,)) for rows in product(range(2, 5), repeat=2) for g in range(1, min(rows))]
    fixtures += [((3, 3, 3), (1, 1)), ((3, 4, 3), (2, 2)), ((2, 3, 2), (1, 1))]
    derivative_cases = 0
    for rows, gaps in fixtures:
        x, y = beta(rows, gaps)
        span, n = x[0], len(rows)
        M = sp.Matrix([[h[a - b] if a - b > 0 else 0 for b in y] for a in x])
        P = M.det()
        chi = sp.diff(P, h[span])
        assert chi != 0
        L = sum((-1)**(n - 1) * M.cofactor(i, n - 1) * z**(span - x[i]) for i in range(n))
        R = sum((-1)**(n - 1) * M.cofactor(0, j) * z**y[j] for j in range(n))
        LR = sp.Poly(sp.expand(L * R), z)
        for d in range(span):
            right = chi * sp.diff(P, h[span - d]) - P * sp.diff(chi, h[span - d])
            assert sp.expand(LR.nth(d) - right) == 0
            derivative_cases += 1
    joins = 0
    for A, B in product(fixtures[:8], repeat=2):
        rowsA, gapsA = A
        rowsB, gapsB = B
        rows = rowsA + rowsB
        gaps = gapsA + (0,) + gapsB
        def expr(rs, gs):
            value = permutation_jt(rs, gs)
            return sp.expand(sum(sp.Rational(c.numerator, c.denominator) * sp.prod(h[i] for i in mon) for mon, c in value.items()))
        joined = expr(rows, gaps)
        fused_rows = rowsA[:-1] + (rowsA[-1] + rowsB[0],) + rowsB[1:]
        fused_gaps = gapsA + gapsB
        assert sp.expand(joined - expr(*A) * expr(*B) + expr(fused_rows, fused_gaps)) == 0
        x, y = beta(rows, gaps)
        raw = sp.Matrix([[0 if a < b else 1 if a == b else h[a - b] for b in y] for a in x]).det(method='domain-ge')
        assert sp.expand(joined - raw) == 0
        joins += 1
    print('PASS positive-block profile derivatives:', derivative_cases, '; actual blocks:', len(fixtures))
    print('PASS zero-join contraction identities and independent raw determinants:', joins)


if __name__ == '__main__':
    main()
