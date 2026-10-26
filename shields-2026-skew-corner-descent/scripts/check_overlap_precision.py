#!/usr/bin/env python3
"""Check the common-window congruence at its actual, not enlarged, precision.

Original Jacobi--Trudi matrices are evaluated over the polynomial ring in h1.
The full determinant calculation is independent of eliminated response words.
"""
import sympy as sp


def square_chain(edges):
    rows, gaps = [2, 2], [1]
    for edge in edges:
        if edge == 'H':
            rows[-1] += 2
            rows.append(2)
            gaps.append(1)
        else:
            assert edge == 'V'
            rows.extend((2, 2))
            gaps.extend((0, 1))
    return rows, gaps


def determinant(profile, t):
    rows, gaps = profile
    n = len(rows)
    x, y = [0] * n, [0] * n
    x[-1] = rows[-1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    def h(j):
        if j < 0:
            return 0
        if j == 0:
            return 1
        if j == 1:
            return t
        return {2: 2, 4: 7}.get(j, j**3 + j + 3)
    return sp.Poly(sp.Matrix([[h(a - b) for b in y] for a in x]).det(method='domain-ge'), t)


def order(poly):
    assert not poly.is_zero
    return min(m[0] for m, _ in poly.terms())


def main():
    t = sp.Symbol('t')
    U = determinant(square_chain('HVVH'), t)
    W = determinant(square_chain('H'), t)
    E2 = determinant(square_chain('HVVHVVH'), t)
    difference = E2 * W - U**2
    assert U.eval(0) == 4 * 7**2 * 3**2
    assert W.eval(0) == 4 * 7
    assert order(difference) == 2
    assert difference.rem(sp.Poly(t**2, t)).is_zero
    assert not difference.rem(sp.Poly(t**5, t)).is_zero
    # The units do not alter normal order on division.
    assert U.eval(0) != 0 and W.eval(0) != 0
    print('PASS actual common-window bridge has order 2, not full corner order 5')
    print('PASS replacement of the overlap by the reciprocal window at full precision is rejected')


if __name__ == '__main__':
    main()
