#!/usr/bin/env python3
"""Paper sections `sec:positive-oo` (Positive ordinary comparison) and `sec:parent`
(Empty candidates and transfer to parents); targets `lem:oo-positive-gauge`,
`lem:two-layers`, `thm:chain-transfer`.

Check hook-template exponents and the first two image layers exactly.

The comparisons use direct Jacobi--Trudi determinants.  Formal residue and
first-normal substitutions are made in the matrix entries before expansion.
"""
import sympy as sp


def schur(shape, h):
    n = len(shape)
    if not n:
        return sp.Integer(1)
    return sp.expand(sp.Matrix([[h(shape[i] - i + j) for j in range(n)] for i in range(n)]).det(method='domain-ge'))


def partitions(n, maximum=None):
    if n == 0:
        yield ()
        return
    for first in range(min(n, maximum or n), 0, -1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


def interior_area(shape):
    return sum(max(x - 1, 0) for x in shape[1:])


def main():
    u, eps = sp.symbols('u eps')
    def residue(j):
        return 0 if j < 0 else 1 if j == 0 else u**(j - 1)
    def normal(j):
        if j <= 1:
            return 0 if j < 0 else 1
        return u**(j - 1) + (j - 2) * u**(j - 3) * eps
    hooks = layers = 0
    for size in range(1, 9):
        for leg in range(size):
            shape = (size - leg,) + (1,) * leg
            assert sp.cancel(schur(shape, residue) - u**(size - leg - 1) * (1 - u)**leg) == 0
            hooks += 1
        for shape in partitions(size):
            image = schur(shape, normal)
            area = interior_area(shape)
            assert (sp.expand(image).coeff(eps, 0) == 0) == (area > 0)
            if area >= 2:
                assert sp.expand(image).coeff(eps, 1) == 0
            if area == 1:
                a, leg = shape[0], len(shape) - 2
                coefficient = sp.expand(image).coeff(eps, 1)
                expected = -u**(a - 2) * (1 - u)**leg
                assert sp.cancel(coefficient - expected) == 0
            layers += 1
    # The zero-weight component must survive; the j=1 correction is not a rule.
    assert schur((), normal) == 1
    assert normal(1) == 1
    assert 1 - u**(-2) * eps != normal(1)
    transfers = 0
    for b, v in ((3, 1), (4, 1), (5, 2)):
        d = b - v
        for H, Z in ((0, 0), (1, 0), (0, 1), (1, 1)):
            m, J = H + Z + 1, (b + 1) * (H + Z + 1) - v
            for leg in range(J):
                lam = leg - (b + 1) * Z
                assert J - 1 - leg == (b + 1) * H + d - lam
                left = u**(J - 1 - leg) * (1 - u)**leg
                right = u**((b + 1) * H) * (1 - u)**((b + 1) * Z) * u**(d - lam) * (1 - u)**lam
                assert sp.cancel(left - right) == 0
                transfers += 1
    # Gauge placement: equality is literal, not equality of mark areas.
    i, j, v1, v2 = sp.symbols('i j v1 v2')
    direct = sp.Matrix([(j - i) * v1 + i, (j - i) * v2 + i])
    ii, jj = -j, -i
    dual = sp.Matrix([(jj - ii) * (v1 - 1) - ii, (jj - ii) * (v2 - 1) - ii])
    assert sp.simplify(direct - dual) == sp.zeros(2, 1)
    print('PASS direct hook determinants:', hooks, '; first-two-layer partition cases:', layers)
    print('PASS admitted hook exponents:', transfers, '; constant and singleton boundary controls')
    print('PASS literal ordinary-gauge placement identity')


if __name__ == '__main__':
    main()
