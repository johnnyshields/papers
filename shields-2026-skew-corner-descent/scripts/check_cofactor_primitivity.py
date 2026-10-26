#!/usr/bin/env python3
"""Check the affine corner and characteristic-independent primitivity in a box.

Original Jacobi--Trudi determinants are expanded over all permutations, without
using the cell-model supplement.  The signed extreme minor is computed by
SymPy's matrix determinant.  Integer content and coprimality of the two affine
coefficients are checked over the rationals and three finite fields.  This is
finite corroboration, not an all-size irreducibility proof.
"""
from itertools import permutations, product
from functools import reduce
from math import gcd
import sympy as sp
from sympy.polys.domains import GF, QQ
from sympy.polys.rings import ring


def expand_permutations(matrix):
    n = matrix.rows
    answer = 0
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        answer += (-1)**inversions * sp.prod(matrix[i, perm[i]] for i in range(n))
    return sp.expand(answer)


def check_affine(polynomial, top, signed_minor, variables):
    a = sp.diff(polynomial, top)
    c = polynomial.subs(top, 0)
    assert not a.has(top) and sp.expand(polynomial - a * top - c) == 0
    assert sp.expand(a - signed_minor) == 0
    coefficients = sp.Poly(polynomial, *variables).coeffs()
    assert reduce(gcd, (abs(int(x)) for x in coefficients)) == 1
    lower = tuple(h for h in variables if h != top)
    for field in (QQ, GF(2), GF(3), GF(5)):
        algebra = ring(lower, field)[0]
        ar, cr = algebra.from_expr(a), algebra.from_expr(c)
        assert ar and ar.gcd(cr).is_ground, (field, polynomial)


def main():
    hs = sp.symbols('h1:11')
    count = 0
    for size in range(1, 4):
        for lengths in product(range(1, 4), repeat=size):
            choices = [range(min(lengths[i], lengths[i + 1])) for i in range(size - 1)]
            for gaps in product(*choices):
                x, y = [0] * size, [0] * size
                x[-1] = lengths[-1]
                for i in range(size - 2, -1, -1):
                    y[i] = x[i + 1] - gaps[i]
                    x[i] = y[i] + lengths[i]
                span = x[0] - y[-1]
                def h(index):
                    return 0 if index < 0 else 1 if index == 0 else hs[index - 1]
                matrix = sp.Matrix([[h(a - b) for b in y] for a in x])
                polynomial = expand_permutations(matrix)
                minor = (-1)**(size - 1) * matrix.minor_submatrix(0, size - 1).det()
                check_affine(polynomial, hs[span - 1], minor, hs[:span])
                count += 1
    # Both controls would falsely suggest an affine primitive corner if only
    # the identity or only the top minor were checked.
    top, lower = hs[:2]
    for wrong, minor in ((2 * top + 2 * lower, 2), (lower * top + lower, lower)):
        try:
            check_affine(wrong, top, minor, (top, lower))
        except AssertionError:
            pass
        else:
            raise AssertionError('nonprimitive/common-factor control survived')
    print('PASS affine extreme minors and integer content:', count, 'connected row profiles')
    print('PASS affine coefficient gcd over QQ and GF(2), GF(3), GF(5); two mutations rejected')


if __name__ == '__main__':
    main()
