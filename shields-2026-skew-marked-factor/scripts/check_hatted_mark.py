"""Exercise a nonempty hatted mark in both ordinary attachment conventions."""

import sympy as sp

from schur_tools import (compose, decode, delta, dimensions, from_profile, hats,
                         legal_marks, schur, standard_tableaux, transpose)


def main():
    E = from_profile((2, 4, 2), (1, 1))
    marks = [(W, v, case) for W, v, case in legal_marks(E)
             if v[1] - v[0] == 4 and case in ('a', 'b')]
    assert {case for W, v, case in marks} == {'a', 'b'}
    nonempty = tested = 0
    for W, v, case in marks:
        O, What, Ohat = hats(E, W, v)
        nonempty += bool(What)
        A, B, C = schur(W), schur(What), schur(Ohat)
        Xi = delta(schur(E), 4)
        sign = sp.cancel(Xi / (A * B * C))
        assert sign in (-1, 1)
        for D in (from_profile((2,), ()), from_profile((2, 2), (1,))):
            P = schur(compose(D, E, W, v, case))
            a, inner, outer, T, U, ratios = decode(P, 4)
            r, c, M = dimensions(D)
            assert T == sp.expand(sign ** a * standard_tableaux(D) * A ** r * B ** c * C ** M)
            assert a == len(D) and inner == schur(E)
            assert outer == schur(D if case == 'a' else transpose(D))
            tested += 1
    assert nonempty
    print('Eight-cell inner: nonempty hatted-mark readings', nonempty,
          '; exact terminal and recovery checks', tested)
    print('ALL PASS')


if __name__ == '__main__':
    main()
