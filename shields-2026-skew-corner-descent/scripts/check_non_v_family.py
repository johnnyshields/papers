#!/usr/bin/env python3
"""The ordinary mark outside Hypothesis V, for every k in a range.

Paper sections `sec:transport` (An ordinary mark outside Hypothesis V) and
`sec:marks`; targets `eq:non-v-family`, `eq:non-v-factors`, `eq:non-v-jt`,
`eq:non-v-child`, `rem:comparison-v`, `rem:ordinary-gauge`.

E_k = (k,k,2)/(k-2) is built from partition data and compared with the
row-profile shape.  The maximality statement, the failure of V, the
normalization factors, the Jacobi--Trudi expansion, the row and rectangle
transport formulas with their spans, and the non-replacement of the finite
caps by full hatted marks are asserted for each k, 3 <= k <= K_MAX.  The
vertical reading of E_4 is checked to be a legal ordinary mark whose composition
agrees with the horizontal one after antitransposing the outer.
"""
from collections import Counter
from diagram_tools import (canonical, compose, connected_skew, corner_cofactor,
                           interior, jt_indices, legal_marks, mark_sets, multiply,
                           normalization, polynomial_span, power, profile_shape,
                           schur, shapes_of_area, span, translate)
from check_without_v import adjacent_cells

K_MAX = 12


def partition_shape(lam, mu):
    n = len(lam)
    return frozenset((i-n+1, j) for i in range(n) for j in range(mu[i], lam[i]))


def antitranspose(D):
    return canonical(frozenset((-j, -i) for i, j in D))


def main():
    counts = Counter()
    for k in range(3, K_MAX+1):
        Ek = profile_shape((2, k, 2), (1, 1))
        assert canonical(partition_shape((k, k, 2), (k-2, 0, 0))) == Ek     # eq:non-v-family
        rows = {}
        for i, j in Ek:
            rows.setdefault(i, []).append(j)
        assert [(min(js), max(js)) for _, js in sorted(rows.items(), reverse=True)] == \
            [(0, 1), (0, k-1), (k-2, k-1)]
        W = frozenset({(-1, 0), (0, 0)})
        v = (-1, k-1)
        p, w = v[1]-v[0], span(W)
        assert (p, w) == (k, 2)
        on_diagonals = {z for z in Ek if z[1]-z[0] in (0, 1)}
        assert on_diagonals - W == {(0, 1)}
        assert not connected_skew(W | {(0, 1)})                             # maximality of the mark
        assert (W, v, 'a') in list(legal_marks(Ek))
        O, What, Ohat = mark_sets(Ek, W, v)
        assert Ohat == frozenset()                                           # the middle is a ribbon
        assert len(adjacent_cells(W, O)) == len(adjacent_cells(translate(W, v), O)) == 2   # V fails
        assert What == frozenset({(-1, -1), (-1, 0)})                        # hat W is a row of two
        caps = interior(Ek)
        assert {z for z in caps if z[1]-z[0] < w} == {(-1, 0)}
        assert {z for z in caps if z[1]-z[0] >= p} == {(-2, k-2)}
        A, B, C, Theta = normalization(Ek, W, v)
        assert (A, B, C, Theta) == ({(1, 1): 1, (2,): -1}, {(2,): 1}, {(): 1}, {(1, 1): 1})   # eq:non-v-factors
        assert tuple(map(polynomial_span, (A, B, C, Theta))) == (2, 2, 0, 1)
        matrix = jt_indices(Ek)                                              # eq:non-v-jt
        assert matrix[0] == (2, k+1, k+2) and matrix[1] == (1, k, k+1)
        assert matrix[2][0] < 0 and matrix[2][1:] == (1, 2)
        assert schur(Ek) == {(2, 2, k): 1, (1, 2, k+1): -2, (1, 1, k+2): 1}
        assert corner_cofactor(Ek) == {(1, 1): 1}
        for m in range(1, 6):
            F = compose(profile_shape((m,), ()), Ek, W, v, 'a')
            exact = {(1, 1)+(2,)*(m-1): 1}
            assert corner_cofactor(F) == exact
            full_hats = multiply(power(B, m+1), power(C, m))                 # rem:comparison-v
            assert full_hats == {(2,)*(m+1): 1} and full_hats != exact
            counts['row amalgamations'] += 1
        D = profile_shape((3, 3), (2,))                                      # eq:non-v-child
        F = compose(D, Ek, W, v, 'a')
        child = compose(profile_shape((2,), ()), Ek, W, v, 'a')
        assert corner_cofactor(F) == multiply({(1, 1): 1}, schur(child))
        assert (span(F), span(child)) == (4*k+2, 2*k+2)
        counts['k values'] += 1
    # rem:ordinary-gauge on E_4: the display and the vertical ordinary reading
    E4 = profile_shape((2, 4, 2), (1, 1))
    assert canonical(partition_shape((4, 4, 2), (2, 0, 0))) == E4
    W, v = frozenset({(-1, 0), (0, 0)}), (-1, 3)
    assert translate(W, v) == frozenset({(-2, 3), (-1, 3)})                  # the letters u in the display
    vertical = [(Wb, vb, c) for Wb, vb, c in legal_marks(E4) if c == 'b' and vb == (v[0]-1, v[1]-1)]
    assert vertical, 'no ordinary vertical reading with displacement v - e'
    Wb, vb, _ = vertical[0]
    for n in range(2, 6):
        for D in shapes_of_area(n):
            assert compose(D, E4, W, v, 'a') == compose(antitranspose(D), E4, Wb, vb, 'b')
            counts['gauge compositions'] += 1
    h2, h11 = {(2,): 1}, {(1, 1): 1, (2,): -1}
    assert schur(profile_shape((2,), ())) == h2 != schur(frozenset({(0, 0), (-1, 0)}))
    assert schur(frozenset({(0, 0), (-1, 0)})) == h11
    row = profile_shape((2,), ())
    assert compose(row, E4, W, v, 'a') != compose(row, E4, Wb, vb, 'b')     # a nonsymmetric outer separates them
    print(dict(counts))
    print('check_non_v_family: PASS')


if __name__ == '__main__':
    main()
