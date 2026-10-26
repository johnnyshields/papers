"""An explicit I--IV mark outside Hypothesis V, with nonconstant factors."""
from collections import Counter
from diagram_tools import (compose, corner_cofactor, interior, legal_marks, mark_sets,
                           normalization, polynomial_span, profile, profile_shape,
                           schur, shapes_of_area, span, translate)
from verify_transport import check_mark, check_transport


def adjacent_cells(W, O):
    return frozenset((i, j) for i, j in W if any((i+x, j+y) in O
                     for x, y in ((1, 0), (-1, 0), (0, 1), (0, -1))))


def main():
    E = profile_shape((2, 4, 2), (1, 1))
    ordinary = [(W, v, c) for W, v, c in legal_marks(E) if W and c == 'a']
    assert ordinary
    counts = Counter()
    for W, v, case in ordinary:
        O, What, Ohat = mark_sets(E, W, v)
        lower = adjacent_cells(W, O)
        upper = adjacent_cells(translate(W, v), O)
        if min(len(lower), len(upper)) <= 1:
            continue
        print('inner', profile(E), 'W', sorted(W), 'v', v, 'case', case)
        print('adjacent mark cells', len(lower), len(upper), 'FAIL V')
        print('p,w', v[1]-v[0], span(W))
        A, B, C, Theta = normalization(E, W, v)
        print('A,B,C,Theta', A, B, C, Theta)
        print('spans', tuple(map(polynomial_span, (A, B, C, Theta))))
        check_mark(E, W, v, case, counts)
        for n in range(2, 7):
            for D in shapes_of_area(n):
                check_transport(D, E, W, v, case, counts)
        D = profile_shape((3, 3), (2,))
        F = compose(D, E, W, v, case)
        print('D', profile(D), 'F', profile(F), 'corner', corner_cofactor(F))
        counts['V failures'] += 1
    family = 0
    for k in range(3, 13):
        Ek = profile_shape((2, k, 2), (1, 1))
        W = frozenset({(-1, 0), (0, 0)})
        v = (-1, k-1)
        assert (W, v, 'a') in list(legal_marks(Ek))
        O, _, _ = mark_sets(Ek, W, v)
        assert len(adjacent_cells(W, O)) == len(adjacent_cells(translate(W, v), O)) == 2
        A, B, C, Theta = normalization(Ek, W, v)
        assert A == {(1, 1): 1, (2,): -1}
        assert B == {(2,): 1} and C == {(): 1} and Theta == {(1, 1): 1}
        assert schur(Ek) == {(2, 2, k): 1, (1, 2, k+1): -2, (1, 1, k+2): 1}
        for m in range(1, 5):
            F = compose(profile_shape((m,), ()), Ek, W, v, 'a')
            assert corner_cofactor(F) == {(1, 1)+(2,)*(m-1): 1}
        family += 1
    print('non-V family: k=3..12;', family, 'members; row amalgamations m=1..4')
    assert counts['V failures'], 'no mark outside V tested'
    assert counts['nonempty hatted marks'] and counts['wrong B exponent control']
    assert counts['omit caps control'] and counts['B exponent control']
    print(dict(counts))
    print('check_without_v: PASS')


if __name__ == '__main__':
    main()
