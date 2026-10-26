"""Check corner extraction and interior bounds from independent cell sets.

The full free-h Jacobi--Trudi polynomial supplies the left side, not its
known cofactor.  The right side is rebuilt by four-neighbor components of
the southeast interior.  The box includes every connected normalized shape
with at most five rows and six columns, plus a six-by-six square.
"""
from collections import Counter
from diagram_tools import (ONE, boxed_shapes, canonical, columns, components,
                           corner_cofactor, corner_from_polynomial, interior,
                           polynomial_span, profile_shape, rows, schur, span, translate)


def main():
    counts = Counter()
    shapes = list(boxed_shapes(5, 6))
    assert len(shapes) == len(set(shapes)), 'duplicate box enumeration'
    shapes.append(profile_shape((6,)*6, (5,)*5))
    for G in shapes:
        I = interior(G)
        northwest_deleted = frozenset((i, j) for i, j in G if (i-1, j-1) in G)
        assert translate(I, (1, 1)) == northwest_deleted
        value = corner_from_polynomial(G)
        assert value == schur(I) == corner_cofactor(G)
        assert polynomial_span(schur(G)) == span(G)
        assert max(map(len, schur(G))) == rows(G)
        assert len(I) == len(G)-span(G)
        counts['shapes'] += 1
        counts['nonempty interiors'] += bool(I)
        counts['disconnected interiors'] += len(components(I)) > 1
        if len(G) >= 2:
            pieces = components(I)
            rho = sum(rows(T) for T in pieces)
            chi = sum(columns(T) for T in pieces)
            L = sum(span(T) for T in pieces)
            assert rows(G)-1-rho >= 0
            assert columns(G)-1-chi >= 0
            assert span(G)-L >= 2
            counts['proper outer bounds'] += 1
        raw_coefficient = {mon: (-1)**(rows(G)-1)*c for mon, c in value.items()}
        counts['dropped sign control'] += raw_coefficient != schur(I)
        wrong = {tuple(j for j in mon if j != span(G)-1): (-1)**(rows(G)-1)*c
                 for mon, c in schur(G).items() if mon.count(span(G)-1) == 1}
        counts['wrong generator control'] += wrong != value
    assert counts['disconnected interiors'] and counts['dropped sign control']
    assert counts['wrong generator control']
    singleton = frozenset({(0, 0)})
    assert span(singleton)-sum(span(T) for T in components(interior(singleton))) == 1
    assert corner_from_polynomial(profile_shape((3,), ())) == ONE
    print(dict(counts))
    print('singleton-outer control: M-L=1, so properness is required')
    print('verify_corner: PASS')


if __name__ == '__main__':
    main()
