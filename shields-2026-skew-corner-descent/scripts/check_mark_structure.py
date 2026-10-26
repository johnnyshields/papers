#!/usr/bin/env python3
"""Local geometry of legal marks, the cap decompositions, and the hypotheses.

Paper sections `sec:marks` (Marked inners and finite end caps); targets
`eq:mark-data`, `eq:local-properties`, `eq:caps`, `eq:cap-hat`,
`eq:erosion-union`, `lem:row-amalgamation`.

For every legal mark on inners of at most MAX_AREA cells the script checks, from
the cell sets alone: the mark data O, w, p; maximality W = E & (E - v), at most
one cell of O on each marked diagonal, and singleton diagonals E_w and E_{p-1};
the disjoint decomposition E^- = K_- + hat O + K_+ with the stated content
supports; hat W = K_- + (K_+ - v) with intersection W^-; and, for row outers
of one to four copies, the erosion of the union equals the union of the
erosions.

Hypotheses III and IV are then shown load-bearing: candidate end-copy pairs
satisfying the other hypotheses and failing exactly this one are enumerated,
and some of them must violate the row-amalgamation formula, its span bounds, or
corner transport for every connected outer of at most OUTER_AREA cells.
Hypothesis II (w < p) is shown necessary on the same candidates with w >= p.
Hypothesis I is not shown necessary for those conclusions: candidates failing
only I satisfy them throughout the range, and the census prints that count.
Maximality is used for the local properties, which every legal mark is checked
to satisfy; it is not a hypothesis whose removal changes those conclusions here.
"""
from collections import Counter
from diagram_tools import (canonical, columns, components, compose, connected_skew, corner_cofactor, interior, legal_marks,
                           mark_sets, multiply, nonadjacent, normalization,
                           polynomial_span, power, rows, schur, shapes_of_area, span, translate)

MAX_AREA = 8
NECESSITY_AREA = 9
OUTER_AREA = 4


def candidates(E, widths):
    """All (W, v) with W a connected skew set on the first w diagonals through the
    southwest cell, W + v inside E and reaching the northeast cell."""
    N = span(E)
    ne = max(E, key=lambda z: z[1]-z[0])
    for w in widths:
        p = N-w
        if p < 1:
            continue
        band = sorted(z for z in E if 0 <= z[1]-z[0] < w)
        for mask in range(1 << len(band)):
            W = frozenset(z for j, z in enumerate(band) if mask >> j & 1)
            if (0, 0) not in W or span(W) != w or not connected_skew(W):
                continue
            for v in E:
                if v[1]-v[0] == p and translate(W, v) <= E and ne in translate(W, v):
                    yield W, v


def hypotheses(E, W, v, pool):
    w, p = span(W), v[1]-v[0]
    upper = translate(W, v)
    maximal = not any(W < bigger for bigger, _ in pool)
    separated = w < p
    connected_after = connected_skew(E-W) and connected_skew(E-upper)
    O, What, Ohat = mark_sets(E, W, v)
    hatted = all(nonadjacent(Ohat, translate(What, (k*v[0], k*v[1]))) for k in (-1, 0, 1, 2))
    return maximal, separated, connected_after, hatted


def row_union(E, v, m):
    return canonical(frozenset().union(*(translate(E, (j*v[0], j*v[1])) for j in range(m))))


def attachment_case(E, W, v):
    """The attachment case of a candidate, or None when it is not unique."""
    O, _, _ = mark_sets(E, W, v)
    if not O or not connected_skew(O):
        return None
    upper = translate(W, v)
    sw = min(O, key=lambda z: z[1]-z[0])
    ne = max(O, key=lambda z: z[1]-z[0])
    lowerH, lowerV = (sw[0], sw[1]-1) in W, (sw[0]+1, sw[1]) in W
    upperH, upperV = (ne[0], ne[1]+1) in upper, (ne[0]-1, ne[1]) in upper
    cases = [c for c, ok in (('a', lowerH and upperH), ('b', lowerV and upperV),
                             ('c', lowerH and upperV), ('d', lowerV and upperH)) if ok]
    return cases[0] if len(cases) == 1 else None


def transport_holds(E, W, v, case):
    """Corner transport for every connected outer of at most OUTER_AREA cells."""
    p, w = v[1]-v[0], span(W)
    A, B, C, Theta = normalization(E, W, v)
    for n in range(2, OUTER_AREA+1):
        for D in shapes_of_area(n):
            try:
                F = compose(D, E, W, v, case)
            except AssertionError:
                return False
            children = components(interior(D))
            rho = sum(rows(T) for T in children)
            chi = sum(columns(T) for T in children)
            L = sum(span(T) for T in children)
            expected = multiply(Theta, multiply(power(A, rows(D)-1-rho),
                                multiply(power(B, columns(D)-1-chi), power(C, span(D)-L))))
            for T in children:
                expected = multiply(expected, schur(compose(canonical(T), E, W, v, case)))
            if corner_cofactor(F) != expected:
                return False
    return True


def conclusion_holds(E, W, v):
    try:
        return _conclusion_holds(E, W, v)
    except AssertionError:
        return False        # a normalization factor is not even a skew function


def _conclusion_holds(E, W, v):
    """Row-amalgamation formula for m = 1..3 and the span bounds, as the paper states them."""
    w, p = span(W), v[1]-v[0]
    A, B, C, Theta = normalization(E, W, v)
    if not (polynomial_span(A) <= w < p and polynomial_span(B) <= w
            and polynomial_span(Theta) <= max(0, w-1)
            and polynomial_span(C) <= max(0, p-w-2)):
        return False
    for m in range(1, 4):
        F = row_union(E, v, m)
        if not connected_skew(F):
            return False
        expected = multiply(Theta, multiply(power(C, m), power(B, m-1)))
        if schur(interior(F)) != expected:
            return False
    case = attachment_case(E, W, v)
    return case is None or transport_holds(E, W, v, case)


def main():
    counts = Counter()
    for n in range(2, MAX_AREA+1):
        for E in (canonical(frozenset(s)) for s in shapes_of_area(n)):
            N = span(E)
            for W, v, case in legal_marks(E):
                O, What, Ohat = mark_sets(E, W, v)
                w, p = span(W), v[1]-v[0]
                assert p == N-w and O == E-W-translate(W, v)          # eq:mark-data
                Eminus = interior(E)
                if w == 0:
                    assert span(O) == N and Ohat == Eminus
                    for z in Eminus:
                        assert 1 <= z[1]-z[0] <= p-2
                    counts['empty marks'] += 1
                    continue
                assert W == frozenset(z for z in E if translate({z}, v) <= E)   # eq:local-properties
                for k in list(range(w))+list(range(p, p+w)):
                    assert sum(1 for z in O if z[1]-z[0] == k) <= 1
                for k in (w, p-1):
                    assert sum(1 for z in E if z[1]-z[0] == k) == 1
                Kminus = frozenset(z for z in Eminus if 0 <= z[1]-z[0] < w)   # eq:caps
                Kplus = frozenset(z for z in Eminus if p <= z[1]-z[0] < p+w)
                assert Eminus == Kminus | Ohat | Kplus
                assert not (Kminus & Ohat) and not (Kminus & Kplus) and not (Ohat & Kplus)
                assert all(1 <= z[1]-z[0] <= w-1 for z in Kminus)
                assert all(w+1 <= z[1]-z[0] <= p-2 for z in Ohat)
                assert all(p <= z[1]-z[0] <= p+w-2 for z in Kplus)
                assert What == Kminus | translate(Kplus, (-v[0], -v[1]))   # eq:cap-hat
                assert Kminus & translate(Kplus, (-v[0], -v[1])) == interior(W)
                for m in range(1, 5):                                    # eq:erosion-union
                    F = row_union(E, v, m)
                    assert canonical(interior(F)) == canonical(frozenset().union(
                        *(translate(Eminus, (j*v[0], j*v[1])) for j in range(m))))
                    for j in range(m-1):
                        assert translate(E, (j*v[0], j*v[1])) & translate(E, ((j+1)*v[0], (j+1)*v[1])) \
                            == translate(W, ((j+1)*v[0], (j+1)*v[1]))
                counts['positive-width marks'] += 1
    # Necessity of each hypothesis, over every candidate end-copy pair.
    necessity = Counter()
    for n in range(3, NECESSITY_AREA+1):
        for shape in shapes_of_area(n):
            E = canonical(shape)
            N = span(E)
            pool = list(candidates(E, range(1, (N-1)//2+1)))
            for W, v in pool:
                I, II, III, IV = hypotheses(E, W, v, pool)
                failed = [name for name, ok in zip(('I', 'II', 'III', 'IV'), (I, II, III, IV)) if not ok]
                if len(failed) == 0:
                    necessity['legal candidates'] += 1
                    assert conclusion_holds(E, W, v)
                elif len(failed) == 1:
                    necessity['fails only '+failed[0]] += 1
                    necessity['violates after failing only '+failed[0]] += not conclusion_holds(E, W, v)
            wide = list(candidates(E, range((N-1)//2+1, N)))
            for W, v in wide:
                necessity['II fails (w >= p)'] += 1
                necessity['violates after failing II'] += not conclusion_holds(E, W, v)
    print(dict(sorted(necessity.items())))
    for name in ('III', 'IV'):
        assert necessity['violates after failing only '+name] > 0, name
    assert necessity['violates after failing II'] > 0
    assert necessity['legal candidates'] > 0
    print(dict(counts))
    print(dict(sorted(necessity.items())))
    print('check_mark_structure: PASS')


if __name__ == '__main__':
    main()
