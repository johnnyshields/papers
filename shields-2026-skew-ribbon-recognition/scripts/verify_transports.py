r"""Paper section `app:boundary` (Boundary constructions and exceptional entrances), rt:transports;
and `sec:charts` (Marked charts and strict descent), lem:strict-area.

rt:transports.  Antitransposition (i, j) -> (-j, -i) carries a positive ordinary (b) mark to an
ordinary (a) mark and a mixed (c) mark to a mixed (d) mark, with the same coarse outer: for every
connected V, AT(V o_mu J) = V o_{AT mu} AT(J).  Properness, area, period and width are preserved, and
AT(V o_{EMPTY} Col_r) = AT(V) o_{EMPTY} Row_r for the genuine empty mark.  The marks are transported
cell by cell and the transported mark is re-tested by `legal`, so legality is not assumed.

lem:strict-area.  In every proper legal composition P = A o_kappa K both factors have strictly
smaller area than P.

Exhaustive over every connected J of at most CELLS cells, every legal mark of it and every connected
V of at most OUTER cells.
"""
from _gluing_common import (antitranspose, compose, content, empty_mark, is_connected_skew, legal,
                            normalize, span)
from _gluing_common import Mark
from check_two_copy_flags import diagrams, marks

CELLS = 8
OUTER = 5


def at_cells(S):
    return frozenset((-j, -i) for i, j in S)


def at_mark(mk):
    """Cell-by-cell antitransposition of a mark, with the translation that normalizes the inner."""
    raw = at_cells(mk.inner)
    low = min(raw, key=content)
    shift_by = (-low[0], -low[1])
    move = lambda S: frozenset((i + shift_by[0], j + shift_by[1]) for i, j in at_cells(S))
    d = (-mk.displacement[1], -mk.displacement[0])
    case = {'a': 'b', 'b': 'a', 'c': 'd', 'd': 'c'}[mk.case]
    return Mark(move(mk.inner), move(mk.lower), move(mk.upper), case, d)


def main():
    outers = list(diagrams(OUTER))
    transported = proper = 0
    for J in diagrams(CELLS):
        for mk in marks(J):
            if mk.lower:
                image = at_mark(mk)
                assert legal(image), (sorted(J), mk.case)
                assert image.inner == normalize(at_cells(J))
                assert (image.period, image.width) == (mk.period, mk.width)
                assert len(image.inner) == len(J)
                if mk.case in 'bc':
                    assert image.case == {'b': 'a', 'c': 'd'}[mk.case]
            for V in outers:
                P = compose(V, mk)
                assert is_connected_skew(P)
                if len(V) >= 2 and len(J) >= 2:
                    proper += 1
                    assert len(V) < len(P) and len(J) < len(P), (sorted(V), sorted(J))
                if mk.lower:
                    image = at_mark(mk)
                    Q = compose(V, image)
                    assert Q == normalize(at_cells(P)) and len(Q) == len(P), \
                        (sorted(J), mk.case, sorted(V))
                    transported += 1
    # the empty-mark identity: AT(V o_EMPTY Col_r) = AT(V) o_EMPTY Row_r
    empties = 0
    for r in range(2, 7):
        col = frozenset((i, 0) for i in range(r))
        row = frozenset((0, j) for j in range(r))
        for V in outers:
            left = normalize(at_cells(compose(V, empty_mark(col))))
            right = compose(antitranspose(V), empty_mark(row))
            assert left == right, (r, sorted(V))
            empties += 1
    assert transported > 0 and empties > 0 and proper > 0
    print(f'rt:transports: {transported} (V, mark) pairs with AT(V o mu J) = V o AT(mu) AT(J); '
          f'{empties} empty-mark identities; lem:strict-area: {proper} proper compositions with '
          f'both factors strictly smaller')
    print('ALL PASS')


if __name__ == '__main__':
    main()
