r"""Paper section `sec:charts` (Marked charts and strict descent).

Labels: lem:diagonal-reconstruction, eq:intro-span, prop:local-data, prop:gluing-inputs (first
item), ex:gauge, ge:remark:same-mark.

Everything is rebuilt from cell sets with exact integer or `fractions` arithmetic; no floating
point.  Objects are derived from definitions, not from the formulas under test:

* connected skew diagrams are generated as the connected cell sets of \(\lambda/\mu\) over all
  pairs of partitions in a box, never from the diagonal characterization being tested;
* marks come from `_gluing_common.legal`, which tests legality by cell sets, every marked
  displacement and the hats, and composition from adjacency propagation.

Exhaustive over the stated bounds: every connected diagram of at most CELLS cells, every legal
mark of it, and every connected outer of at most OUTER cells.
"""
import itertools

from _gluing_common import (compose, content, intersection_mark, is_connected_skew,
                            legal, normalize, schur, shift, southwest, span)
from check_two_copy_flags import diagrams, marks, phases

CELLS = 9
OUTER = 5
BOX = 4


def partitions_in_box(rows, cols):
    return [p for p in itertools.product(range(cols, -1, -1), repeat=rows)
            if all(p[i] >= p[i + 1] for i in range(rows - 1))]


def skew_cells(lam, mu):
    return frozenset((i, j) for i in range(len(lam)) for j in range(mu[i], lam[i]))


def diagonals(shape):
    d = {}
    for i, j in shape:
        d.setdefault(j - i, []).append(i)
    return {c: (min(v), max(v), len(v)) for c, v in d.items()}


def characterization(shape):
    """The four conditions of lem:diagonal-reconstruction (without connectivity)."""
    d = diagonals(shape)
    contents = sorted(d)
    if contents != list(range(contents[0], contents[-1] + 1)):
        return False
    if any(hi - lo + 1 != n for lo, hi, n in d.values()):
        return False
    lows = [d[c][0] for c in contents]
    highs = [d[c][1] for c in contents]
    if any(b - a not in (0, -1) for a, b in zip(lows, lows[1:])):
        return False
    if any(b - a not in (0, -1) for a, b in zip(highs, highs[1:])):
        return False
    return d[contents[0]][2] == 1 and d[contents[-1]][2] == 1


def check_diagonal_reconstruction():
    shapes = set()
    for lam in partitions_in_box(BOX, BOX):
        for mu in partitions_in_box(BOX, BOX):
            if all(mu[i] <= lam[i] for i in range(BOX)):
                cells = skew_cells(lam, mu)
                if cells and is_connected_skew(cells):
                    shapes.add(normalize(cells))
    # Conversely: every connected skew diagram has the properties.
    assert all(characterization(s) for s in shapes)
    # If: every cell set in a 4 x 4 box with the properties is a connected skew diagram.
    box = [(i, j) for i in range(BOX) for j in range(BOX)]
    found = 0
    for mask in range(1, 1 << len(box)):
        cells = frozenset(c for k, c in enumerate(box) if mask >> k & 1)
        if characterization(cells):
            found += 1
            assert is_connected_skew(cells) and normalize(cells) in shapes, sorted(cells)
    assert found >= len(shapes)
    # Heights with singleton ends and the two binary boundary words determine the diagram.
    seen = {}
    for s in shapes:
        d = diagonals(s)
        contents = sorted(d)
        lows = [d[c][0] for c in contents]
        highs = [d[c][1] for c in contents]
        aword = tuple(a - b for a, b in zip(lows, lows[1:]))
        bword = tuple(a - b for a, b in zip(highs, highs[1:]))
        heights = tuple(d[c][2] for c in contents)
        assert heights[0] == heights[-1] == 1 and min(heights) >= 1
        assert set(aword + bword) <= {0, 1}
        key = (heights, aword, bword)
        assert seen.setdefault(key, s) == s, 'two diagrams with the same data'
        # reconstruct from the data
        rebuilt = set()
        lo = 0
        for c, h in zip(contents, heights):
            rebuilt.update((i, i + c) for i in range(lo, lo + h))
            if c != contents[-1]:
                k = c - contents[0]
                lo -= aword[k]
        assert normalize(frozenset(rebuilt)) == s
    print(f'lem:diagonal-reconstruction: {len(shapes)} diagrams, {found} box subsets with the '
          f'properties, all connected skew; data injective and reconstructing')


def counts_outers():
    return list(diagrams(2, OUTER)) if False else [D for D in diagrams(OUTER) if len(D) >= 2]


def check_span_and_local_data():
    outers = [D for D in diagrams(OUTER)]
    nmarks = positive = mixed = 0
    for E in diagrams(CELLS):
        for mk in marks(E):
            assert legal(mk)
            nmarks += 1
            p, w = mk.period, mk.width
            assert 0 <= w < p and span(E) == p + w                  # eq:intro-span, N_E = p + w
            if w:
                positive += 1
                v = mk.displacement
                # prop:local-data
                assert mk.lower == E & shift(E, (-v[0], -v[1]))      # W_- = E n (E - v)
                diag = diagonals(E)
                base = min(diag)
                for a in (w, p - 1):                                  # private diagonals singletons
                    if w <= a < p:
                        assert diag[base + a][2] == 1, (sorted(E), a)
                s, t = phases(mk)
                O = E - mk.lower - mk.upper
                contents = sorted({content(c) - base for c in O})
                if mk.case in 'cd':
                    mixed += 1
                    assert 1 <= s <= w and 0 <= t < w and t < s, (sorted(E), s, t)
                else:
                    assert 1 <= s <= w and 0 <= t < w, (sorted(E), s, t)
                assert contents == list(range(s, p + t)), (sorted(E), contents, s, t)
                # the middle is thin on the marked diagonals
                for a in list(range(w)) + list(range(p, p + w)):
                    assert sum(1 for c in O if content(c) - base == a) <= 1, (sorted(E), a)
            for D in outers:
                F = compose(D, mk)
                assert is_connected_skew(F)
                m = span(D)
                assert span(F) == p * m + w                         # eq:intro-span, N_F = p N_D + w
                if w and len(E) <= 7:
                    # first and last p diagonals determine the inner
                    base_F = min(content(c) for c in F)
                    first = frozenset(c for c in F if content(c) - base_F < p)
                    last = frozenset(c for c in F if content(c) - base_F >= span(F) - p)
                    base_E = min(content(c) for c in E)
                    assert first == frozenset(c for c in E if content(c) - base_E < p)
                    expect = frozenset(c for c in E if content(c) - base_E >= w)
                    assert normalize(last) == normalize(expect), (sorted(E), sorted(D))
                    if mk.case in 'cd':                              # final copy at (m-1) v
                        v = mk.displacement
                        assert southwest(F) == southwest(E)
                        placed = shift(E, ((m - 1) * v[0], (m - 1) * v[1]))
                        cut = span(F) - p
                        assert last == frozenset(c for c in placed
                                                 if content(c) - base_F >= cut), \
                            (sorted(E), sorted(D))
    assert positive > 0 and mixed > 0
    print(f'eq:intro-span, prop:local-data: {nmarks} legal marks of diagrams up to {CELLS} cells '
          f'({positive} positive width, {mixed} mixed), composed with {len(outers)} outers')


def check_two_marks_at_fixed_width():
    doubles = 0
    for E in diagrams(CELLS):
        by_width = {}
        for mk in marks(E):
            if mk.width:
                by_width.setdefault(mk.width, []).append(mk)
        for w, ms in by_width.items():
            assert len(ms) <= 2, (sorted(E), w)
            if len(ms) == 2:
                doubles += 1
                assert sorted(m.case for m in ms) == ['a', 'b'], (sorted(E), w)
    assert doubles > 0
    print(f'prop:gluing-inputs (fixed inner and width): at most two marks, {doubles} doubles, '
          f'each the two ordinary gauges')


def check_example_gauge():
    raw = frozenset([(0, 2), (0, 3)] + [(1, j) for j in range(4)] + [(2, 0), (2, 1)])
    assert is_connected_skew(raw)
    E = normalize(raw)                      # the paper's coordinates, translated by (2, 0)
    back = lambda S: shift(S, (2, 0))
    ma = intersection_mark(E, (-1, 3))
    mb = intersection_mark(E, (-2, 2))
    assert ma.width == mb.width == 2 and ma.period == mb.period == 4
    assert ma.case == 'a' and mb.case == 'b'
    assert back(ma.lower) == frozenset({(1, 0), (2, 0)})
    assert back(ma.upper) == frozenset({(0, 3), (1, 3)})
    assert back(mb.lower) == frozenset({(2, 0), (2, 1)})
    assert back(mb.upper) == frozenset({(0, 2), (0, 3)})
    assert (ma.displacement[0] - mb.displacement[0], ma.displacement[1] - mb.displacement[1]) \
        == (1, 1)
    both = [m for m in marks(E) if m.width == 2]
    assert len(both) == 2
    row2 = frozenset({(0, 0), (0, 1)})
    col2 = frozenset({(0, 0), (1, 0)})
    A = compose(row2, ma)
    B = compose(col2, mb)
    assert A == B and len(A) == 14
    target = normalize(frozenset((i, j) for i, rowlen, low in
                                 ((0, 7, 5), (1, 7, 2), (2, 5, 0), (3, 2, 0))
                                 for j in range(low, rowlen)))
    assert A == target                                              # (7,7,5,2)/(5,2)
    # outer functions: h_2 = Row_2 and e_2 = Col_2 are different polynomials
    assert schur(row2) != schur(col2)
    print('ex:gauge: both marks legal, displacements differ by (1,1), composites equal '
          '(7,7,5,2)/(5,2) of area 14')


def check_same_mark_outer_equality():
    outers = [D for D in diagrams(OUTER) if span(D) >= 2]
    groups = checked = 0
    for E in diagrams(6):
        for mk in marks(E):
            by_function = {}
            for D in outers:
                F = compose(D, mk)
                by_function.setdefault(schur(F), []).append(D)
            for Ds in by_function.values():
                groups += 1
                for D in Ds:
                    for D2 in Ds:
                        assert schur(D) == schur(D2), (sorted(E), sorted(D), sorted(D2))
                        checked += 1
    print(f'ge:remark:same-mark: {groups} Schur-equal groups of compositions through one mark, '
          f'{checked} outer pairs, all with equal outer functions')


def main():
    check_diagonal_reconstruction()
    check_span_and_local_data()
    check_two_marks_at_fixed_width()
    check_example_gauge()
    check_same_mark_outer_equality()
    print('ALL PASS')


if __name__ == '__main__':
    main()
