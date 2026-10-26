r"""Paper section `sec:gluing` (Local common-factor gluing).

Exact bounded controls for ge:decoder, ge:cell-criterion, ge:ordinary-fold,
ge:empty-fold, ge:mixed-fold and the actual-inner restrictions in
prop:gluing-ordinary-fold, prop:gluing-mixed-fold and lem:gluing-small.
Only integer arithmetic is used.  Full flags are derived from row endpoints;
word inversion is compared with the separate literal cell composition and
I--IV mark search in check_gcd_fold_sweep.py.  Native signatures generate
candidate supplied inners, not a preselected divisor root.  The punctured-word
sweep also calls check_native_restriction on its actual two-root parents.
These finite checks do not prove the uniform theorems.
"""
from collections import Counter
from itertools import product
from math import gcd

from check_gcd_fold_sweep import (
    Mark, at, at_mark, cells, compose, diag, endpoints, marks, marks_at,
    norm, phases, root_inner, shapes, shift, skew, span,
)


def full_flags(board):
    """Read beta sets directly from rows, independently of diagonal bits."""
    rows = sorted({i for i, _ in board})
    left = {i: min(j for k, j in board if k == i) for i in rows}
    right = {i: max(j for k, j in board if k == i) for i in rows}
    base = left[rows[-1]] - rows[-1]
    x = {right[i] + 1 - i - base for i in rows}
    y = {left[i] - i - base for i in rows}
    assert len(x) == len(y) == len(rows)
    assert max(x) == span(board) and min(y) == 0
    return x, y


def word_cells(x, y, n):
    """Build the actual diagonal intervals, rejecting nonclosed/nonpositive words."""
    if not (x <= set(range(1, n + 1)) and y <= set(range(n))):
        return None
    if n not in x or 0 not in y or len(x) != len(y):
        return None
    lo = hi = 0
    board = {(0, 0)}
    for k in range(1, n):
        lo -= k in y
        hi -= k in x
        if hi < lo:
            return None
        board.update((i, i + k) for i in range(lo, hi + 1))
    if lo != hi:
        return None
    board = norm(board)
    return board if skew(board) else None


def heights(board):
    start = min(j - i for i, j in board)
    count = Counter(j - i - start for i, j in board)
    return [count[k] for k in range(span(board))]


def slots(mark):
    t, s = phases(mark)
    if not mark.w:
        return ((0, 0), (1, 0))
    return {
        'a': ((0, s), (1, t)), 'b': ((0, t), (1, s)),
        'c': ((0, s), (0, t)), 'd': ((1, t), (1, s)),
    }[mark.case]


def decode(parent, mark):
    """ge:decoder: test BOTH labeled native words, then invert the ports."""
    if mark not in marks_at(mark.E, mark.p) or mark.p < 2:
        return None
    n = span(parent)
    m, a = divmod(n, mark.p)
    if m < 1 or a != mark.w:
        return None
    words, native = full_flags(parent), full_flags(mark.E)
    ports = slots(mark)
    for label in (0, 1):
        for k in range(n + 1):
            if any(label == side and k >= phase and
                   (k - phase) % mark.p == 0 and
                   (k - phase) // mark.p <= m for side, phase in ports):
                continue
            if (k in words[label]) != (k % mark.p in native[label]):
                return None
    t, s = phases(mark)
    x, y = set(), set()
    for j in range(m + 1):
        if not mark.w or mark.case == 'a':
            bx, by = j * mark.p + s in words[0], j * mark.p + t in words[1]
        elif mark.case == 'b':
            bx, by = j * mark.p + s not in words[1], j * mark.p + t not in words[0]
        elif mark.case == 'c':
            bx, by = j * mark.p + s in words[0], j * mark.p + t not in words[0]
        else:
            bx, by = j * mark.p + s not in words[1], j * mark.p + t in words[1]
        if bx:
            x.add(j)
        if by:
            y.add(j)
    return word_cells(x, y, m)


def check_chart(parent, outer, mark):
    assert compose(outer, mark) == parent
    assert full_flags(word_cells(*full_flags(parent), span(parent))) == full_flags(parent)
    h, coarse = heights(parent), heights(outer)
    assert coarse == [h[j * mark.p + mark.w] for j in range(span(outer))]
    assert coarse == [h[(j + 1) * mark.p - 1] for j in range(span(outer))]
    if span(outer) == 1:
        assert outer == cells((1,)) and parent == mark.E
    else:
        assert 1 < len(outer) < len(parent) and 1 < len(mark.E) < len(parent)
    sw, _ = endpoints(parent)
    first = norm({z for z in parent if z[1] - z[0] - (sw[1] - sw[0]) < mark.p})
    last = norm({z for z in parent if z[1] - z[0] - (sw[1] - sw[0]) >= span(parent) - mark.p})
    esw, _ = endpoints(mark.E)
    efirst = norm({z for z in mark.E if z[1] - z[0] - (esw[1] - esw[0]) < mark.p})
    elast = norm({z for z in mark.E if z[1] - z[0] - (esw[1] - esw[0]) >= mark.w})
    assert first == efirst and last == elast


def check_ordinary_criterion(mark):
    """ge:cell-criterion, including its two endpoint bits and literal intervals."""
    if mark.case == 'b':
        mark = at_mark(mark)
    assert mark.w and mark.case == 'a'
    intervals = diag(mark.E)
    a, g = mark.w, mark.p
    tau, sigma = phases(mark)
    aa = [None] + [left[0] - right[0] for left, right in zip(intervals, intervals[1:])]
    bb = [None] + [left[1] - right[1] for left, right in zip(intervals, intervals[1:])]
    h = [hi - lo + 1 for lo, hi in intervals]
    assert 0 <= tau < a and 1 <= sigma <= a
    for c in range(1, a):
        assert aa[g + c] == aa[c] - (c == tau)
        assert bb[g + c] == bb[c] + (c == sigma)
    assert h[g] == 1 + (tau > 0) and h[a] == h[g - 1] == 1
    assert all(h[c] - (c >= sigma) >= 1 for c in range(a))
    assert sigma != a or bb[a] == 0
    assert tau != 0 or aa[g] == 0
    low = frozenset((i, i + c) for c in range(a)
                    for i in range(intervals[c][0], intervals[c][1] - (c >= sigma) + 1))
    high = frozenset((i, i + g + c) for c in range(a)
                     for i in range(intervals[g + c][0] + (c < tau), intervals[g + c][1] + 1))
    sw, _ = endpoints(mark.E)
    actual = shift(mark.W, (-sw[0], -sw[1]))
    assert low == actual and high == shift(actual, mark.v)
    assert mark in marks_at(mark.E, g)  # All displacements, complements and both hatted clauses.


def native_sets(mark):
    assert mark.w and mark.case in ('a', 'd')
    x, y = full_flags(mark.E)
    wx, wy = full_flags(norm(mark.W))
    t, s = phases(mark)
    private_x = {k for k in x if mark.w < k < mark.p}
    private_y = {k for k in y if mark.w < k < mark.p}
    assert len(private_x) == len(private_y)
    b = wx | private_x
    c = wy | private_y if mark.case == 'a' else (wy - {t}) | {s} | private_y
    assert len(b) == len(c)
    if mark.case == 'a':
        assert s in wx
        assert b == {k for k in x if k < mark.p} | {s}
        assert c == {k for k in y if k < mark.p} and t in c
    else:
        assert b == {k for k in x if k < mark.p}
        assert c == {k for k in y if k < mark.p} - {t}
        assert t not in c and s in c
    assert 0 not in b and mark.w in b
    return b, c


def full_classes(values, period, divisor, holes=()):
    return all(z in holes or len({k in values for k in range(z, period, divisor)}) == 1
               for z in range(divisor))


def empty_completion(mark, divisor):
    x, y = full_flags(mark.E)
    proper = range(divisor, mark.p, divisor)
    row = {k in x for k in proper}
    col = {k in y for k in proper}
    if len(row) != 1 or row != col:
        return None
    value = next(iter(row))
    b, c = x - {mark.p}, y - {0}
    if value:
        b.add(0)
        c.add(0)
    if not full_classes(b, mark.p, divisor) or not full_classes(c, mark.p, divisor):
        return None
    return int(value)


def check_fold(mark, divisor):
    """Search the root's physical mark only AFTER earning its native contract."""
    assert 2 <= divisor < mark.p and mark.p % divisor == 0
    t, s = phases(mark)
    a = mark.w % divisor
    if not mark.w:
        value = empty_completion(mark, divisor)
        assert value is not None
        wanted_case, wanted_phases = 'a', (0, 0)
    else:
        b, c = native_sets(mark)
        if mark.case == 'a':
            assert full_classes(b, mark.p, divisor, {s % divisor})
            assert full_classes(c, mark.p, divisor, {t % divisor})
            assert any(k in b for k in range(s % divisor, mark.p, divisor))
            assert any(k in c for k in range(t % divisor, mark.p, divisor))
            tau, sigma = t % divisor, s % divisor
            wanted_case = 'a' if not a or mark.w < divisor or tau <= sigma else 'b'
            wanted_phases = (tau, sigma) if wanted_case == 'a' else (sigma, tau)
        else:
            assert full_classes(b, mark.p, divisor)
            assert full_classes(c, mark.p, divisor, {t % divisor, s % divisor})
            assert a and t % divisor != s % divisor
            exceptional = sum(k in c for k in range(mark.p)
                              if k % divisor in {t % divisor, s % divisor})
            assert exceptional == mark.p // divisor
            wanted_case = 'd'
            wanted_phases = tuple(sorted((t % divisor, s % divisor)))
    inner = root_inner(mark.E, divisor)
    assert inner is not None
    candidates = [m for m in marks_at(inner, divisor) if m.case == wanted_case and
                  (not a or phases(m) == wanted_phases)]
    assert len(candidates) == 1, (mark, divisor, candidates)
    root = candidates[0]
    outer = decode(mark.E, root)
    assert outer is not None, (mark, divisor, root)
    check_chart(mark.E, outer, root)
    if root.w and root.case in 'ab':
        check_ordinary_criterion(root)
    if not mark.w:
        assert outer == (cells((mark.p // divisor,)) if value == 0 else
                         cells((1,) * (mark.p // divisor)))
    return outer, root


def check_native_restriction(parent, first, second):
    """Actual-inner restrictions for the ordinary and mixed two-root propositions."""
    if first.case in 'bc' and first.w:
        parent, first = at(parent), at_mark(first)
        second = at_mark(second) if second.w else marks_at(at(second.E), second.p)[0]
    divisor = gcd(first.p, second.p)
    assert divisor > 1 and first.p % second.p and second.p % first.p
    assert decode(parent, first) is not None and decode(parent, second) is not None
    if not first.w:
        x, y = full_flags(first.E)
        row = {k in x for k in range(divisor, first.p, divisor)}
        col = {k in y for k in range(divisor, first.p, divisor)}
        assert len(row) == len(col) == 1
        lx, ly = int(next(iter(row))), int(next(iter(col)))
        delta = sum((k in y) - (k in x) for k in range(1, divisor))
        repetitions = first.p // divisor
        assert repetitions * delta + (repetitions - 1) * (ly - lx) == 0
        assert lx == ly and delta == 0
    lower_outer, root = check_fold(first, divisor)
    coarse = decode(parent, first)
    lifted = decode(parent, root)
    assert lifted is not None
    check_chart(parent, lifted, root)
    # Search the actual descended mark, including the empty-edge outer gauge.
    probes = (coarse, cells((2,)), cells((1, 1)), cells((2, 1)), cells((2, 2)))
    choices = []
    for descended in marks_at(lower_outer, first.p // divisor):
        for transport in (lambda d: d, at) if not descended.w else (lambda d: d,):
            if all(compose(compose(transport(d), descended), root) == compose(d, first)
                   for d in probes):
                choices.append(descended)
    assert choices, (first, second, divisor)


def residue_sets(period, divisor, holes):
    classes = [tuple(range(z, period, divisor)) for z in range(divisor)]
    choices = [tuple(frozenset(k for k, bit in zip(cl, bits) if bit)
                     for bits in product((0, 1), repeat=len(cl)))
               if z in holes else (frozenset(), frozenset(cl))
               for z, cl in enumerate(classes)]
    for selected in product(*choices):
        yield frozenset().union(*selected)


def native_candidates(period, divisor, width, case):
    for t in range(width):
        for s in range(1, width + 1):
            if case == 'd' and t >= s:
                continue
            bs = residue_sets(period, divisor, {s % divisor} if case == 'a' else set())
            cs = tuple(residue_sets(period, divisor, {t % divisor} if case == 'a'
                                    else {t % divisor, s % divisor}))
            for b in bs:
                if 0 in b or width not in b or (case == 'a' and s not in b):
                    continue
                for c in cs:
                    if len(b) != len(c):
                        continue
                    if case == 'a' and (0 not in c or width in c or t not in c):
                        continue
                    if case == 'd' and (t in c or s not in c):
                        continue
                    wx = {k for k in b if k <= width}
                    wy = {k for k in c if k <= width}
                    if case == 'd':
                        wy = (wy - {s}) | {t}
                    w = word_cells(wx, wy, width)
                    if w is None:
                        continue
                    bx, cy = {k for k in b if k > width}, {k for k in c if k > width}
                    x = {period + k for k in wx} | bx | (wx - {s} if case == 'a' else wx)
                    y = {period + k for k in wy - {t}} | cy | (wy if case == 'a' else wy | {s})
                    inner = word_cells(x, y, period + width)
                    if inner is None:
                        continue
                    for mark in marks_at(inner, period):
                        if mark.case == case and phases(mark) == (t, s) and norm(mark.W) == w:
                            assert native_sets(mark) == (b, c)
                            yield mark


def decoder_controls():
    counts = Counter()
    templates = [m for area in range(2, 7) for board in shapes(area)
                 for m in marks(board) if m.p >= 2]
    for mark in templates:
        if mark.w and mark.case in 'ab':
            check_ordinary_criterion(mark)
        native = full_flags(mark.E)
        for m in (1, 2, 3):
            n = m * mark.p + mark.w
            variable = sorted({(label, j * mark.p + phase)
                               for label, phase in slots(mark) for j in range(m + 1)})
            base = [{k for k in range(n + 1) if k % mark.p in word}
                    for word in native]
            for assignment in product((0, 1), repeat=len(variable)):
                words = [set(base[0]), set(base[1])]
                for (label, k), bit in zip(variable, assignment):
                    words[label].add(k) if bit else words[label].discard(k)
                parent = word_cells(*words, n)
                if parent is None:
                    continue
                outer = decode(parent, mark)
                assert outer is not None
                check_chart(parent, outer, mark)
                counts[(mark.case if mark.w else 'empty', m)] += 1
    for kind in ('a', 'b', 'c', 'd', 'empty'):
        assert all(counts[kind, m] for m in (1, 2, 3)), (kind, counts)

    row_inner = cells((2,))
    edge = marks_at(row_inner, 2)[0]
    wrong_native = cells((1, 1))
    assert heights(row_inner) == heights(wrong_native)
    assert decode(wrong_native, edge) is None  # Heights cannot replace both words.
    hook = cells((2, 1))
    mixed = next(m for m in marks_at(hook, 2) if m.case == 'd')
    bad = Mark(mixed.E, mixed.W, mixed.v, 'a')
    assert bad not in marks_at(bad.E, bad.p) and decode(hook, bad) is None
    # A genuine empty divisor chart can fail the COMMON-filled-return contract.
    partial = compose(hook, edge)
    partial_mark = marks_at(partial, span(partial))[0]
    assert empty_completion(partial_mark, 2) is None
    assert decode(partial, edge) == hook
    gauge_inner = cells((4, 4, 2), (2,))
    ma = next(m for m in marks_at(gauge_inner, 4) if m.case == 'a')
    mb = next(m for m in marks_at(gauge_inner, 4) if m.case == 'b')
    assert slots(ma)[0][1] == slots(ma)[1][1]
    assert slots(ma)[0][0] != slots(ma)[1][0]  # Equal residues are two labeled slots.
    parent = compose(cells((2,)), ma)
    assert decode(parent, ma) == cells((2,)) and decode(parent, mb) == cells((1, 1))
    # The supplemented composition is checked against a copy-only cell union.
    supplemented = 0
    for mark in templates:
        if mark.case not in 'cd':
            continue
        outer = cells((1, 1))
        sw, _ = endpoints(outer)
        outer0 = shift(outer, (-sw[0], -sw[1]))
        intervals = diag(outer0)
        raw = set()
        for i, j in outer0:
            lo, hi = intervals[j - i]
            rank = i - lo if mark.case == 'c' else i - hi
            raw.update(shift(mark.E, ((j - i) * mark.v[0] + rank,
                                     (j - i) * mark.v[1] + rank)))
        parent = compose(outer, mark)
        check_chart(parent, decode(parent, mark), mark)
        supplemented += norm(raw) != parent
    assert supplemented
    print('decoder connected-word counts', dict(counts), 'essential supplements', supplemented)


def fold_controls():
    counts = Counter()
    seen = set()
    boxes = [(4, 2, v) for v in (1, 2, 3)] + [(6, 3, v) for v in range(1, 6)]
    for period, divisor, width in boxes:
        for case in ('a', 'd'):
            for mark in native_candidates(period, divisor, width, case):
                key = mark, divisor
                if key in seen:
                    continue
                seen.add(key)
                outer, root = check_fold(mark, divisor)
                counts[case, width % divisor, width < divisor] += 1
                if case == 'd':
                    t, s = phases(mark)
                    counts['mixed order', t % divisor < s % divisor] += 1
                else:
                    counts['ordinary gauge', root.case] += 1
                counts['lower contact', phases(mark)[0] == 0] += 1
                counts['upper contact', phases(mark)[1] == width] += 1
                # No original parent is planted here; these are one-inner folds.
                assert span(outer) == (period + width) // divisor
    for case in ('a', 'd'):
        assert any(k[0] == case and k[-1] is True for k in counts)
        assert any(k[0] == case and k[-1] is False for k in counts)
    assert all(any(k[:2] == ('a', rem) for k in counts) for rem in (0, 1, 2))
    assert counts['mixed order', True] and counts['mixed order', False]
    assert counts['ordinary gauge', 'a'] and counts['ordinary gauge', 'b']
    # Empty inputs are enumerated as actual diagrams, not imposed periodic words.
    empty = Counter()
    for area in range(4, 9):
        for board in shapes(area):
            mark = marks_at(board, span(board))[0]
            for divisor in range(2, mark.p):
                if mark.p % divisor:
                    continue
                value = empty_completion(mark, divisor)
                if value is not None:
                    check_fold(mark, divisor)
                    empty[value] += 1
    assert empty[0] and empty[1]
    print('native fold counts', dict(counts), 'empty common-fill counts', dict(empty))


def main():
    decoder_controls()
    fold_controls()
    print('ALL PASS')


if __name__ == '__main__':
    main()
