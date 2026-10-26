#!/usr/bin/env python3
"""Check horizontal end-row charts against literal cell and edge placements.

The source convention for an empty overlap is implemented with corner edges,
not inferred from a composition engine.  Infinite-chain membership is exact:
row bounds leave at most two candidate translates for any queried cell.
Controls reject extending the same marks to the terminal threshold, replacing
an overlap of t cells by t+1 cells, and changing the north-step displacement.
The I and IV certificates are the stronger singleton-diagonal and empty-barred-
overlap assertions used in the proof; this is not a general legality oracle.
All bounded checks concern geometry, not arbitrary-mate class exhaustion.
"""
from collections import deque
from itertools import product


def shift(cells, vec):
    return frozenset((i + vec[0], j + vec[1]) for i, j in cells)


def norm(cells):
    if not cells:
        return frozenset()
    return shift(cells, (-min(i for i, _ in cells), -min(j for _, j in cells)))


def cells_of_profile(rows, gaps):
    assert rows and len(gaps) == len(rows) - 1
    assert all(r > 0 for r in rows)
    assert all(0 <= g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps))
    left = [0] * len(rows)
    for i in range(len(rows) - 2, -1, -1):
        left[i] = left[i + 1] + rows[i + 1] - gaps[i] - 1
    return frozenset((i, j) for i, r in enumerate(rows) for j in range(left[i], left[i] + r))


def row_intervals(cells):
    if not cells:
        return []
    grouped = {}
    for i, j in cells:
        grouped.setdefault(i, set()).add(j)
    if sorted(grouped) != list(range(min(grouped), max(grouped) + 1)):
        return None
    intervals = []
    for i in sorted(grouped):
        cols = grouped[i]
        lo, hi = min(cols), max(cols)
        if len(cols) != hi - lo + 1:
            return None
        intervals.append((lo, hi))
    return intervals


def connected_skew(cells):
    intervals = row_intervals(cells)
    if not intervals:
        return False
    for (left, right), (next_left, next_right) in zip(intervals, intervals[1:]):
        if left < next_left or right < next_right or left > next_right:
            return False
    return True


def profile_of_cells(cells):
    assert connected_skew(cells)
    intervals = row_intervals(cells)
    rows = tuple(b - a + 1 for a, b in intervals)
    gaps = tuple(min(b, d) - max(a, c) for (a, b), (c, d) in zip(intervals, intervals[1:]))
    return rows, gaps


def near(left, right):
    r, g = left
    s, h = right
    return r[:-1] + (r[-1] + s[0],) + s[1:], g + h


def composite_profile(alpha, profile, t=0):
    r_out, g_out = (), ()
    for part in alpha:
        block = profile
        for _ in range(part - 1):
            block = near(block, profile)
        r, g = block
        if r_out:
            g_out += (0,)
        r_out += r
        g_out += g
    return tuple(r + t for r in r_out), tuple(g + t for g in g_out)


def compositions(size):
    if size == 0:
        yield ()
    else:
        for first in range(1, size + 1):
            for rest in compositions(size - first):
                yield (first,) + rest


def end_marks(inner, width):
    intervals = row_intervals(inner)
    assert connected_skew(inner)
    n = len(intervals)
    bottom_left = intervals[-1][0]
    top_right = intervals[0][1]
    sw = frozenset((n - 1, j) for j in range(bottom_left, bottom_left + width))
    ne = frozenset((0, j) for j in range(top_right - width + 1, top_right + 1))
    # At width zero, these are edge anchors: west edge at bottom_left and
    # east edge at top_right+1, rather than two missing cell coordinates.
    delta = (1 - n, top_right - width + 1 - bottom_left)
    return sw, ne, delta


def in_infinite_chain(cell, inner, delta):
    i, j = cell
    n = len(row_intervals(inner))
    d = n - 1
    assert d > 0 and delta[0] == -d
    low = -(i // d)  # ceil(-i/d), using exact integer division
    high = (d - i) // d
    return any((i - k * delta[0], j - k * delta[1]) in inner for k in range(low, high + 1))


def literal_hypotheses(inner, width):
    """Sufficient literal certificates, including stronger witnesses for I/IV."""
    sw, ne, delta = end_marks(inner, width)
    if width == 0:
        # Empty mark source convention: no occupied diagonals, unchanged
        # connected complement, and an empty barred overlap.
        return dict(I=True, II=bool(inner), III=connected_skew(inner), IV=True,
                    V=None, case_a=True), (sw, ne, delta)
    assert sw <= inner and ne <= inner
    diag = lambda shape: {j - i for i, j in shape}
    ds, dn = diag(sw), diag(ne)
    singleton_diagonals = all({p for p in inner if p[1] - p[0] in diag(mark)} == mark
                              for mark in (sw, ne))
    complement_ok = all(connected_skew(inner - mark) for mark in (sw, ne))
    middle = inner - sw - ne
    adjacent = lambda mark: {p for p in mark if any((p[0] + a, p[1] + b) in middle
                                                for a, b in ((1, 0), (-1, 0), (0, 1), (0, -1)))}
    barred = set()
    for i, j in sw:
        if in_infinite_chain((i - 1, j - 1), inner, delta):
            barred.add((i - 1, j - 1))
        if in_infinite_chain((i + 1, j + 1), inner, delta):
            barred.add((i, j))
    # Empty barred W is stronger than IV; it is the advertised proof here.
    horizontal = ((max(sw)[0], max(j for _, j in sw) + 1) in middle
                  and (0, min(j for _, j in ne) - 1) in middle)
    return dict(I=singleton_diagonals, II=min(dn) > max(ds) + 1,
                III=complement_ok, IV=not barred,
                V=all(len(adjacent(mark)) == 1 for mark in (sw, ne)),
                case_a=horizontal), (sw, ne, delta)


def source_ribbon_chart(alpha, inner, width, north_error=0):
    """Place copies using the published east/north adjacency rules."""
    sw, ne, delta = end_marks(inner, width)
    if not alpha:
        return norm(sw)  # Source empty-outer convention, not an empty union.
    outer = cells_of_profile(alpha, (0,) * (len(alpha) - 1))
    anchor = (max(i for i, _ in outer), min(j for i, j in outer if i == max(r for r, _ in outer)))
    offsets = {anchor: (0, 0)}
    queue = deque([anchor])
    east = delta
    north = (delta[0] - 1, delta[1] - 1 + north_error)
    directions = (((0, 1), east), ((-1, 0), north),
                  ((0, -1), (-east[0], -east[1])), ((1, 0), (-north[0], -north[1])))
    while queue:
        i, j = queue.popleft()
        offset = offsets[(i, j)]
        for (di, dj), (dr, dc) in directions:
            other = (i + di, j + dj)
            if other not in outer:
                continue
            new = (offset[0] + dr, offset[1] + dc)
            if other in offsets:
                assert offsets[other] == new
            else:
                offsets[other] = new
                queue.append(other)
    assert offsets.keys() == outer
    union = set()
    for offset in offsets.values():
        union.update(shift(inner, offset))
    return norm(union)


def parameter_box():
    for n in range(2, 5):
        for gaps in product((1, 2), repeat=n - 1):
            for u, v in product(range(1, 5), repeat=2):
                for excess in product((1, 2, 3), repeat=n - 2):
                    rows = ((gaps[0] + u,) + tuple(gaps[i] + gaps[i + 1] + excess[i]
                                                         for i in range(n - 2))
                            + (gaps[-1] + v,))
                    yield rows, gaps


def main():
    counts = dict(inners=0, marked=0, edge_marked=0, cell_identities=0, wall_controls=0)
    outers = [alpha for m in range(1, 6) for alpha in compositions(m)]
    for rows, gaps in parameter_box():
        n = len(rows)
        assert all(0 < g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps))
        assert all(rows[i] > gaps[i - 1] + gaps[i] for i in range(1, n - 1))
        p = min(rows[0] - gaps[0], rows[-1] - gaps[-1])
        counts['inners'] += 1
        span = sum(rows) - sum(gaps)
        for t in range(p):
            inner = cells_of_profile(tuple(r + t for r in rows), tuple(g + t for g in gaps))
            hyps, marks = literal_hypotheses(inner, t)
            assert all(value for name, value in hyps.items() if name != 'V' or t > 0), (rows, gaps, t, hyps)
            assert marks[2] == (1 - n, span - n + 1)
            counts['marked' if t else 'edge_marked'] += 1
            # Empty outer has the stated source value, independently of any engine.
            assert len(source_ribbon_chart((), inner, t)) == t
            for alpha in outers:
                chart = source_ribbon_chart(alpha, inner, t)
                expected = cells_of_profile(*composite_profile(alpha, (rows, gaps), t))
                assert chart == expected, (rows, gaps, t, alpha)
                counts['cell_identities'] += 1
        # Same family, same literal mark prescription: the strict threshold
        # cannot be relaxed, since a connected-skew complement fails.
        wall = cells_of_profile(tuple(r + p for r in rows), tuple(g + p for g in gaps))
        hyps, _ = literal_hypotheses(wall, p)
        assert not hyps['III'], (rows, gaps, p)
        counts['wall_controls'] += 1

    # The geometric lemma permits zero gaps and inners that are already
    # non-Hessenberg before inflation, not only internally activated images.
    general_checks = 0
    general_profiles = (((11, 6, 8), (4, 4)),
                        ((3, 4, 3, 4), (1, 0, 1)),
                        ((2, 1, 3), (0, 0)),
                        ((3, 3, 3), (2, 2)))
    assert general_profiles[0][0][1] < sum(general_profiles[0][1])
    for rows, gaps in general_profiles:
        p = min(rows[0] - gaps[0], rows[-1] - gaps[-1])
        for t in range(p):
            inner = cells_of_profile(tuple(r + t for r in rows), tuple(g + t for g in gaps))
            hyps, _ = literal_hypotheses(inner, t)
            assert all(value for name, value in hyps.items() if name != 'V' or t > 0)
            for alpha in outers:
                assert source_ribbon_chart(alpha, inner, t) == cells_of_profile(*composite_profile(alpha, (rows, gaps), t))
                general_checks += 1

    # Internally activated indices do not defeat the endpoint proof.
    rows, gaps, t = (6, 3, 6), (1, 1), 3
    assert rows[1] - gaps[0] - gaps[1] == 1 < t < min(rows[0] - gaps[0], rows[-1] - gaps[-1])
    inner = cells_of_profile(tuple(r + t for r in rows), tuple(g + t for g in gaps))
    hyps, _ = literal_hypotheses(inner, t)
    assert all(hyps.values())
    assert (gaps[0] + t) + (gaps[1] + t) - (rows[1] + t) > 0
    assert source_ribbon_chart((1, 2), inner, t) == cells_of_profile(*composite_profile((1, 2), (rows, gaps), t))

    # A same-family boundary control makes the claimed empty barred overlap
    # false.  The southeast neighbor is also exhibited in one actual copy,
    # so a broken infinite-membership routine cannot pass by always saying no.
    control = cells_of_profile((6, 7), (4,))  # I_3(3,4;1), beyond p=2.
    hyps, (_, _, delta) = literal_hypotheses(control, 3)
    neighbor = (2, 1)
    assert neighbor in shift(control, (-delta[0], -delta[1]))
    assert in_infinite_chain(neighbor, control, delta)
    assert not hyps['IV']  # Here IV denotes our stronger empty-barred-W certificate.

    # These mutations test the literal identity itself, on the advertised family.
    alpha = (1, 2)
    expected = cells_of_profile(*composite_profile(alpha, (rows, gaps), t))
    assert source_ribbon_chart(alpha, inner, t + 1) != expected
    assert source_ribbon_chart(alpha, inner, t, north_error=1) != expected

    # Unbounded-height source family: finite instances supplement the proof.
    tall = 0
    for exponent in range(1, 7):
        rows = (3,) + (4, 3, 6) * exponent + (5, 4)
        gaps = (1,) * (len(rows) - 1)
        for t in (0, 1):
            inner = cells_of_profile(tuple(r + t for r in rows), tuple(g + t for g in gaps))
            hyps, _ = literal_hypotheses(inner, t)
            assert all(value for name, value in hyps.items() if name != 'V' or t > 0)
            for alpha in ((1, 2), (2, 1), (1, 2, 1, 3, 2), (1, 3, 2, 1, 2)):
                assert source_ribbon_chart(alpha, inner, t) == cells_of_profile(*composite_profile(alpha, (rows, gaps), t))
                tall += 1
    print('bounded literal checks:', counts)
    print('non-Hessenberg and zero-gap inner cell identities:', general_checks)
    print('internally activated non-Hessenberg inflated inner: legal I--V, literal identity PASS')
    print('controls: threshold extension rejects III; overlap-width and north-displacement mutations reject the literal identity')
    print('empty-barred-overlap control: a literal southeast neighbor in a translated copy is detected')
    print('unbounded-height family finite cell identities:', tall)
    print('ALL PASS')


if __name__ == '__main__':
    main()
