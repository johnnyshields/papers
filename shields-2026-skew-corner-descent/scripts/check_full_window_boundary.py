#!/usr/bin/env python3
"""The full-window boundary v = b-1 forces a literal b-copy empty root.

Paper section `sec:one-active` (The full-window boundary); target
`lem:boundary-full-window`.

Every connected skew diagram U of area at most MAX_AREA with span q = b*delta is tested
for b >= 2, delta >= 1.  U has literal complete windows of width (b-1)*delta when its
first and last (b-1)*delta content bands are translates of one another; the inherited
private cuts require singleton diagonals at delta-1, delta and at (b-1)*delta-1,
(b-1)*delta, and the two joining edges to have the same direction (horizontal or
vertical).  Every such U is checked to be the empty row or column composition
of b translates of its first delta-band: bands translate by one common displacement
whose empty join is horizontal or vertical, and the band is connected skew with
singleton end diagonals.  Control: the same test at width (b-2)*delta (v = b-2, b >= 3) produces diagrams
with equal literal windows and matching cuts that are not b-copy roots, so the
conclusion is specific to the boundary v = b-1.
"""
from collections import Counter
from diagram_tools import canonical, connected_skew, shapes_of_area, span, translate

MAX_AREA = 13


def band(U, lo, hi):
    return frozenset(z for z in U if lo <= z[1]-z[0] < hi)


def translate_between(X, Y):
    """The translation carrying X onto Y, or None."""
    if len(X) != len(Y) or not X:
        return None
    x, y = min(X), min(Y)
    d = (y[0]-x[0], y[1]-x[1])
    return d if translate(X, d) == Y else None


def diag_size(U, k):
    return sum(1 for z in U if z[1]-z[0] == k)


def edge_direction(U, delta, k):
    """Joining edge at content boundary k*delta: 'H', 'V' or None."""
    below = [z for z in U if z[1]-z[0] == k*delta-1]
    above = [z for z in U if z[1]-z[0] == k*delta]
    if len(below) != 1 or len(above) != 1:
        return None
    (i, j), (a, b) = below[0], above[0]
    if (a, b) == (i, j+1):
        return 'H'
    if (a, b) == (i-1, j):
        return 'V'
    return None


def is_root(U, b, delta):
    lo = min(z[1]-z[0] for z in U)
    bands = [band(U, lo+i*delta, lo+(i+1)*delta) for i in range(b)]
    if not all(connected_skew(X) and diag_size(X, lo+i*delta) == 1
               and diag_size(X, lo+(i+1)*delta-1) == 1 for i, X in enumerate(bands)):
        return False
    steps = [translate_between(bands[0], X) for X in bands]
    if any(s is None for s in steps):
        return False
    diffs = {(steps[i+1][0]-steps[i][0], steps[i+1][1]-steps[i][1]) for i in range(b-1)}
    if len(diffs) != 1:
        return False
    # the common displacement is the content-delta displacement of an empty H or V join
    first = bands[0]
    ne = max(first, key=lambda z: z[1]-z[0])
    sw = min(first, key=lambda z: z[1]-z[0])
    h = (ne[0]-sw[0], ne[1]+1-sw[1])
    v = (ne[0]-1-sw[0], ne[1]-sw[1])
    return next(iter(diffs)) in (h, v)


def main():
    counts = Counter()
    seen = set()
    for n in range(2, MAX_AREA+1):
        for shape in shapes_of_area(n):
            U = canonical(shape)
            if U in seen:
                continue
            seen.add(U)
            N = span(U)
            lo = min(z[1]-z[0] for z in U)
            for b in range(2, N+1):
                if N % b:
                    continue
                delta = N//b
                q, w = N, (b-1)*delta
                first, last = band(U, lo, lo+w), band(U, lo+q-w, lo+q)
                windows = (connected_skew(first) and connected_skew(last)
                           and translate_between(first, last) is not None)
                # the first and last private cuts sit at content lo+delta and lo+(b-1)*delta
                d_first = None
                d_last = None
                below = [z for z in U if z[1]-z[0] == lo+delta-1]
                above = [z for z in U if z[1]-z[0] == lo+delta]
                if len(below) == 1 and len(above) == 1:
                    (i, j), (a, c) = below[0], above[0]
                    d_first = 'H' if (a, c) == (i, j+1) else 'V' if (a, c) == (i-1, j) else None
                below = [z for z in U if z[1]-z[0] == lo+(b-1)*delta-1]
                above = [z for z in U if z[1]-z[0] == lo+(b-1)*delta]
                if len(below) == 1 and len(above) == 1:
                    (i, j), (a, c) = below[0], above[0]
                    d_last = 'H' if (a, c) == (i, j+1) else 'V' if (a, c) == (i-1, j) else None
                if windows and d_first and d_first == d_last:
                    counts['boundary diagrams'] += 1
                    assert is_root(U, b, delta), (sorted(U), b, delta)
                    counts['roots confirmed'] += 1
                if b >= 3:
                    w2 = (b-2)*delta
                    f2, l2 = band(U, lo, lo+w2), band(U, lo+q-w2, lo+q)
                    if (connected_skew(f2) and connected_skew(l2) and translate_between(f2, l2) is not None
                            and d_first and d_first == d_last
                            and edge_direction(U, delta, 2) == d_first):
                        counts['v = b-2 equal windows, matching cuts'] += 1
                        counts['v = b-2: not a root'] += not is_root(U, b, delta)
    assert counts['boundary diagrams'] and counts['roots confirmed'] == counts['boundary diagrams']
    assert counts['v = b-2: not a root'], 'no diagram showing the boundary is sharp'
    print(dict(counts))
    print('check_full_window_boundary: PASS')


if __name__ == '__main__':
    main()
