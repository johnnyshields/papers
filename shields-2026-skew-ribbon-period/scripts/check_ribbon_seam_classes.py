r"""Paper section `app:coincident` (Positive coincident attachment phases).

The class of each marked seam of a coincident composite follows the step of its ribbon outer
(`app:coincident`, `lem:mark-pair`: "At an original source seam, the horizontal step contributes
class `B` and the vertical step class `A`"; the bridge from the band classes to
`CounterpartRibbonLineTwo` in `lean/SkewRibbonPeriod/Reduction/`).

For every legal case-(a) mark `omega` on a small connected skew `E` with coincident internal phase
`0 < s = t < u`, `u >= 2`, and every ribbon outer `C` of `k` cells, the composite `S = C o E` has
on the seam window of each step `j` of `C` (contents `[c0 + j p, c0 + j p + u - 1]`) exactly one
interior component, of span `u`.  Its Schur function depends only on the direction of the step:
one function on every horizontal step, another on every vertical step, and the two differ.  The
vertical class is the mark function `s_W`.
"""

import sys

import sympy as sp

from check_band_single_component import components, interior
from check_chart_witnesses import schur
from check_line_charge import phases
from check_regroup_mixed import content, is_connected, legal_marks, min_content, skew_shapes

DEG = 30
h = {0: sp.Integer(1)}
h.update({j: sp.Symbol(f"h{j}") for j in range(1, DEG + 1)})


def ribbon(comp):
    """Ribbon with row lengths `comp`, top row first, rows going south-west."""
    cells = []
    row, end = 0, 0
    for c in comp:
        for j in range(end - c + 1, end + 1):
            cells.append((row, j))
        end = end - c + 1
        row += 1
    return frozenset(cells)


def steps(C):
    cells = sorted(C, key=content)
    out = []
    for a, b in zip(cells, cells[1:]):
        out.append('h' if a[0] == b[0] else 'v')
    return out


def norm(D):
    r = min(x[0] for x in D)
    c = min(x[1] for x in D)
    return frozenset((x[0] - r, x[1] - c) for x in D)


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    cache = {}

    def sch(D):
        key = norm(D)
        if key not in cache:
            cache[key] = schur(key, h)
        return cache[key]

    cases = 0
    for E in skew_shapes(nmax, 5, 6):
        for om in legal_marks(E):
            if om.case != 'a':
                continue
            u = om.width()
            s, t = phases(om)
            if not (s == t and 0 < s < u and u >= 2):
                continue
            p = om.period()
            sW = sch(om.W)
            for k in range(2, kmax + 1):
                for comp in _compositions(k):
                    C = ribbon(comp)
                    st = steps(C)
                    S = om.compose(C)
                    assert is_connected(S)
                    comps = components(interior(S))
                    c0 = min_content(S)
                    cls = {'h': set(), 'v': set()}
                    for j, d in enumerate(st, start=1):
                        lo, hi = c0 + j * p, c0 + j * p + u - 1
                        inside = [X for X in comps if all(lo <= content(x) <= hi for x in X)]
                        assert len(inside) == 1, (sorted(E), comp, j, len(inside))
                        cls[d].add(sp.srepr(sch(inside[0])))
                    assert len(cls['h']) <= 1 and len(cls['v']) <= 1, (sorted(E), comp, cls)
                    if cls['h'] and cls['v']:
                        assert cls['h'] != cls['v'], (sorted(E), comp)
                    if cls['v']:
                        assert cls['v'] == {sp.srepr(sW)}, (sorted(E), comp)
                    cases += 1
    print(f"coincident case-(a) composites over ribbon outers: {cases}")
    assert cases > 0
    print("ALL PASS")


def _compositions(k):
    if k == 0:
        yield ()
        return
    for first in range(1, k + 1):
        for rest in _compositions(k - first):
            yield (first,) + rest


if __name__ == "__main__":
    main()
