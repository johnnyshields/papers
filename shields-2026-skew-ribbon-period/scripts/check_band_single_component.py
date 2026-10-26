r"""Paper section `app:coincident` (Positive coincident attachment phases).

One interior component per marked band of a coincident row composite (`app:coincident`, "The
whole marked-band determinant": "An original coincident ribbon seam has whole height `Omega_r + 1`
on its marked band ... Each such band is consequently one connected actual proper component `B_i`
of span `u`"; `BandSingleComponent` in `lean/SkewRibbonPeriod/Reduction/BandClassParts.lean`).

For every legal case-(a) mark `omega` on a small connected skew `E` with coincident internal phase
`0 < s = t < u`, `u >= 2`, and every row outer of `m` cells, the composite `S = Row_m o E` has, on
each seam window `[c0 + j p, c0 + j p + u - 1]`, `1 <= j < m`, interior diagonals of height at
least two throughout, and the interior cells on that window form exactly one edge component of
span `u`.  The script asserts both.
"""

import sys

from check_line_charge import phases
from check_regroup_mixed import content, is_connected, legal_marks, min_content, skew_shapes


def row(m):
    return frozenset((0, j) for j in range(m))


def interior(S):
    return frozenset(x for x in S if (x[0] + 1, x[1] + 1) in S)


def components(X):
    left = set(X)
    out = []
    while left:
        seed = left.pop()
        comp = {seed}
        stack = [seed]
        while stack:
            x = stack.pop()
            for y in ((x[0] + 1, x[1]), (x[0] - 1, x[1]), (x[0], x[1] + 1), (x[0], x[1] - 1)):
                if y in left:
                    left.remove(y)
                    comp.add(y)
                    stack.append(y)
        out.append(frozenset(comp))
    return out


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    cases = bands = 0
    for E in skew_shapes(nmax, 5, 6):
        for om in legal_marks(E):
            if om.case != 'a':
                continue
            u = om.width()
            s, t = phases(om)
            if not (s == t and 0 < s < u and u >= 2):
                continue
            p = om.period()
            for m in range(2, 5):
                S = om.compose(row(m))
                assert is_connected(S)
                I = interior(S)
                comps = components(I)
                c0 = min_content(S)
                cases += 1
                for j in range(1, m):
                    lo, hi = c0 + j * p, c0 + j * p + u - 1
                    for c in range(lo, hi + 1):
                        h = sum(1 for x in S if content(x) == c)
                        assert h >= 2, (sorted(E), sorted(om.W), om.v, m, j, c, h)
                    inside = [C for C in comps if all(lo <= content(x) <= hi for x in C)]
                    assert len(inside) == 1, (sorted(E), sorted(om.W), om.v, m, j, len(inside))
                    spanC = len({content(x) for x in inside[0]})
                    assert spanC == u, (sorted(E), sorted(om.W), om.v, m, j, spanC)
                    bands += 1
    print(f"coincident case-(a) composites: {cases}, bands checked: {bands}")
    assert cases > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
