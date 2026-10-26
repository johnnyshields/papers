r"""Paper section `app:coincident` (Positive coincident attachment phases).

The counterpart is invariant under its period vector in the middle (`lem:one-coincident-entry`,
"The row coding has only the initial `t` correction and terminal `M a g + s = L g + t` correction.
Both are outside the internal marked bands, so their complete component words have period `a`";
`CounterpartShift` in `lean/SkewRibbonPeriod/Reduction/ClassTopSeam.lean`).

For every legal mark of case (a) or (b) on a small connected skew `E`, of period `P = B g` with
`B >= 2` and width `w = k g + u`, `2 <= u < g`, and every row outer of `M` cells whose composite
`S` has `P(g, u)` heights (span `L g + u`), membership in `S` is invariant under the period vector
on the contents `[c0 + u, c0 + (L - B) g)`.  For `k = 0` this is the shift the row outer gives
directly; for `k >= 1` (the wide side) the window starts below the width, which is the end
correction of the paper.
"""

from check_regroup_mixed import add, content, legal_marks, min_content, skew_shapes
from check_top_seam_form import heights_ok, row


def main():
    tested = {0: 0, 1: 0}
    for E in skew_shapes(11, 5, 7):
        for om in legal_marks(E):
            if om.case not in ('a', 'b'):
                continue
            w, P = om.width(), om.period()
            for g in range(3, P):
                if P % g or P // g < 2:
                    continue
                B = P // g
                k, u = divmod(w, g)
                if u < 2:
                    continue
                for M in (2, 3):
                    S = om.compose(row(M))
                    L = heights_ok(S, g, u)
                    if L is None:
                        continue
                    c0 = min_content(S)
                    v = om.v
                    back = {(x[0] - v[0], x[1] - v[1]) for x in S}
                    for y in set(S) | back:
                        if c0 + u <= content(y) < c0 + (L - B) * g:
                            assert (y in S) == (add(y, v) in S), (sorted(E), om.case, g, u, M, y)
                    tested[min(k, 1)] += 1
    print(f"composites with P(g, u) heights: width below g {tested[0]}, wide {tested[1]}")
    assert tested[1] > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
