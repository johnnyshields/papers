r"""Paper section `app:coincident` (Positive coincident attachment phases).

The period vector of a ribbon-outer chart on its middle (`app:coincident`, `lem:mark-pair`,
"The original seam assignment gives literal charts through `A_0`- and `B_0`-cell ribbon natives";
`CounterpartShift` and `counterpart_shift_two` in
`lean/SkewRibbonPeriod/Reduction/CounterpartShiftTwo.lean`).

`chart_shift_mem` gives, for a chart `omega o D` of period `P` and width `u` over a ROW outer `D` of
`m` cells, a vector `v` of content `P` with `y in S <-> y + v in S` on the contents
`[c0 + u, c0 + (m - 1) P)`.  The Lean route for the two-coincident counterpart therefore needs the
counterpart outer to be a line first (`CounterpartRibbonLineTwo`), while the paper reads the
counterpart's marked bands off the seam assignment of its chart alone.

This script asks the question that decides whether the line outer is needed for the shift: for a
coincident case-(a) composite over a ribbon outer that is NOT a line, is the middle of the composite
invariant under a single vector of content `P`?  It counts the composites where no such vector
exists.  The statement actually used downstream is weaker -- invariance of the band COMPONENT
CLASSES, not of membership -- and that is checked as well.
"""

from check_band_single_component import components, interior
from check_chart_witnesses import flags
from check_line_charge import phases
from check_regroup_mixed import content, legal_marks, min_content, skew_shapes
from check_top_seam_form import jt


def is_line(D):
    rows = {i for i, _ in D}
    cols = {j for _, j in D}
    return len(rows) == 1 or len(cols) == 1


def ribbon(D):
    return not any((i + 1, j + 1) in D for i, j in D)


def shift_exists(S, P, lo, hi):
    c0 = min_content(S)
    window = [y for y in S if c0 + lo <= content(y) < c0 + hi]
    if not window:
        return True
    cand = {(a, a + P) for a in range(-40, 41)}
    for v in cand:
        ok = True
        for i in range(min(x for x, _ in S) - 3, max(x for x, _ in S) + 4):
            for j in range(min(y for _, y in S) - 3, max(y for _, y in S) + 4):
                y = (i, j)
                if not (c0 + lo <= content(y) < c0 + hi):
                    continue
                if (y in S) != ((i + v[0], j + v[1]) in S):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False


def band_classes(S, g, u, L):
    c0 = min_content(S)
    comps = components(interior(S))
    out = {}
    for i in range(1, L):
        lo, hi = c0 + i * g, c0 + i * g + u - 1
        inside = [C for C in comps if all(lo <= content(x) <= hi for x in C)]
        out[i] = tuple(sorted(str(jt(C)) for C in inside))
    return out


def main():
    total = nonline = no_shift = class_breaks = 0
    for E in skew_shapes(7, 3, 4):
        for om in legal_marks(E):
            if om.case != 'a':
                continue
            u = om.width()
            s, t = phases(om)
            if not (s == t and 0 < s < u and u >= 2):
                continue
            P = om.period()
            for D in skew_shapes(4, 3, 3):
                if len(D) < 2 or not ribbon(D):
                    continue
                S = om.compose(D)
                total += 1
                m = len({content(x) for x in D})
                if is_line(D):
                    assert shift_exists(S, P, u, (m - 1) * P), (sorted(S), P, u)
                    continue
                nonline += 1
                if not shift_exists(S, P, u, (m - 1) * P):
                    no_shift += 1
                # the band classes at the gcd period `g = P` with `L = m`: shift by one band
                L = m
                cl = band_classes(S, P, u, L)
                if any(cl[i] != cl[i + 1] for i in range(1, L - 1)):
                    class_breaks += 1
    print(f"coincident case-(a) ribbon-outer composites: {total}, non-line outers: {nonline}")
    print(f"  non-line with no period vector on the middle: {no_shift}")
    print(f"  non-line whose band classes are not constant: {class_breaks}")
    assert total > 0 and nonline > 0
    # the line outer is genuinely needed for the period vector: a non-line ribbon outer breaks it
    assert no_shift > 0 and class_breaks > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
