r"""Paper section `app:coincident` (Positive coincident attachment phases).

Is the one-coincident wide side invariant under its period vector on the whole middle?
(`app:coincident`, `lem:one-coincident-entry`, "The row coding has only the initial `t` correction
and terminal `M a g + s = L g + t` correction.  Both are outside the internal marked bands";
`CounterpartShiftOne` in `lean/SkewRibbonPeriod/Reduction/CounterpartShiftTwo.lean`.)

The wide side is `Row_j o omega` with `omega` ordinary case (a) of period `P = B g`, width
`w = u + k g` (`k >= 1`, `2 <= u < g`) and phases `s = t + k g`, `0 <= t <= u`; its span is
`L g + u` with `L = j B + k`.  `CounterpartShiftOne` asks for a vector `v` of content `B g` with
`y in T <-> y + v in T` on the contents `[c0 + u, c0 + (L - B) g)`.  `chart_shift_mem` gives this
only on `[c0 + w, c0 + (j - 1) B g)`.  Counted here: the composites where the full window fails,
and separately where the band COMPONENT CLASSES on the internal bands fail to be `B`-periodic,
which is what `CounterpartClassPeriodic` actually consumes.
"""

from check_band_single_component import components, interior
from check_line_charge import phases
from check_regroup_mixed import content, legal_marks, min_content, skew_shapes
from check_ribbon_outer_shift import shift_exists
from check_top_seam_form import jt


def row(m):
    return frozenset((0, j) for j in range(m))


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
    total = full_fail = inner_fail = class_fail = 0
    for E in skew_shapes(13, 4, 9):
        for om in legal_marks(E):
            if om.case != 'a':
                continue
            w = om.width()
            s, t = phases(om)
            P = om.period()
            if s <= t:
                continue
            for g in range(3, P):
                if P % g or P // g < 2:
                    continue
                B = P // g
                if (s - t) % g:
                    continue
                k = (s - t) // g
                u = w - k * g
                if k < 1 or not (2 <= u < g) or not (0 <= t <= u):
                    continue
                for j in (2, 3):
                    T = om.compose(row(j))
                    L = j * B + k
                    assert len({content(x) for x in T}) == L * g + u
                    total += 1
                    assert shift_exists(T, P, w, (j - 1) * P), (sorted(T), P, w)
                    if not shift_exists(T, P, w, (L - B) * g):
                        inner_fail += 1
                    if not shift_exists(T, P, u, (L - B) * g):
                        full_fail += 1
                    cl = band_classes(T, g, u, L)
                    if any(cl[i] != cl[i + B] for i in range(1, L - B)):
                        class_fail += 1
    print(f"one-coincident wide sides: {total}")
    print(f"  membership shift fails on [u, (L-B)g): {full_fail}")
    print(f"  membership shift fails on [w, (L-B)g): {inner_fail}")
    print(f"  band classes not B-periodic: {class_fail}")
    assert total > 0
    # `CounterpartShiftOne` holds on every tested wide side, on the full window, although
    # `chart_shift_mem` alone covers only `[w, (j - 1) B g)`
    assert full_fail == 0 and inner_fail == 0 and class_fail == 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
