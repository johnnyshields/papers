r"""Paper section `app:coincident` (Positive coincident attachment phases).

Native height at marked residues of a zero-offset ordinary mark
(`app:coincident`, `lem:one-coincident-entry`, "marked positions read Omega plus a positive outer
height"; `bandTwo_compose` in `lean/SkewRibbonPeriod/Reduction/One/BandTwo.lean`).

For every legal ordinary mark with equal phases `s = t` on a small skew `E`, of period `q` and
width `w`, the height of `E` on the diagonals `a` with `s <= a < w` is at least two, and on every
diagonal `0 <= a < q` it is at least one.
"""

from check_line_charge import phases
from check_regroup_mixed import diag_hi, diag_lo, legal_marks, min_content, skew_shapes


def main():
    total = marked = 0
    for E in skew_shapes(13, 4, 9):
        for om in legal_marks(E):
            if om.case not in "ab":
                continue
            s, t = phases(om)
            if s != t:
                continue
            q, w = om.period(), om.width()
            c0 = min_content(E)
            total += 1
            for a in range(q):
                h = diag_hi(E, c0 + a) - diag_lo(E, c0 + a) + 1
                assert h >= 1, (sorted(E), a)
                if s <= a < w:
                    marked += 1
                    assert h >= 2, (sorted(E), om.case, s, a, h)
    print(f"zero-offset ordinary marks: {total}, marked diagonals checked: {marked}")
    assert total > 0 and marked > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
