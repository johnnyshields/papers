"""The one-period response at a low mark row of a mixed finer (hsupp of the row reader).

Paper section `sec:comparison` (Finite comparisons on actual composition charts), ph:mixed-flags and the mixed
response l = e_s^T D_s(u)^{-1} on the native rows R = X_W + B_- and columns
C = (Y_W - t) + C_- + {s}.

[u^1] l_b = -sum_{x in R, y in C} l0_x h_{r + x - y} (D_0^{-1})_{y, b}.  The top letter
h_{r + max R} occurs only at the entry (max R, 0) (0 is a column, since t > 0) and nowhere in D_0,
so in algebraically independent letters [u^1] l_b != 0 as soon as both
l0_{max R} = (D_0^{-1})_{s, max R} and (D_0^{-1})_{0, b} are nonzero, i.e. the Jacobi--Trudi minors
(R - max R, C - s) and (R - b, C - 0) have valid skew shapes.  Checked at every low mark row
b < v of every legal case (d) mark with t > 0, up to CELLS cells; it does NOT hold on every
such row, so it proves hsupp only where it holds (the numeric nonvanishing on all of them is
check_mixed_coframe_legal_marks.py).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(__file__))

from _gluing_common import intersection_mark, legal  # noqa: E402
from check_two_copy_flags import betas, diagrams, phases  # noqa: E402

CELLS = int(sys.argv[1]) if len(sys.argv) > 1 else 11


def valid(rows, cols):
    """det(h_{x - y}) over distinct rows and columns is a nonzero skew Schur function exactly
    when, both sorted decreasingly, every row dominates its column."""
    if len(set(rows)) != len(rows):
        return False
    return all(x >= y for x, y in zip(sorted(rows, reverse=True), sorted(cols, reverse=True)))


def main():
    hist = {}
    bad = []
    total = 0
    seen = set()
    for J in diagrams(CELLS):
        for cell in J:
            try:
                mu = intersection_mark(J, cell)
            except AssertionError:
                continue
            if mu.case != 'd' or not legal(mu):
                continue
            r, v = mu.period, mu.width
            s, t = phases(mu)
            if t == 0:
                continue
            X, Y = betas(J)
            XW = sorted(x for x in X if x <= v)
            R = sorted(x for x in X if x < r)
            C = sorted(y for y in Y if y < r and y != t)  # (Y_W - t) + C_- + {s}
            key = (r, v, tuple(R), tuple(C), s, t)
            if key in seen:
                continue
            seen.add(key)
            assert len(R) == len(C) and valid(R, C)
            xmax = max(R)
            assert 0 in C
            top = valid([x for x in R if x != xmax], [y for y in C if y != s])
            for b in XW:
                if b >= v:
                    continue
                ok = top and valid([x for x in R if x != b], [y for y in C if y != 0])
                total += 1
                hist[ok] = hist.get(ok, 0) + 1
                if not ok and len(bad) < 5:
                    bad.append((key, b))
    print(f"low mark rows (t > 0) on legal (d) marks up to {CELLS} cells: {total}")
    print("top-letter criterion holds / fails:", hist.get(True, 0), "/", hist.get(False, 0))
    for e in bad:
        print("  criterion fails:", e)
    assert total > 0 and hist.get(True, 0) > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
