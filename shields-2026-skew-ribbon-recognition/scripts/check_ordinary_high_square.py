"""The high piece of an ordinary finer and the flags of its two-copy diagram (ph:active-dichotomy,
ph:ordinary-two-copy).

Paper section `app:endpoints` (Endpoint scalars and ordinary reflection), ph:active-dichotomy, and
app:cofaces, ph:ordinary-two-copy.

For every connected skew diagram J with at most CELLS cells and every legal nonempty case (a) mark
of J, of period r, width v and phases (s, t):

1. the proper rows X_J \\ {N} and the proper columns Y_J \\ {0} at least r are equally many, so the
   threshold r splits the proper corner (the high piece r + JT(X_W \\ s, Y_W \\ 0) is square);
2. Z = Row_2 o_mu J has flags X_Z = B_0 u (r + B_0) u (2r + B_+) u {2r + s} and
   Y_Z = C_0 u (r + C_0) u (2r + C_+) u {t}: on [0, 2r + v] the row word of Z is the row word of
   J at the native position (k for k <= r, k - r beyond) and the column word is the native one
   except at r + t with t > 0, where Z has no column;
3. the fixed matrix D_2 of the two-copy solve is block lower triangular by period: every native row
   of Z in a period block (B_0, r + B_0, 2r + B_+) lies below every native column of a later block
   (C_0, r + C_0, 2r + C_+), so h vanishes there.  This uses no rectangular-shape condition and
   holds on two-row lower copies too.

The counts are read directly off the cell lists, not from the boundary words the Lean proofs use.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(__file__))

from check_two_copy_flags import betas, diagrams, marks, phases  # noqa: E402
from _gluing_common import compose, legal  # noqa: E402

CELLS = 9


def main():
    row2 = frozenset({(0, 0), (0, 1)})
    total = 0
    tpos = 0
    two_row = 0
    for J in diagrams(CELLS):
        for mk in marks(J):
            if mk.case != 'a' or not mk.lower or not legal(mk):
                continue
            total += 1
            r, v = mk.period, mk.width
            s, t = phases(mk)
            tpos += t > 0
            X, Y = betas(J)
            N = r + v
            assert X[0] == N and Y[-1] == 0
            rows_hi = sum(1 for x in X[1:] if x >= r)
            cols_hi = sum(1 for y in Y[:-1] if y >= r)
            assert rows_hi == cols_hi, (sorted(J), sorted(mk.lower))
            XZ, YZ = betas(compose(row2, mk))
            assert XZ[0] == 2 * r + v
            for k in range(0, 2 * r + v + 1):
                nat = k if k <= r else k - r
                assert (k in XZ) == (nat in X and nat != 0), (sorted(J), k)
                if k == r + t and t > 0:
                    assert k not in YZ, (sorted(J), k)
                else:
                    assert (k in YZ) == (nat in Y and nat != N), (sorted(J), k)
            B0 = [x for x in X if 0 < x < r]
            C0 = [y for y in Y if y < r and y != t]
            Bp = [x for x in X if 0 < x <= v and x != s]
            Cp = [y for y in Y if y <= v and y != t]
            rowsZ = [B0, [r + b for b in B0], [2 * r + b for b in Bp]]
            colsZ = [C0, [r + c for c in C0], [2 * r + c for c in Cp]]
            assert sorted(set(sum(rowsZ, [])) | {2 * r + s}) == sorted(x for x in XZ if x > 0)
            assert sorted(set(sum(colsZ, [])) | {t}) == sorted(YZ), (sorted(J), sorted(mk.lower))
            assert len(B0) == len(C0) and len(Bp) == len(Cp)
            two_row += len({i for i, _ in mk.lower}) > 1
            for p in range(3):
                for q in range(p + 1, 3):
                    assert all(x < y for x in rowsZ[p] for y in colsZ[q])
    print(f'two-row lower copies: {two_row}')
    assert two_row > 0
    print(f'legal nonempty case (a) marks: {total}; with t > 0: {tpos}')
    assert 0 < tpos < total
    print('ALL PASS')


if __name__ == '__main__':
    main()
