"""The one-period mixed coframe reading on flags of actual legal case (d) marks.

Paper section `sec:comparison` (Finite comparisons on actual composition charts), ph:mixed-flags, ph:mixed-native.

`check_mixed_one_period_coframe.py` samples flag configurations of the shape of ph:mixed-flags.
Here the flags are read off every legal case (d) mark of a connected diagram J with at most CELLS
cells: X_W = X_J on [0, v], B_- = X_J on (v, r), Y_W = (Y_J on [0, v]) minus {s}, C_- = Y_J on
(v, r), and the same reading is run on each.  Reports, separately for t = 0 and t > 0, how many
legal marks have a low mark row b < v (b in X_W) where `[u^1] l_b = eta * C_{N_J - b}` fails.
The high-mark and private-row identities are asserted on every mark by `sample`.

The row reader of `ph:mixed-native` needs the one-period response to be nonzero at every actual
row `x < N_J` of `J`: `[u^1] l_x` at a row `x < r` (a low or top mark row, or a private row) and
`[u^0] l_b` at a high mark row `x = r + b`.  `resp_support` evaluates all of them at random
rational letters with `D_s(0)` invertible; a nonzero value at one point shows the rational
function is not identically zero.  Asserted on every legal mark, both signs of `t`.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(__file__))

from _gluing_common import intersection_mark, legal  # noqa: E402
from check_two_copy_flags import betas, diagrams, phases  # noqa: E402
from check_mixed_one_period_coframe import sample  # noqa: E402

import random  # noqa: E402

from sympy import Matrix, Rational  # noqa: E402

CELLS = int(sys.argv[1]) if len(sys.argv) > 1 else 9


def resp_support(r, v, XW, YW, s, t, Bm, Cm, seed):
    """The one-period response at every actual row x < N_J, at random rational letters."""
    rnd = random.Random(1000 + seed)
    rows = sorted(XW + Bm)
    cols = sorted([c for c in YW if c != t] + Cm + [s])
    k = len(rows)
    while True:
        hv = {n: Rational(rnd.randint(-9, 9), rnd.randint(1, 5)) for n in range(4 * r + 4)}
        hv[0] = Rational(rnd.randint(1, 9), rnd.randint(1, 3))
        h = lambda n: hv[n] if n >= 0 else 0  # noqa: E731
        D = [Matrix(k, k, lambda i, j: h(n * r + rows[i] - cols[j])) for n in range(2)]
        if D[0].det() != 0:
            break
    D0i = D[0].inv()
    l0 = D0i.row(cols.index(s))
    l1 = (-D0i * D[1] * D0i).row(cols.index(s))
    vals = {}
    for i, b in enumerate(rows):
        vals[b] = l1[i]  # target b < r: [u^1] l_b
        if b in XW and b < v:
            vals[r + b] = l0[i]  # target r + b: [u^0] l_b
    return vals


def main():
    seen = set()
    stats = {False: [0, 0, 0], True: [0, 0, 0]}  # marks, with a low row, with a failing low row
    examples = []
    support_fail = []
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
            X, Y = betas(J)
            XW = sorted(x for x in X if x <= v)
            Bm = sorted(x for x in X if v < x < r)
            YW = sorted(y for y in Y if y <= v and y != s)
            Cm = sorted(y for y in Y if v < y < r)
            # the flags of ph:mixed-flags reproduce the actual beta lists
            assert sorted(X) == sorted(XW + Bm + [r + x for x in XW]), (sorted(J), r, v)
            assert sorted(Y) == sorted(YW + [s] + Cm + [r + y for y in YW if y != t]), (sorted(J),)
            key = (r, v, tuple(XW), tuple(YW), s, t, tuple(Bm), tuple(Cm))
            if key in seen:
                continue
            seen.add(key)
            low = [b for b in XW if b < v]
            st = stats[t > 0]
            st[0] += 1
            XJ = set(X)
            for seed in range(2):
                vals = resp_support(r, v, XW, YW, s, t, Bm, Cm, seed)
                assert set(vals) == {x for x in XJ if x < r + v}, key
                zero = [x for x, val in vals.items() if val == 0]
                if not zero:
                    break
            else:
                support_fail.append((key, zero))
            if not low:
                continue
            st[1] += 1
            ok = all(all(sample(r, v, XW, YW, s, t, Bm, Cm, seed)) for seed in range(2))
            if not ok:
                st[2] += 1
                if len(examples) < 5:
                    examples.append(key)
    for tpos in (False, True):
        m, lw, bad = stats[tpos]
        print(f"t {'> 0' if tpos else '= 0'}: legal (d) flag sets {m}, with a low mark row {lw}, "
              f"failing at a low mark row {bad}")
    for e in examples:
        print("  failing (r, v, X_W, Y_W, s, t, B_-, C_-):", e)
    print(f"one-period response vanishing at an actual row: {len(support_fail)} flag sets")
    for e in support_fail[:5]:
        print("  vanishing:", e)
    assert stats[False][2] == 0
    assert not support_fail
    print("ALL PASS")


if __name__ == "__main__":
    main()
