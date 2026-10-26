"""The mixed normalization on the flags of actual legal case (d) marks.

Paper section `app:cofaces` (Cofaces, two-copy identities, and native residues), ph:coface-data (mixed
normalization), ph:CF0.

For every legal case (d) mark of a connected diagram J with at most CELLS cells, with
X_W = X_J on [0, v], Y_W = (Y_J on [0, v]) minus {s}, the low rectangular mark matrix is
JT(X_W, Y_W + {s}).  Its two maximal minors are

    D_W = det JT(X_W, (Y_W + {s}) - {0}),    A^ = det JT(X_W, (Y_W - {t}) + {s}),

and N_W = det JT(X_W - {v}, Y_W - {t}).  With all lists decreasing, at random rational letters:

* g_t, the right coframe of J (normalized at the zero column) at the column t, is
  chi * A^ / D_W with chi = (-1)^(a - k), a = |X_W|, k = #{y in Y_W + {s} : y > t};
  at t = 0 both sides are 1;
* eta = (A^^{-1})_{s, v}, the inverse s-row of the replaced mark at the top mark row v, is
  psi * N_W / A^ with psi = (-1)^p, p = #{y in Y_W : y > s};
* eta equals the entry (D_0^{-1})_{s, v} of the native one-period block
  D_0 = JT(X_W + B_-, (Y_W - {t}) + C_- + {s});
* X_J on [r, r + v] is r + X_W and Y_J on [r, r + v) is r + (Y_W - {t}), and N_W, D_W are the
  determinants of the high and the low diagonal blocks of the proper matrix of J.
"""

import os
import random
import sys

sys.path.insert(0, os.path.dirname(__file__))

from _gluing_common import intersection_mark, legal  # noqa: E402
from check_two_copy_flags import betas, diagrams, phases  # noqa: E402

from sympy import Matrix, Rational  # noqa: E402

CELLS = int(sys.argv[1]) if len(sys.argv) > 1 else 9


def jt(h, rows, cols):
    return Matrix(len(rows), len(cols), lambda i, j: h(rows[i] - cols[j]))


def det(h, rows, cols):
    return jt(h, rows, cols).det() if rows else Rational(1)


def check(r, v, X, Y, XW, YW, s, t, Bm, Cm, seed):
    rnd = random.Random(seed)
    hv = {n: Rational(rnd.randint(-9, 9), rnd.randint(1, 5)) for n in range(4 * r + 4)}
    hv[0] = Rational(1)
    h = lambda n: hv[n] if n >= 0 else 0  # noqa: E731
    dec = lambda L: sorted(L, reverse=True)  # noqa: E731
    NJ = r + v
    xw = dec(XW)
    a = len(xw)
    assert xw[0] == v
    low = dec(YW + [s])
    DW = det(h, xw, [y for y in low if y != 0])
    Ah = det(h, xw, [y for y in low if y != t])
    NW = det(h, xw[1:], dec([y for y in YW if y != t]))
    if DW == 0 or Ah == 0 or NW == 0:
        return None
    # g_t from the right coframe of J
    rows = dec([x for x in X if x != NJ])
    cols = dec([y for y in Y if y != 0])
    T = jt(h, rows, cols)
    b = Matrix([h(x) for x in rows])
    G = -(T.inv() * b)
    gt = G[cols.index(t)] if t != 0 else Rational(1)
    k = sum(1 for y in low if y > t)
    chi = (-1) ** (a - k)
    assert gt == chi * Ah / DW, ("g_t", gt, Ah / DW)
    # eta from the inverse s-row of the replaced mark
    yhat = [y for y in low if y != t]
    Ahat = jt(h, xw, yhat)
    eta = Ahat.inv()[yhat.index(s), 0]
    p = sum(1 for y in YW if y > s)
    assert eta == (-1) ** p * NW / Ah, ("eta", eta, NW / Ah)
    # the same entry of the native one-period block
    nrows = dec(XW + Bm)
    ncols = dec([y for y in YW if y != t] + Cm + [s])
    D0 = jt(h, nrows, ncols)
    assert D0.inv()[ncols.index(s), nrows.index(v)] == eta
    # the high and low blocks of the proper matrix of J
    hi = a - 1
    assert rows[:hi] == [r + x for x in xw[1:]], "high rows"
    assert cols[:hi] == [r + y for y in dec([y for y in YW if y != t])], "high cols"
    assert rows[-a:] == xw and cols[-a:] == [y for y in low if y != 0], "low block"
    assert det(h, rows[:hi], cols[:hi]) == NW
    return chi, (-1) ** p


def main():
    seen = set()
    count = {False: 0, True: 0}
    signs = set()
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
            key = (r, v, tuple(XW), tuple(YW), s, t, tuple(Bm), tuple(Cm))
            if key in seen:
                continue
            seen.add(key)
            for seed in range(5):
                res = check(r, v, X, Y, XW, YW, s, t, Bm, Cm, seed)
                if res is not None:
                    signs.add(res)
                    break
            else:
                raise AssertionError(("no generic sample", key))
            count[t > 0] += 1
    print(f"legal (d) flag sets: t = 0: {count[False]}, t > 0: {count[True]}")
    print(f"(chi, psi) seen: {sorted(signs)}")
    assert count[False] > 0 and count[True] > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
