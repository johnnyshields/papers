"""The mixed square baseline and its determinant (ph:mixed-baseline-det).

Paper section `sec:comparison` (Finite comparisons on actual composition charts), ph:mixed-flags,
ph:source-chart, ph:mixed-baseline-det.

For every connected finer J with at most CELLS cells, every legal case (d) mark mu of J, and every
connected coarse diagram V of span M <= MAXSPAN, build the actual source E = V o_mu J by the
gluing composition and check:

* the finer lists split as X_J = X_W u B_- u (r + X_W) and
  Y_J = (Y_W u {s}) u C_- u (r + (Y_W \\ {t})), with X_W, Y_W u {s} in [0, v] and B_-, C_- in
  (v, r), where (s, t) are the middle phases and 0 <= t < s <= v;
* the rows of E are the native list: the union of jr + X_W (0 <= j <= M) and jr + B_-
  (0 <= j < M);
* the square baseline -- the fixed columns of E (those off the variable slots jr + s, jr + t,
  0 <= j <= M) together with every jr + s -- is the union of jr + ((Y_W \\ {t}) u {s})
  (0 <= j <= M) and jr + C_- (0 <= j < M);
* its Jacobi--Trudi determinant is +- Ahat^(M+1) C_priv^M at random integer letters, with
  Ahat = det JT(X_W, (Y_W \\ {t}) u {s}) and C_priv = det JT(B_-, C_-).

These are the hypotheses and the conclusion of `mixed_baseline_det` in the Lean tree.
"""

import os
import random
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(__file__))

from _gluing_common import compose, intersection_mark, legal  # noqa: E402
from check_two_copy_flags import betas, diagrams, phases  # noqa: E402

CELLS = 7
MAXSPAN = 4


def det(mat):
    n = len(mat)
    a = [[Fraction(x) for x in row] for row in mat]
    d = Fraction(1)
    for k in range(n):
        p = next((i for i in range(k, n) if a[i][k] != 0), None)
        if p is None:
            return Fraction(0)
        if p != k:
            a[k], a[p] = a[p], a[k]
            d = -d
        d *= a[k][k]
        for i in range(k + 1, n):
            f = a[i][k] / a[k][k]
            for j in range(k, n):
                a[i][j] -= f * a[k][j]
    return d


def jt(X, Y, h):
    return [[h(x - y) for y in Y] for x in X]


def main():
    rng = random.Random(1)
    coarse = [V for V in diagrams(MAXSPAN + 2)
              if max(j - i for i, j in V) - min(j - i for i, j in V) + 1 <= MAXSPAN]
    coarse = [V for V in coarse] + [frozenset({(0, 0)})]
    checked = 0
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
            assert 0 <= t < s <= v, (sorted(J), s, t)
            XJ, YJ = betas(J)
            XW = [x for x in XJ if x <= v]
            Bm = [x for x in XJ if v < x < r]
            low = [y for y in YJ if y <= v]
            Cm = [y for y in YJ if v < y < r]
            assert s in low and t in low
            YW = [y for y in low if y != s]
            assert sorted(XJ) == sorted(XW + Bm + [r + x for x in XW])
            assert sorted(YJ) == sorted(low + Cm + [r + y for y in YW if y != t])
            Yhat = sorted([y for y in YW if y != t] + [s], reverse=True)
            assert len(XW) == len(Yhat) and len(Bm) == len(Cm)
            for V in coarse:
                M = max(j - i for i, j in V) - min(j - i for i, j in V) + 1
                E = compose(V, mu)
                XE, YE = betas(E)
                rows = sorted([j * r + x for j in range(M + 1) for x in XW]
                              + [j * r + b for j in range(M) for b in Bm], reverse=True)
                assert XE == rows, (sorted(J), sorted(V))
                slots = {j * r + s for j in range(M + 1)} | {j * r + t for j in range(M + 1)}
                base = sorted([y for y in YE if y not in slots]
                              + [j * r + s for j in range(M + 1)], reverse=True)
                pred = sorted([j * r + y for j in range(M + 1) for y in Yhat]
                              + [j * r + c for j in range(M) for c in Cm], reverse=True)
                assert base == pred, (sorted(J), sorted(V), base, pred)
                for _ in range(2):
                    vals = {k: rng.randint(-5, 5) for k in range(1, max(XE) + 2)}

                    def h(m):
                        return 0 if m < 0 else (1 if m == 0 else vals[m])

                    d = det(jt(XE, base, h))
                    a = det(jt(XW, Yhat, h))
                    c = det(jt(Bm, Cm, h))
                    assert d == a ** (M + 1) * c ** M, \
                        (sorted(J), sorted(V), d, a, c)
                checked += 1
    print(f'mixed (finer, coarse) pairs checked: {checked}')
    assert checked > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
