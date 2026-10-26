"""Row marks, mixed finer words, and the keyed crossing regrouping.

Paper section `app:physical` (Whole currents and the first complete grade), ph:rectangular-splice;
sec:comparison, ph:mixed-flags, ph:source-chart, ph:finite-block.

* Horizontal row marks (`IsRowMark` in the Lean tree): among the legal case (a) marks of connected
  diagrams with at most CELLS cells, those whose lower copy lies in one row are exactly those with
  single-row end windows (`endRows_of_rowMark` and its converse on this window), and both positive
  and empty row marks occur, so the hypothesis is not vacuous.
* Mixed (d) finers (`mixed_Xw_high`, `mixed_Yw_high`, `legal_low_card`, `legal_mid_card`): on every
  legal case (d) mark, the closed words of J satisfy X_J(r + x) = X_J(x) and
  Y_J(r + x) = [x != s, t] Y_J(x) for 0 <= x <= v, and the column word has one more one than the row
  word on [0, v] and equally many on (v, r).
* `keyed_crossing_regroup`: sum_{j,k} A(j,k) [a <= k] f(j - k) = -sum_D C_{a,D} f(D) on random
  arrays supported on the box.
"""

import os
import random
import sys

sys.path.insert(0, os.path.dirname(__file__))

from _gluing_common import intersection_mark, legal  # noqa: E402
from check_two_copy_flags import betas, diagrams, marks, phases  # noqa: E402

CELLS = 9


def words(E):
    """Closed words X(k), Y(k) on 0 <= k <= N from the beta lists."""
    X, Y = betas(E)
    N = X[0]
    return N, [1 if k in X else 0 for k in range(N + 1)], [1 if k in Y else 0 for k in range(N + 1)]


def check_row_marks():
    pos = emp = total = 0
    for E in diagrams(CELLS):
        for mk in marks(E):
            if mk.case != 'a' or not legal(mk):
                continue
            total += 1
            w, Q = mk.width, mk.period
            X, Y = betas(E)
            window = all(k not in X and k not in Y
                         for k in list(range(1, w)) + list(range(Q + 1, Q + w)))
            one_row = len({i for i, _ in mk.lower}) <= 1
            assert one_row == window, (sorted(E), sorted(mk.lower))
            if one_row:
                if w == 0:
                    emp += 1
                else:
                    pos += 1
    print(f'case (a) legal marks: {total}; positive row marks: {pos}; empty: {emp}')
    assert pos > 0 and emp > 0


def check_mixed():
    count = 0
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
            N, Xw, Yw = words(J)
            assert N == r + v and 0 <= t < s <= v and v >= 1
            for x in range(v + 1):
                assert Xw[r + x] == Xw[x], (sorted(J), x)
                assert Yw[r + x] == (0 if x in (s, t) else Yw[x]), (sorted(J), x)
            assert sum(Yw[:v + 1]) == sum(Xw[:v + 1]) + 1
            assert sum(Yw[v + 1:r]) == sum(Xw[v + 1:r])
            count += 1
    print(f'legal case (d) marks checked: {count}')
    assert count > 0


def check_regroup():
    rng = random.Random(3)
    for _ in range(300):
        M = rng.randint(1, 6)
        a = rng.randint(-1, M + 1)
        A = {(j, k): rng.randint(-4, 4) for j in range(M + 1) for k in range(M + 1)}
        f = {D: rng.randint(-4, 4) for D in range(-M, M + 1)}
        lhs = sum(A[j, k] * (f[j - k] if a <= k else 0)
                  for j in range(M + 1) for k in range(M + 1))

        def C(a, D):
            return -sum(A.get((k + D, k), 0) for k in range(max(a, 0), M - D + 1))
        rhs = -sum(C(a, D) * f[D] for D in range(-M, M + 1))
        assert lhs == rhs, (M, a)
    print('keyed crossing regrouping: 300 random arrays')


def main():
    check_row_marks()
    check_mixed()
    check_regroup()
    print('ALL PASS')


if __name__ == '__main__':
    main()
