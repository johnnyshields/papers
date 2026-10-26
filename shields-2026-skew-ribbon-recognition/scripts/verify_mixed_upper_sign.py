r"""Paper section `app:endpoints` (Endpoint scalars and ordinary reflection), ph:mixed-upper-sign.

The actual finite comparison produces the returned low cofactor equation through ph:row-value.
This check covers its explicit word/cofactor subgate: A_{s-delta,t}(W)=A_{s,delta+t}(W),
the closed upper recurrences, actual central contacts, and the singleton pinches.
It does not construct a nonliteral Schur-equal comparison.

  (d)  X_W(x+delta) = X_W(x),   Y_W(x+delta) = Y_W(x) - [x = t_O] - [x = s_O],
  (c)  X_W(x+delta) = X_W(x) + [x = t_O] + [x = s_O],   Y_W(x+delta) = Y_W(x),

Enumerate connected strict boards through VMAX, retaining shared row/column labels and their
genuine unit entries.  Independently of whether the cofactor equality holds, assert the exact
telescoping parity formula on every present-port case with both singleton pinches.  This is
non-vacuous coverage of the sign mechanism even if the bounded full-subgate count is zero.
Cases meeting the full subgate must satisfy the strict-between conclusion and cannot have
s=v,t=0.  A zero count is a bounded observation, not universal unsatisfiability.

Actual composition sources independently check the upper recurrences.  Their cofactor-equality
count is reported, not assumed to be zero: geometry alone does not supply the finite comparison.
"""
import itertools
from functools import lru_cache
from math import comb

import sympy as sp

from _gluing_common import compose, content, intersection_mark, legal, span
from check_two_copy_flags import betas, diagrams, marks, phases

VMAX = 9
hs = sp.symbols('h1:40')


def h(i):
    return 0 if i < 0 else 1 if i == 0 else hs[i - 1]


def cofactor(X, Y, x, y):
    if x not in X or y not in Y:
        return sp.Integer(0)
    i, j = X.index(x), Y.index(y)
    rows = [a for k, a in enumerate(X) if k != i]
    cols = [b for k, b in enumerate(Y) if k != j]
    det = sp.Matrix(len(rows), len(cols), lambda p, q: h(rows[p] - cols[q])).det() if rows \
        else sp.Integer(1)
    return (-1) ** (i + j) * sp.expand(det)


@lru_cache(maxsize=None)
def _cofactor_value(X, Y, x, y, alphabet):
    if x not in X or y not in Y:
        return sp.Integer(0)
    row, column = X.index(x), Y.index(y)

    def entry(i, j):
        if i == row:
            return int(j == column)
        n = X[i] - Y[j]
        return 0 if n < 0 else comb(alphabet + n - 1, n)

    return sp.Matrix(len(X), len(Y), entry).det()


def _cofactors_equal(X, Y, x1, y1, x2, y2):
    # Unequal exact specializations refute polynomial equality.  Agreement never proves it.
    X, Y = tuple(X), tuple(Y)
    for alphabet in (VMAX + 1, VMAX + 2):
        if _cofactor_value(X, Y, x1, y1, alphabet) != _cofactor_value(X, Y, x2, y2, alphabet):
            return False
    return sp.expand(cofactor(X, Y, x1, y1) - cofactor(X, Y, x2, y2)) == 0


def recurrences(case, X, Y, v, w, d, tO, sO):
    for x in range(w + 1):
        bx = (x + d in X) - (x in X)
        by = (x + d in Y) - (x in Y)
        e = (x == tO) + (x == sO)
        if case == 'd' and not (bx == 0 and by == -e):
            return False
        if case == 'c' and not (bx == e and by == 0):
            return False
    return True


def inequality(case, s, t, d, tO, sO):
    return (tO < t < sO) if case == 'd' else (tO < s - d < sO)


def _connected_flags(X, Y):
    return (len(X) == len(Y) and all(a > b for a, b in zip(X, Y))
            and all(a >= b for a, b in zip(X[1:], Y)))


def _check_parity(case, X, Y, s, t, d, tO, sO):
    beta, y = s - d, d + t
    R = sum(x < d for x in X)
    C = sum(x < d for x in Y)
    assert C - R == 1
    exponent = sum(beta <= x < s for x in X) + sum(t <= x < y for x in Y)
    expected = (2 * R + 1 - (tO < t) - (sO < t)) if case == 'd' \
        else (2 * C - 1 + (tO < beta) + (sO < beta))
    assert exponent == expected, (case, X, Y, s, t, d, tO, sO)


def main():
    assert _connected_flags([2, 1], [1, 0])
    for X, Y in (((2, 1), (1, 0)), ((4, 2, 1), (2, 1, 0))):
        for alphabet in (VMAX + 1, VMAX + 2):
            values = {letter: comb(alphabet + i, i + 1) for i, letter in enumerate(hs)}
            for x in X:
                for y in Y:
                    assert _cofactor_value(X, Y, x, y, alphabet) == cofactor(X, Y, x, y).subs(values)
    gate = control = parity = units = 0
    for v in range(3, VMAX + 1):
        for nx in range(1, v + 1):
            for XW in itertools.combinations(range(1, v), nx - 1):
                X = sorted(set(XW) | {v}, reverse=True)
                for ny in (nx,):
                    for YW in itertools.combinations(range(1, v), ny - 1):
                        Y = sorted(set(YW) | {0}, reverse=True)
                        if not _connected_flags(X, Y):
                            continue
                        for w in range(1, v):
                            d = v - w
                            height = lambda q: sum(y <= q for y in Y) - sum(x <= q for x in X)
                            if height(w) != 1 or height(d - 1) != 1:
                                continue
                            for tO in range(w + 1):
                                for sO in range(tO + 1, w + 1):
                                    for case in 'dc':
                                        if not recurrences(case, X, Y, v, w, d, tO, sO):
                                            continue
                                        for s in range(max(d, w + 1), v + 1):
                                            for t in range(0, min(w, d - 1) + 1):
                                                if s not in X or t not in Y:
                                                    continue
                                                if s - d in X and d + t in Y:
                                                    _check_parity(case, X, Y, s, t, d, tO, sO)
                                                    parity += 1
                                                    units += bool(set(X) & set(Y))
                                                eq = _cofactors_equal(X, Y, s - d, t, s, d + t)
                                                ok = inequality(case, s, t, d, tO, sO)
                                                if eq:
                                                    assert ok, (case, X, Y, w, tO, sO, s, t)
                                                    assert not (s == v and t == 0)
                                                    gate += 1
                                                elif not ok:
                                                    control += 1
    assert control > 0 and parity > 0 and units > 0
    print(f'ph:mixed-upper-sign: {gate} bounded subgate cases; '
          f'{parity} exact parity checks, {units} retaining shared-label units; '
          f'{control} violations without the cofactor equality')
    seen = set()
    geometric_equal = 0
    outers = [V for V in diagrams(5) if span(V) >= 3]
    for J in diagrams(8):
        for mu in marks(J):
            if mu.case != 'a' or not mu.lower:
                continue
            v = mu.width
            if v <= 1:
                continue
            s, t = phases(mu)
            XW, YW = betas(mu.lower)
            for V in outers:
                E = compose(V, mu)
                S = span(E)
                # A narrow upper has period span(E)-w, so only these end-cell displacements qualify.
                for cell in E:
                    if not 0 < S - content(cell) < v:
                        continue
                    try:
                        om = intersection_mark(E, cell)
                    except AssertionError:
                        continue
                    if om.case not in 'cd' or not legal(om):
                        continue
                    w = om.width
                    if not 0 < w < v:
                        continue
                    d = v - w
                    sO, tO = phases(om)
                    key = (om.case, tuple(XW), tuple(YW), w, s, t, sO, tO)
                    if key in seen:
                        continue
                    seen.add(key)
                    assert recurrences(om.case, XW, YW, v, w, d, tO, sO), key
                    geometric_equal += _cofactors_equal(XW, YW, s - d, t, s, d + t)
    print(f'geometry control: {len(seen)} classes satisfy the recurrences; '
          f'{geometric_equal} also satisfy the cofactor equality')
    print('ALL PASS')


if __name__ == '__main__':
    main()
