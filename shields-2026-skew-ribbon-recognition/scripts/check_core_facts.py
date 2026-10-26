"""The zero-free core and the replaced boards of the first-grade proof (ph:first-grade).

Paper section `app:physical` (Whole currents and the first complete grade), proof of ph:first-grade.

For every connected normalized diagram of span M (3 <= M <= MMAX) with beta lists (X, Y), remove
the common flags I = X n Y, leaving the core lists (X_B, Y_B) of rank q, and check:

* the core is a connected zero-free diagram of span M: it keeps the top row M and the bottom
  column 0, Y_B[i] < X_B[i] and Y_B[i] < X_B[i+1] (sorted decreasingly), and no core row equals a
  core column;
* the proper corner (X_B minus M, Y_B minus 0) is a feasible board;
* for every common flag z, the boards with the column 0 replaced by z, and with the row M
  replaced by z, are feasible.

A zero-free board det(x_{u_i - v_j}), x_0 = 0, is nonzero exactly when the sorted lists satisfy
v_i < u_i (`xBoard_det_ne_zero`, `colReplaced_det_ne_zero`, `rowReplaced_det_ne_zero` in the
Lean tree); the criterion is itself checked against the determinant on every board of span at
most 5.
"""
import itertools
from math import comb
import sys

import sympy as sp

MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 9

xs = sp.symbols('x1:20')


def profiles(M):
    """Connected normalized beta pairs of span M: rows in (0, M] with M, columns in [0, M) with 0."""
    out = []
    for xm in range(1 << (M - 1)):
        X = [M] + [k for k in range(M - 1, 0, -1) if xm >> (k - 1) & 1]
        for ym in range(1 << (M - 1)):
            Y = [k for k in range(M - 1, 0, -1) if ym >> (k - 1) & 1] + [0]
            if len(X) != len(Y):
                continue
            n = len(X)
            if all(Y[i] < X[i] for i in range(n)) and all(Y[i] <= X[i + 1] for i in range(n - 1)):
                out.append((tuple(X), tuple(Y)))
    return out


def feasible(u, v):
    u = sorted(u, reverse=True)
    v = sorted(v, reverse=True)
    return len(u) == len(v) and all(v[i] < u[i] for i in range(len(u)))


def board_det(u, v):
    def x(k):
        return 0 if k <= 0 else xs[k - 1]
    return sp.expand(sp.Matrix(len(u), len(u), lambda i, j: x(u[i] - v[j])).det())


# The feasibility criterion against the determinant, on all boards with entries in [0, 5].
tested = 0
for n in range(1, 4):
    for u in itertools.combinations(range(6), n):
        for v in itertools.combinations(range(6), n):
            if set(u) & set(v):
                continue
            assert (board_det(u, v) != 0) == feasible(u, v), (u, v)
            tested += 1
print(f'feasibility criterion agrees with the determinant on {tested} disjoint boards')

for M in range(3, MMAX + 1):
    cnt = replaced = 0
    for xi, ze in profiles(M):
        common = set(xi) & set(ze)
        X = sorted(set(xi) - common, reverse=True)
        Y = sorted(set(ze) - common, reverse=True)
        q = len(X)
        assert len(Y) == q and X[0] == M and Y[-1] == 0, (xi, ze)
        assert all(Y[i] < X[i] for i in range(q)), ('core not a beta diagram', xi, ze)
        assert all(Y[i] < X[i + 1] for i in range(q - 1)), ('core not connected', xi, ze)
        assert not set(X) & set(Y)
        assert feasible(X[1:], Y[:-1]), ('proper corner infeasible', xi, ze)
        for z in common:
            assert feasible(X, Y[:-1] + [z]), ('column-replaced board infeasible', xi, ze, z)
            assert feasible(X[1:] + [z], Y), ('row-replaced board infeasible', xi, ze, z)
            replaced += 2
        cnt += 1
    assert cnt == comb(2 * M, M) // (M + 1), (M, cnt)  # Catalan: connected diagrams of span M
    print(f'M = {M}: {cnt} connected diagrams, {replaced} replaced boards, all feasible')
print('check_core_facts: PASS')
