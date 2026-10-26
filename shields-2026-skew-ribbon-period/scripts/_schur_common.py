"""Exact skew Schur functions at a rational point of the alphabet, shared by the composition checks.

Skew diagrams are sets of cells `(i, j)` (row increasing southward, `content = j - i`); a Schur
function is the product over edge-connected components of the Jacobi--Trudi determinant of the
component's row intervals, evaluated with `fractions.Fraction`.  The alphabet is a fixed seeded
choice of rational values `h_1, h_2, ...` with `h_0 = 1`, `h_j = 0` for `j < 0`.
"""
import random
from fractions import Fraction

from check_regroup_mixed import E_CELL, add


def alphabet(seed):
    rng = random.Random(seed)
    values = {j: Fraction(rng.randint(2, 40), rng.randint(1, 9)) for j in range(1, 120)}

    def h(j):
        return Fraction(1) if j == 0 else (Fraction(0) if j < 0 else values[j])
    return h


def components(D):
    D = set(D)
    out = []
    while D:
        s = next(iter(D))
        seen = {s}
        stack = [s]
        while stack:
            x = stack.pop()
            for d in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                y = add(x, d)
                if y in D and y not in seen:
                    seen.add(y)
                    stack.append(y)
        out.append(frozenset(seen))
        D -= seen
    return out


def determinant(M):
    n = len(M)
    M = [r[:] for r in M]
    d = Fraction(1)
    for i in range(n):
        p = next((r for r in range(i, n) if M[r][i] != 0), None)
        if p is None:
            return Fraction(0)
        if p != i:
            M[i], M[p] = M[p], M[i]
            d = -d
        d *= M[i][i]
        for r in range(i + 1, n):
            f = M[r][i] / M[i][i]
            for c in range(i, n):
                M[r][c] -= f * M[i][c]
    return d


def row_intervals(C):
    rows = sorted({x[0] for x in C})
    a = [min(x[1] for x in C if x[0] == i) for i in rows]
    b = [max(x[1] for x in C if x[0] == i) + 1 for i in rows]
    return a, b


def jt(C, h):
    """Jacobi--Trudi determinant of one connected component with generator function `h`."""
    a, b = row_intervals(C)
    n = len(a)
    return determinant([[h(b[i] - a[j] - i + j) for j in range(n)] for i in range(n)])


def schur(S, h):
    out = Fraction(1)
    for C in components(S):
        out *= jt(C, h)
    return out


def minus(S):
    """`S^- = {x in S : x + (1, 1) in S}`."""
    return frozenset(x for x in S if add(x, E_CELL) in S)
