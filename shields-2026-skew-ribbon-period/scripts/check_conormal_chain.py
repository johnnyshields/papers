r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Ordered conormal chain of lem:conormal-caps (app:aligned), eq:ordered-conormal-chain.

For a bordered matrix M = [[w, h], [A, b]] with A upper block triangular, whose singular
diagonal blocks G_1, ..., G_e have corank one and whose other blocks are regular, the product of
the window numerators (left endpoint, consecutive links, right endpoint) equals, up to sign,
det M times the product of the proper corners kappa_i = det(G_i minus its first row and last
column).  Exact rational arithmetic; every random instance asserts the identity.
"""
import random
from fractions import Fraction

import sympy as sp


def rand_block(n, singular, rng):
    while True:
        B = sp.Matrix(n, n, lambda i, j: Fraction(rng.randint(-4, 4)))
        if singular:
            if n == 1:
                return sp.zeros(1, 1)
            c = [rng.randint(-3, 3) for _ in range(n - 1)]
            for j in range(n):
                B[n - 1, j] = sum(c[i] * B[i, j] for i in range(n - 1))
            return B
        if B.det() != 0:
            return B


def instance(types, sizes, rng):
    n = sum(sizes)
    A = sp.zeros(n, n)
    starts = []
    pos = 0
    for t, s in zip(types, sizes):
        starts.append(pos)
        A[pos:pos + s, pos:pos + s] = rand_block(s, t == "S", rng)
        for i in range(pos, pos + s):
            for j in range(pos + s, n):
                A[i, j] = rng.randint(-4, 4)
        pos += s
    w = [rng.randint(-4, 4) for _ in range(n)]
    b = [rng.randint(-4, 4) for _ in range(n)]
    h = rng.randint(-4, 4)
    # M: row 0 = (w, h); rows 1..n = (A, b); column n = border column
    M = sp.zeros(n + 1, n + 1)
    for j in range(n):
        M[0, j] = w[j]
        for i in range(n):
            M[i + 1, j] = A[i, j]
    M[0, n] = h
    for i in range(n):
        M[i + 1, n] = b[i]
    return M, starts


def minor(M, rows, cols):
    return M.extract(rows, cols).det()


def check(types, sizes, rng):
    M, starts = instance(types, sizes, rng)
    n = sum(sizes)
    blocks = [(st, st + s) for st, s in zip(starts, sizes)]
    sing = [k for k, t in enumerate(types) if t == "S"]
    # A-rows are M-rows 1 + i; A-cols are M-cols i
    rowsA = lambda k: [1 + i for i in range(*blocks[k])]
    colsA = lambda k: list(range(*blocks[k]))
    nums = []
    g1 = sing[0]
    rows = [0] + sum((rowsA(k) for k in range(g1)), []) + rowsA(g1)[1:]
    cols = sum((colsA(k) for k in range(g1 + 1)), [])
    nums.append(minor(M, rows, cols))
    for a, c in zip(sing, sing[1:]):
        rows = sum((rowsA(k) for k in range(a, c)), []) + rowsA(c)[1:]
        cols = colsA(a)[:-1] + sum((colsA(k) for k in range(a + 1, c + 1)), [])
        nums.append(minor(M, rows, cols))
    ge = sing[-1]
    rows = sum((rowsA(k) for k in range(ge, len(types))), [])
    cols = colsA(ge)[:-1] + sum((colsA(k) for k in range(ge + 1, len(types))), []) + [n]
    nums.append(minor(M, rows, cols))
    kap = [minor(M, rowsA(k)[1:], colsA(k)[:-1]) for k in sing]
    lhs = sp.prod(nums)
    rhs = M.det() * sp.prod(kap)
    assert lhs == rhs or lhs == -rhs, (types, sizes, lhs, rhs)
    return lhs != 0


def main():
    rng = random.Random(20261025)
    shapes = [
        ("S", ), ("RS", ), ("SR", ), ("RSR", ), ("SS", ), ("SRS", ), ("RSRSR", ),
        ("SSS", ), ("SRSRS", ), ("RSSR", ), ("SRRS", ),
    ]
    nonzero = 0
    total = 0
    for (pat,) in shapes:
        for _ in range(12):
            sizes = [rng.randint(1, 3) if t == "R" else rng.randint(2, 3) for t in pat]
            nonzero += check(list(pat), sizes, rng)
            total += 1
    assert nonzero > total // 2, (nonzero, total)
    print(f"conormal chain identity: {total} instances, {nonzero} with nonzero product; PASS")


if __name__ == "__main__":
    main()
