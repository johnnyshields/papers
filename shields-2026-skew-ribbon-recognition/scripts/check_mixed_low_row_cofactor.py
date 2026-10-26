"""The first-order mixed row response as a two-period cofactor.

Paper section `sec:comparison` (Finite comparisons on actual composition charts), ph:mixed-native (the row reader
at a low mark row b < v), with the flags of ph:mixed-flags.

With the native rows B = X_W + B_- and columns C = (Y_W - {t}) + C_- + {s}, and
D(u) = sum_n u^n D_n, (D_n)_{x,y} = h_{n r + x - y}, the row l = e_s^T D(u)^{-1} has

    [u^1] l_b = -(D_0^{-1} D_1 D_0^{-1})_{s, b}.

The two-period board M = JT(B + (r + B), C + (r + C)) is block lower triangular with diagonal blocks
D_0 and off-diagonal block D_1, so [u^1] l_b = (M^{-1})_{r + s, b}: a signed cofactor,

    [u^1] l_b = (-1)^(pos(r + s) + pos(b)) det JT(R2, C2) / det M,
    R2 = (B + (r + B)) - {b},   C2 = (C + (r + C)) - {r + s},

with positions in the decreasing lists and det M = det(D_0)^2.  A Jacobi-Trudi determinant of
strictly decreasing lists is a skew Schur function, nonzero exactly when the lists interlace
(C2_i <= R2_i).  The interlacing is automatic: (B, C) interlace, threshold counts add over the
two periods, and deleting a row b below the deleted column r + s lowers the row count only on
thresholds where the column count drops too.  The script asserts the cofactor identity at random
rational letters, the interlacing of (B, C), of the two-period board and of every deletion at a
native row b, and the nonvanishing, on every legal case (d) flag set; it reports the low mark rows
b < v at t > 0 separately.
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


def interlaced(rows, cols):
    return len(rows) == len(cols) and all(c <= r for r, c in zip(rows, cols))


def check(r, v, XW, YW, s, t, Bm, Cm, seed):
    rnd = random.Random(seed)
    hv = {n: Rational(rnd.randint(-9, 9), rnd.randint(1, 5)) for n in range(4 * r + 4)}
    hv[0] = Rational(1)
    h = lambda n: hv[n] if n >= 0 else 0  # noqa: E731
    dec = lambda L: sorted(L, reverse=True)  # noqa: E731
    B = dec(XW + Bm)
    C = dec([y for y in YW if y != t] + Cm + [s])
    D0 = jt(h, B, C)
    if D0.det() == 0:
        return None
    D1 = jt(h, [x + r for x in B], C)
    D0i = D0.inv()
    l1 = -(D0i * D1 * D0i)
    R2full = dec(B + [r + x for x in B])
    C2full = dec(C + [r + y for y in C])
    M = jt(h, R2full, C2full)
    assert M.det() == D0.det() ** 2
    assert interlaced(B, C) and interlaced(R2full, C2full)
    out = {}
    for b in B:
        val = l1[C.index(s), B.index(b)]
        R2 = [x for x in R2full if x != b]
        C2 = [y for y in C2full if y != r + s]
        sign = (-1) ** (R2full.index(b) + C2full.index(r + s))
        assert val == sign * jt(h, R2, C2).det() / M.det(), ("cofactor", b)
        nz = val != 0
        for extra in range(1, 4):
            if nz:
                break
            rx = random.Random(10 ** 6 + 97 * seed + extra)
            hx = {n: Rational(rx.randint(-30, 30), rx.randint(1, 7)) for n in range(4 * r + 4)}
            hx[0] = Rational(1)
            nz = jt(lambda n: hx[n] if n >= 0 else 0, R2, C2).det() != 0  # noqa: B023
        out[b] = (nz, interlaced(R2, C2))
        assert nz or not out[b][1], ("interlaced but zero", b, B, C, R2, C2)
    return out


def main():
    seen = set()
    rows_tpos = [0, 0, 0]  # low rows checked, interlaced, nonzero
    all_rows = [0, 0]  # native rows checked, nonzero
    fails = []
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
            out = None
            for seed in range(5):
                out = check(r, v, XW, YW, s, t, Bm, Cm, seed)
                if out is not None:
                    break
            assert out is not None, key
            for b, (nz, il) in out.items():
                assert il, ("deletion breaks interlacing", key, b)
                all_rows[0] += 1
                all_rows[1] += nz
                if t == 0 or b not in XW or b >= v:
                    continue
                rows_tpos[0] += 1
                rows_tpos[1] += il
                rows_tpos[2] += nz
                if not il and len(fails) < 5:
                    fails.append((key, b))
    print(f"t > 0 low mark rows: {rows_tpos[0]}, interlaced: {rows_tpos[1]}, "
          f"nonzero at a random point: {rows_tpos[2]}")
    print(f"all native rows, both signs of t: {all_rows[0]}, nonzero: {all_rows[1]}")
    assert all_rows[0] == all_rows[1]
    for f in fails:
        print("  not interlaced:", f)
    assert rows_tpos[0] > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
