r"""Antitranspose of the transfer series (ph:transpose).

Paper section `app:cofaces` (Cofaces, two-copy identities, and native residues), ph:transpose.

Reading: for a connected diagram J of span N with beta lists X (rows, X_0 = N) and Y (columns,
0 in Y), letters h_0 = 1, h_1, ... (random rationals), e the conjugate letters (sum e_j z^j =
1/H(-z)), G = 1 - sum_s (T^{-1}(h_i)_{i in I})_s z^s the right coframe, P = [HG]_{<N}, C the right
coframe of the half-turn, Q = [HC]_{<N}, and I(f)(z) = iota(f(-z)) with iota(h_j) = e_j, i.e.
I(f) has coefficients (-1)^a f_a evaluated at the letters e.  For every connected J up to CELLS
cells, with J^dagger its antitranspose:

* the flags of J^dagger are X^dagger = (0, N] minus Y and Y^dagger = [0, N) minus X;
* I(H) = 1/H;
* G^dagger = I(P), P^dagger = I(G), C^dagger = I(Q), Q^dagger = I(C) coefficientwise (the left
  side computed at the letters h on the flags of J^dagger, the right side at the letters e on
  the flags of J), exact at random rational letters;
* the control: without the alternating sign in I(f) the first identity fails on many J.

Uncovered: the returned normalization g^dagger, the clock R_0^dagger, the opposite-field indices
s* = v - t, and the transport of the child comparison with its primitive sign.
"""
import random
from fractions import Fraction

import sympy as sp
from sympy.matrices.exceptions import NonInvertibleMatrixError

from _gluing_common import antitranspose
from check_two_copy_flags import betas, diagrams

CELLS = 8
rng = random.Random(9)


def series_inverse(a, n):
    out = [Fraction(1) / a[0]]
    for k in range(1, n):
        out.append(-sum(a[i] * out[k - i] for i in range(1, k + 1) if i < len(a)) / a[0])
    return out


def coframe(letter, X, Y):
    N = X[0]
    I, S = X[1:], Y[:-1]
    G = [sp.Integer(1)] + [sp.Integer(0)] * (N - 1)
    if I:
        T = sp.Matrix(len(I), len(S), lambda i, j: sp.Rational(letter(I[i] - S[j])))
        sol = T.solve(sp.Matrix([sp.Rational(letter(i)) for i in I]))
        for s, val in zip(S, sol):
            G[s] = -val
    return G


def clip_product(a, b, n):
    return [sum(a[i] * b[k - i] for i in range(k + 1) if i < len(a) and k - i < len(b))
            for k in range(n)]


def main():
    tested = nonconst = unsigned = 0
    for J in diagrams(CELLS):
        X, Y = betas(J)
        N = X[0]
        Jd = antitranspose(J)
        Xd, Yd = betas(Jd)
        assert Xd == sorted(set(range(1, N + 1)) - set(Y), reverse=True), sorted(J)
        assert Yd == sorted(set(range(0, N)) - set(X), reverse=True), sorted(J)
        hv = [Fraction(1)] + [Fraction(rng.randint(1, 6), rng.randint(1, 3)) for _ in range(2 * N + 2)]
        H = lambda n, hv=hv: hv[n] if n >= 0 else Fraction(0)  # noqa: E731
        negH = [hv[n] * (-1) ** n for n in range(len(hv))]
        ev = series_inverse(negH, len(hv))
        assert clip_product(hv, [ev[n] * (-1) ** n for n in range(len(ev))], N + 1) == [1] + [0] * N
        Ee = lambda n, ev=ev: ev[n] if n >= 0 else Fraction(0)  # noqa: E731
        Xr, Yr = rotate_flags(X, Y)
        Xdr, Ydr = rotate_flags(Xd, Yd)
        try:
            Gd = coframe(H, Xd, Yd)
            Cd = coframe(H, Xdr, Ydr)
            Ge = coframe(Ee, X, Y)
            Ce = coframe(Ee, Xr, Yr)
        except NonInvertibleMatrixError:
            continue
        Ev = [sp.Rational(ev[n]) for n in range(len(ev))]
        Hv = [sp.Rational(hv[n]) for n in range(len(hv))]
        Pe = clip_product(Ev, Ge, N)
        Qe = clip_product(Ev, Ce, N)
        Pd = clip_product(Hv, Gd, N)
        Qd = clip_product(Hv, Cd, N)
        sign = [(-1) ** a for a in range(N)]
        assert Gd == [sign[a] * Pe[a] for a in range(N)], sorted(J)
        assert Pd == [sign[a] * Ge[a] for a in range(N)], sorted(J)
        assert Cd == [sign[a] * Qe[a] for a in range(N)], sorted(J)
        assert Qd == [sign[a] * Ce[a] for a in range(N)], sorted(J)
        tested += 1
        if any(g != 0 for g in Ge[1:]):
            nonconst += 1
            unsigned += Gd != Pe
    print(f'diagrams tested: {tested}, with nonconstant G: {nonconst}')
    assert tested > 100 and nonconst > 50 and unsigned > 50
    print('ALL PASS')


def rotate_flags(X, Y):
    N = X[0]
    return sorted((N - y for y in Y), reverse=True), sorted((N - x for x in X), reverse=True)


if __name__ == '__main__':
    main()
