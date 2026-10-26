#!/usr/bin/env python3
"""The raw and chart derivatives of an interval response in endpoint profiles.

Paper section `sec:one-active` (Endpoint profiles and the actual closure); target
`lem:profile-derivative`.

An interval response S = h_K - r P^{-1} c is built from endpoint lists x, y with every
index of the removed matrix P an h-variable.  All generators take independent exact
rational values except the one differentiated (and t, below), so the derivative is
taken of an exact rational function of one or two symbols.  Asserted for several index
configurations, including repeated indices inside P and the largest generator
inside P: dS/dh_j equals [z^{K-j}] A B for every j <= K, with the profiles A and B of the
statement; with h_N = (t - c0)/a0 for psi = a0 h_N + c0, a0 and c0 polynomial in the
lower generators, a0 * d_t S equals [z^{K-N}] A B; and for every lower generator the raw
derivative equals the chart derivative plus (d_t S)(d_j psi).  Control: omitting
the internal dP term breaks the profile identity.
"""
from fractions import Fraction as Fr
import random
import sympy as sp

CONFIGS = [
    ((10, 7, 4), (3, 1, 0), 4),
    ((12, 9, 5, 2), (4, 3, 1, 0), 4),
    ((9, 6, 4, 1), (3, 2, 0, -1), 3),
    ((14, 11, 7, 6, 2), (5, 4, 2, 1, 0), 5),
]


def assemble(xs, ys, value):
    n = len(xs)
    P = sp.Matrix(n-1, n-1, lambda i, j: value(xs[i+1]-ys[j]))
    row = sp.Matrix(1, n-1, lambda _, j: value(xs[0]-ys[j]))
    col = sp.Matrix(n-1, 1, lambda i, _: value(xs[i+1]-ys[n-1]))
    return P, row, col


def main():
    rng = random.Random(5)
    z, t, s = sp.symbols('z t s')
    for xs, ys, N in CONFIGS:
        n = len(xs)
        K = xs[0]-ys[-1]
        base = {k: sp.Rational(rng.randint(1, 9), rng.randint(1, 5)) for k in range(1, K+1)}

        def value_with(var, j):
            def value(k):
                if k < 0:
                    return sp.Integer(0)
                if k == 0:
                    return sp.Integer(1)
                return var if k == j else base[k]
            return value

        for j in range(1, K+1):
            value = value_with(s, j)
            P, row, col = assemble(xs, ys, value)
            Pinv = P.inv()
            S = value(K)-(row*Pinv*col)[0]
            # profiles with the same values, evaluated at s = base[j]
            point = {s: base[j]}
            Pn, rown, coln = assemble(xs, ys, value_with(base[j], j))
            Pninv = Pn.inv()
            A = 1-sum((rown*Pninv)[i]*z**(xs[0]-xs[i+1]) for i in range(n-1))
            B = 1-sum((Pninv*coln)[i]*z**(ys[i]-ys[n-1]) for i in range(n-1))
            AB = sp.expand(A*B)
            derivative = sp.diff(S, s).subs(point)
            assert sp.simplify(derivative-AB.coeff(z, K-j)) == 0, (xs, ys, j)
            if j < K:
                # control: omit the internal dP term
                partial = -((sp.diff(row, s)*Pinv*col)[0]+(row*Pinv*sp.diff(col, s))[0])
                if any(sp.diff(P, s)[a, b] != 0 for a in range(n-1) for b in range(n-1)):
                    assert sp.simplify(partial.subs(point)-AB.coeff(z, K-j)) != 0
        # chart: psi = a0 h_N + c0 with lower generators h_1..h_{N-1}
        lower = {k: base[k] for k in range(1, N)}
        a0 = lambda lo: 1+lo[1]*lo[2]+lo[N-1]
        c0 = lambda lo: lo[1]**2+lo[2]*lo[N-1]+2
        assert N >= 3

        def S_of(lo, hN):
            def value(k):
                if k < 0:
                    return sp.Integer(0)
                if k == 0:
                    return sp.Integer(1)
                if k < N:
                    return lo[k]
                if k == N:
                    return hN
                return base[k]
            P, row, col = assemble(xs, ys, value)
            return value(K)-(row*P.inv()*col)[0]

        hN = sp.Symbol('hN')
        Sraw = S_of(lower, hN)
        # a0 * d_t S at fixed lower generators is d_{h_N} S
        a_value, c_value = a0(lower), c0(lower)
        point = {hN: sp.Rational(7, 3)}
        Pn_, row_, col_ = assemble(xs, ys, lambda k: 0 if k < 0 else 1 if k == 0 else (lower[k] if k < N else point[hN] if k == N else base[k]))
        Pi = Pn_.inv()
        A = 1-sum((row_*Pi)[i]*z**(xs[0]-xs[i+1]) for i in range(n-1))
        B = 1-sum((Pi*col_)[i]*z**(ys[i]-ys[n-1]) for i in range(n-1))
        AB = sp.expand(A*B)
        dS_dhN = sp.diff(Sraw, hN).subs(point)
        # t = psi, so d_t = (1/a0) d_{h_N}
        assert sp.simplify(a_value*(dS_dhN/a_value)-AB.coeff(z, K-N)) == 0
        # lower generators: raw derivative = chart derivative + (d_t S)(d_j psi)
        for k in range(1, N):
            gen = sp.Symbol('g')
            lo = dict(lower)
            lo[k] = gen
            hN_chart = (t-c0(lo))/a0(lo)
            S_chart = S_of(lo, hN_chart)
            S_raw = S_of(lo, hN)
            psi = a0(lo)*hN+c0(lo)
            t_value = (a0(lower)*point[hN]+c0(lower))
            at = {gen: lower[k], t: t_value}
            raw = sp.diff(S_raw, gen).subs({gen: lower[k], hN: point[hN]})
            chart = sp.diff(S_chart, gen).subs(at)
            d_t = sp.diff(S_chart, t).subs(at)
            dpsi = sp.diff(psi, gen).subs({gen: lower[k], hN: point[hN]})
            assert sp.simplify(raw-(chart+d_t*dpsi)) == 0, (xs, ys, k)
            assert sp.simplify(d_t*a0(lower)-dS_dhN) == 0
        print('PASS configuration', xs, ys, 'K =', K, 'N =', N, flush=True)
    print('check_profile_derivative: PASS')


if __name__ == '__main__':
    main()
