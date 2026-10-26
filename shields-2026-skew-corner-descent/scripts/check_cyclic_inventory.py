#!/usr/bin/env python3
"""Exact checks of cyclic multiplicities, dual identities, and retained jets.

Window products are enumerated by start; the alternate formulas use only class
counts and complements.  A small symbolic inverse checks the raw/chart chain
rule and the nonzero jet of an entry whose residue is zero.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, prod
import sympy as sp


def inverse_windows(word, length, values):
    return sum((1 / prod(values[word[(i + j) % len(word)]] for j in range(length)) for i in range(len(word))), F(0))


def run():
    checked = automatic = 0
    for b in range(3, 10):
        for v in range(1, b - 1):
            if gcd(b, v) != 1:
                continue
            d = b - v
            k, s = divmod(b, d)
            for r in range(1, 4):
                n, B, C, m = r * d, r * b, r * v, r * s
                # Dependent plane values, not independent tagged variables.
                for offset in range(3):
                    P = tuple((i * i + offset * i + 1) % 3 for i in range(n))
                    R = P[:m - 1]
                    word = P * k + R
                    assert len(word) == B - 1
                    counts, prefix = Counter(P), Counter(R)
                    exponents = {c: s * counts[c] - d * prefix[c] for c in range(3)}
                    assert sum(exponents.values()) == d
                    for anchor, cap_product in ((F(11), F(2)), (F(13), F(3))):
                        values = {c: anchor - c * cap_product for c in range(3)}
                        AP, DR, T = prod(values[c] for c in P), prod(values[c] for c in R), prod(values[c] for c in word)
                        LS = sum((F(exponents[c], 1) / values[c] for c in range(3)), F(0))
                        def N(j):
                            return b * inverse_windows(P, j, values) - sum((exponents[c] * inverse_windows(word + (c,), j, values) for c in range(3)), F(0))
                        HC = sum((prod(values[P[(i + j) % n]] for j in range(C)) for i in range(n)), F(0))
                        assert N(n) == F(n * d, 1) / AP - LS * HC / T
                        assert N(m) == s * inverse_windows(P, m, values) - m * LS / DR
                        assert N(B) == F(b, s) * AP ** (-k) * N(m)
                        for c in range(3):
                            assert inverse_windows(word + (c,), B, values) == F(B, 1) / (T * values[c])
                        if r == 1 and s == 1:
                            assert N(1) == N(B) == 0
                            automatic += 1
                        checked += 1
    # Exact square-unit inverse: a residue-zero entry has live higher jets.
    h1, h2, t = sp.symbols('h1 h2 t')
    matrix = sp.Matrix([[h2, t], [h1, h2]])
    entry = matrix.inv()[0, 1]
    assert entry.subs(t, 0) == 0
    assert sp.diff(entry, t).subs(t, 0) == -1 / h2**2
    assert sp.diff(entry, t, 2).subs(t, 0) / 2 == -h1 / h2**4
    # Differentiate an actual Schur complement in raw coordinates, not the
    # already differentiated profile formula.
    hs = sp.symbols('h0:11')
    xs, ys = [10, 7, 4], [3, 1, 0]
    Pmat = sp.Matrix([[hs[xs[i] - ys[j]] for j in (0, 1)] for i in (1, 2)])
    row = sp.Matrix([[hs[xs[0] - ys[j]] for j in (0, 1)]])
    col = sp.Matrix([hs[xs[i] - ys[2]] for i in (1, 2)])
    response = hs[10] - (row * Pmat.inv() * col)[0]
    z = sp.Symbol('z')
    left = row * Pmat.inv()
    right = Pmat.inv() * col
    A = 1 - sum(left[i] * z**(xs[0] - xs[i + 1]) for i in range(2))
    Bprof = 1 - sum(right[j] * z**(ys[j] - ys[2]) for j in range(2))
    for j in range(1, 11):
        coeff = sp.expand(A * Bprof).coeff(z, 10 - j)
        assert sp.cancel(sp.diff(response, hs[j]) - coeff) == 0
    bvar = sp.Symbol('b')
    assert sp.expand(bvar**2 - (bvar - 2)**2 - 2 * (2 * bvar - 2)) == 0
    assert sp.expand(bvar * (bvar - 1) - (bvar - 2) * (bvar - 3) - 2 * (2 * bvar - 3)) == 0
    print('PASS cyclic inventories:', checked, '; automatic last-detector zeros:', automatic)
    print('PASS full inverse jets, ten raw profile derivatives, and both n=2 inventories')


if __name__ == '__main__':
    run()
