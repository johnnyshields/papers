r"""Paper section `app:coincident` (Positive coincident attachment phases).

Check for `lem:coincident-reader` (app:coincident, eq:marked-floor, eq:coincident-full-flags):
at a sampled physical specialization (h_0 = 1, low h_m for 0 < m < g random rationals,
ports x_d for d >= 1, all other high h zero) the top matrix of the full source, its marked
block (the bordered band matrix) and every private block have nonzero determinant, and
det(top) = +-det(marked) * prod det(private)."""
import itertools
import random
from fractions import Fraction

import sympy

random.seed(7)
g, u, tau, L = 6, 4, 2, 4
J = [4, 3]
K = [1, 0]
priv_I = [[5], [5, 3 + 2], [], [5]]  # private rows by band (residues in (u, g)), padded below
# private records: row residues I_i, column residues C_i, equal count; use sets in (u, g) = {5}
priv = [([5], [5]), ([5], [5]), ([], []), ([5], [5])]
assert len(priv) == L


def hn(m, lo, x):
    if m == 0:
        return Fraction(1)
    if m < g:
        return lo[m]
    if m % g == u:
        return x.get(m // g, Fraction(0))
    return Fraction(0)


def topE(b, c, lo, x):
    if b < c or b % g < c % g:
        return Fraction(0)
    return hn(b - c, lo, x)


def det(rows, cols, lo, x):
    M = sympy.Matrix([[sympy.Rational(topE(b, c, lo, x).numerator, topE(b, c, lo, x).denominator)
                       for c in cols] for b in rows])
    return M.det()


for trial in range(5):
    lo = {m: Fraction(random.randint(1, 9), random.randint(1, 9)) for m in range(1, g)}
    x = {d: Fraction(random.randint(1, 9), random.randint(1, 9)) for d in range(1, L + 2)}
    rows, cols = [L * g + tau], [tau]
    marked_r, marked_c = [L * g + tau], [tau]
    for i in range(L):
        marked_r += [i * g + j for j in J]
        marked_c += [i * g + k for k in K]
        rows += [i * g + j for j in J] + [i * g + r for r in priv[i][0]]
        cols += [i * g + k for k in K] + [i * g + c for c in priv[i][1]]
    marked_r += [L * g + j for j in J]
    marked_c += [L * g + k for k in K]
    rows += [L * g + j for j in J]
    cols += [L * g + k for k in K]
    # marked block pairs rows and columns in the order above
    assert len(rows) == len(cols)
    D = det(rows, cols, lo, x)
    Dm = det(marked_r, marked_c, lo, x)
    Dp = sympy.Integer(1)
    for i in range(L):
        d = det([i * g + r for r in priv[i][0]], [i * g + c for c in priv[i][1]], lo, x)
        assert d != 0
        Dp *= d
    assert Dm != 0 and D != 0
    assert D == Dm * Dp or D == -Dm * Dp, (D, Dm, Dp)
print("PASS check_clock_top_unit")
