#!/usr/bin/env python3
"""Paper section 4 (Gram structure and the exceptional matrix M_1), sec:gram,
Figure 1 (fig:det-M1) and Lemma 4.3 (lem:M1-indefinite).

Verifies every claim the figure and its caption make about

    f(a) = (4a-1) psi_1(a) - 4,        det M_1 = f(a) / (4 a^2),

and emits the pgfplots coordinate block that the figure inlines:

  * eq:det-M1, by an independent route: det M_1 = psi_1(a+1) - g beta_1^2 with
    g = psi_1(a) and beta_1 = (2a-1)/(2a), against the closed form f(a)/(4a^2);
  * the exact endpoint values f(1/4) = -4 and f(1/2) = pi^2/2 - 4 that fix the
    plotted window [1/4, 1/2];
  * f' > 0 on (0, 1/2) from the series f'(a) = 2 sum_r (2r+1-2a)/(a+r)^3,
    cross-checked against a numerical derivative, so the crossing shown is unique;
  * the threshold a_* = 0.3690738484..., and the sign of f on either side of it;
  * the inertia trichotomy of lem:M1-indefinite read off the eigenvalues of M_1;
  * that no sampled point falls outside the declared axis limits (nothing clipped).

Numerical work is mpmath at arbitrary precision.  Run with no arguments to check
only; run with --emit to also print the coordinate block to stdout.
"""

import sys

from mpmath import mp

mp.dps = 40

# Plot window and sampling, as declared in the figure's axis options.
A_LO = mp.mpf(1) / 4
A_HI = mp.mpf(1) / 2
Y_MIN = mp.mpf('-4.35')
Y_MAX = mp.mpf('1.6')
N_SAMPLES = 101

# The threshold quoted in the caption and in verify_determinant.py.
A_STAR_QUOTED = mp.mpf('0.3690738484')


def g(a):
    return mp.psi(1, a)


def f(a):
    """The sign-carrying factor of det M_1."""
    a = mp.mpf(a)
    return (4 * a - 1) * g(a) - 4


def det_m1_closed(a):
    """det M_1 by the closed form of eq:det-M1."""
    a = mp.mpf(a)
    return f(a) / (4 * a**2)


def m1_matrix(a):
    """M_1 at the sharp endpoint kappa = 1, from eq:matrix-series."""
    a = mp.mpf(a)
    beta_1 = (2 * a - 1) / (2 * a)
    off = mp.sqrt(g(a)) * beta_1
    return mp.matrix([[mp.psi(1, a + 1), off], [off, mp.mpf(1)]])


def det_m1_gram(a):
    """det M_1 by the Gram route: psi_1(a+1) - g beta_1^2."""
    a = mp.mpf(a)
    beta_1 = (2 * a - 1) / (2 * a)
    return mp.psi(1, a + 1) - g(a) * beta_1**2


def f_prime_series(a):
    """f'(a) = 2 sum_{r>=0} (2r+1-2a)/(a+r)^3, the form used in the lemma."""
    a = mp.mpf(a)
    return 2 * mp.nsum(lambda r: (2 * r + 1 - 2 * a) / (a + r) ** 3, [0, mp.inf])


# --- eq:det-M1: two independent routes to det M_1 -------------------------
for a in ['0.05', '0.2', '0.25', '0.3690738484', '0.5', '1', '2.5', '7']:
    a = mp.mpf(a)
    lhs, rhs = det_m1_gram(a), det_m1_closed(a)
    assert abs(lhs - rhs) <= mp.mpf('1e-30') * max(1, abs(rhs)), a
    assert abs(mp.det(m1_matrix(a)) - rhs) <= mp.mpf('1e-30') * max(1, abs(rhs)), a
print('PASS: det M_1 = psi_1(a+1) - g beta_1^2 = ((4a-1)g-4)/(4a^2),'
      ' Gram route vs closed form vs the 2x2 determinant')

# --- exact endpoint values that fix the plotted window --------------------
assert abs(f(A_LO) - (-4)) <= mp.mpf('1e-30')
assert abs(f(A_HI) - (mp.pi**2 / 2 - 4)) <= mp.mpf('1e-30')
assert f(A_HI) > 0
# det M_1 = f/(4a^2) has the same sign, and equals f at a = 1/2.
assert abs(det_m1_closed(A_LO) - (-16)) <= mp.mpf('1e-30')
assert abs(det_m1_closed(A_HI) - f(A_HI)) <= mp.mpf('1e-30')
print('PASS: f(1/4) = -4, f(1/2) = pi^2/2 - 4 = '
      f'{mp.nstr(f(A_HI), 12)} > 0, det M_1(1/4) = -16')

# --- f' > 0 on (0, 1/2): the crossing shown is the only one ---------------
for a in ['0.01', '0.05', '0.1', '0.25', '0.3690738484', '0.45', '0.499']:
    a = mp.mpf(a)
    series = f_prime_series(a)
    numeric = mp.diff(f, a)
    assert abs(series - numeric) <= mp.mpf('1e-25') * max(1, abs(series)), a
    assert series > 0, a
print('PASS: f\'(a) = 2 sum (2r+1-2a)/(a+r)^3 > 0 on (0,1/2), series = numeric diff')

# --- the threshold a_* ----------------------------------------------------
a_star = mp.findroot(f, mp.mpf('0.37'))
assert A_LO < a_star < A_HI
# Pin the digits the paper actually prints.  A tolerance test is too weak here:
# |a_* - 0.3690738484| = 1.15e-11 but |a_* - 0.3690738485| = 8.85e-11, so any
# tolerance of 1e-10 or looser accepts a wrong final digit.  Round instead.
assert mp.nstr(a_star, 10) == '0.3690738484', mp.nstr(a_star, 20)   # Lemma 4.3
assert mp.nstr(a_star, 8) == '0.36907385', mp.nstr(a_star, 20)      # figure literals
assert f(a_star * (1 - mp.mpf('1e-8'))) < 0 < f(a_star * (1 + mp.mpf('1e-8')))
print(f'PASS: a_* = {mp.nstr(a_star, 20)} in (1/4,1/2), exact to the 10 places quoted')

# The figure hard-codes a_* in three places the emitted curve does not cover: the
# dashed vertical, the marker dot, and the node label.  Without this, --emit could
# refresh the curve while the crossing marker silently stayed put.
for literal in ('0.36907385', '0.3690738484'):
    lit = mp.mpf(literal)
    assert abs(f(lit)) < mp.mpf('1e-7'), (literal, mp.nstr(f(lit), 8))
print('PASS: the figure\'s inlined a_* literals 0.36907385 and 0.3690738484 sit on the curve')

# f(a) -> -infty as a -> 0 is the caption's implicit reason the crossing is unique
# from below.  The actual law is a^2 f(a) -> -1 (the r=0 term of psi_1 dominates);
# assert the law on a ladder rather than a single inequality.
for e in (4, 6, 8):
    aa = mp.mpf(10)**(-e)
    assert abs(aa**2 * f(aa) + 1) < mp.mpf('1e-3'), (e, mp.nstr(aa**2*f(aa), 10))
    assert f(aa) < -mp.mpf(10)**(2*e - 1)
print('PASS: a^2 f(a) -> -1 as a -> 0, so f -> -infty')

# The (0,1/2) restriction on f' > 0 is load-bearing, not a convenience: f is NOT
# monotone on (0,infty), so Lemma 4.3 cannot get uniqueness of a_* from monotonicity
# alone and must route a >= 1/2 through Theorem 4.2.
for a in ('0.1', '0.3', '0.499'):
    assert f_prime_series(mp.mpf(a)) > 0, a
for a in ('0.7', '1', '5'):
    assert f_prime_series(mp.mpf(a)) < 0, a
print('PASS: f\' > 0 on (0,1/2) but f\'(0.7) < 0, so the interval hypothesis is load-bearing')

# --- inertia trichotomy of lem:M1-indefinite, from the eigenvalues --------
for a, expected in [('0.05', 'indefinite'), ('0.2', 'indefinite'),
                    ('0.35', 'indefinite'), ('0.4', 'definite'),
                    ('0.5', 'definite'), ('3', 'definite')]:
    ev = mp.eigsy(m1_matrix(mp.mpf(a)), eigvals_only=True)
    lo, hi = min(ev), max(ev)
    if expected == 'indefinite':
        assert lo < 0 < hi, (a, lo, hi)
    else:
        assert lo > 0, (a, lo, hi)
ev = mp.eigsy(m1_matrix(a_star), eigvals_only=True)
assert abs(min(ev)) < mp.mpf('1e-25') < max(ev)
print('PASS: M_1 indefinite for a < a_*, rank-one PSD at a_*, PD for a > a_*')

# --- sample the curve, and check nothing is clipped -----------------------
step = (A_HI - A_LO) / (N_SAMPLES - 1)
samples = [(A_LO + i * step, f(A_LO + i * step)) for i in range(N_SAMPLES)]
assert samples[0][0] == A_LO and samples[-1][0] == A_HI
for a, y in samples:
    assert Y_MIN < y < Y_MAX, (a, y)
    assert (y < 0) == (a < a_star), (a, y)
for (a0, y0), (a1, y1) in zip(samples, samples[1:]):
    assert y1 > y0, (a0, a1)
assert Y_MIN < 0 < Y_MAX
print(f'PASS: {N_SAMPLES} samples strictly increasing, inside '
      f'[{mp.nstr(Y_MIN, 4)}, {mp.nstr(Y_MAX, 4)}], sign changes exactly at a_*')

# --- emit the pgfplots coordinate block ----------------------------------
if '--emit' in sys.argv:
    coords = ' '.join(f'({mp.nstr(a, 8, strip_zeros=False)},'
                      f'{mp.nstr(y, 9, strip_zeros=False)})' for a, y in samples)
    print(f'\n\\addplot[black!70, line width=1.0pt] coordinates {{{coords}}};')
    print(f'%% a_* = {mp.nstr(a_star, 20)}')

print('\nALL PASS')
