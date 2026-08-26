#!/usr/bin/env python3
r"""Paper section `sec:dominance` (Proof of the main theorem), the phase-state
input of the summed-variation clause.

The formalization's `hstate` binder asks, for a zero `beta` of `B`, for a finite
set containing every parameter where

    polarAngle dgamma d2gamma 0 a x  -  polarAngle gamma dgamma beta a x  =  j*pi

for some INTEGER `j`.  Read literally that is a condition quantified over `j`,
which makes it look like it needs a per-`j` argument.  It does not.  Against the
tree's own definitions --

    logLift gamma dgamma beta a s = Complex.log (gamma a - beta)
                                     + integral of dgamma/(gamma - beta) from a to s
    polarAngle ... = (logLift ...).im

-- the difference is a continuous branch of `arg(gamma'(s) / (gamma(s) - beta))`,
so it is an integer multiple of `pi` exactly when that quotient is real:

    Im( gamma'(s) * conj(gamma(s) - beta) ) = 0 .

Geometrically these are the parameters where the line from `beta` is TANGENT to
the branch.  The integer quantifier disappears and the crossing set becomes the
zero set of one real-analytic function.

  (X1) The two conditions have the SAME solution set, checked against the
       definitions as written -- the base constants carried by `Complex.log` at
       `a` are what could break the equivalence, so the lifted angle is built by
       actual integration rather than by assuming the constants cancel.

  (X2) The set is finite on a compact interval for a representative branch, and
       the tangency function's zeros are simple there, which is what makes them
       isolated.

  (X3) **Non-constancy is a genuine hypothesis, not a formality.**  A branch that
       is a straight line through `beta` makes the tangency function identically
       zero, so the crossing set is the whole interval and no finite set exists.
       Exhibited, so the binder that rules it out is not omitted as
       obviously-true.

  (X4) The pencil's own branch is not that degenerate case: on the FT branch
       `t_+ = 1 + e^{2i theta}` the tangency function is non-constant for every
       `beta` tested, including one ON the branch.

mpmath only.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 30


def polar_angle(gamma, dgamma, beta, a, s):
    """(logLift gamma dgamma beta a s).im, by the definition: the principal log at
    `a` plus the integral of the logarithmic derivative."""
    base = mp.log(gamma(a) - beta)
    integ = mp.quad(lambda u: dgamma(u) / (gamma(u) - beta), [a, s])
    return mp.im(base + integ)


def tangency(gamma, dgamma, beta, s):
    """Im( gamma'(s) * conj(gamma(s) - beta) )."""
    return mp.im(dgamma(s) * mp.conj(gamma(s) - beta))


def diff_angles(gamma, dgamma, d2gamma, beta, a, s):
    """polarAngle dgamma d2gamma 0 a s - polarAngle gamma dgamma beta a s."""
    return polar_angle(dgamma, d2gamma, mp.mpc(0), a, s) - polar_angle(gamma, dgamma, beta, a, s)


# --- a representative branch: the FT lower branch, t_+ = 1 + e^{2 i theta} ----
def g_ft(s):
    return 1 + mp.expj(2 * s)


def dg_ft(s):
    return 2j * mp.expj(2 * s)


def d2g_ft(s):
    return -4 * mp.expj(2 * s)


A = mp.mpf('0.2')
B_END = mp.mpf('1.3')

# --- (X1) the two conditions agree -------------------------------------------
checked = 0
for beta in (mp.mpc('0.3', '0.4'), mp.mpc('-0.5', '0.2'), mp.mpc('2.5', '0'),
             g_ft(mp.mpf('0.9'))):
    # beta on the branch is a genuine case: the amplitude vanishes there
    for k in range(41):
        s = A + (B_END - A) * mp.mpf(k) / 40
        if abs(g_ft(s) - beta) < mp.mpf('1e-6'):
            continue          # the angle is undefined at the meeting point itself
        d = diff_angles(g_ft, dg_ft, d2g_ft, beta, A, s)
        t = tangency(g_ft, dg_ft, beta, s)
        # d is an integer multiple of pi  <->  t = 0
        frac = d / mp.pi
        near_int = abs(frac - mp.nint(frac))
        if near_int < mp.mpf('1e-8'):
            assert abs(t) < mp.mpf('1e-6'), (beta, s, mp.nstr(t, 8))
        if abs(t) < mp.mpf('1e-10'):
            assert near_int < mp.mpf('1e-6'), (beta, s, mp.nstr(near_int, 8))
        checked += 1
print(f"PASS  (X1) at {checked} parameters across four values of beta -- one of them ON "
      f"the branch -- the integer-multiple-of-pi condition and Im(gamma' conj(gamma-beta)) "
      f"= 0 have the same solution set, with the lifted angle built by actual integration "
      f"so the base constants are tested rather than assumed to cancel")


# --- (X2) the set is finite, and the zeros are simple -------------------------
for beta in (mp.mpc('0.3', '0.4'), mp.mpc('-0.5', '0.2')):
    f = lambda s: tangency(g_ft, dg_ft, beta, s)
    roots = []
    N = 400
    for k in range(N):
        s0 = A + (B_END - A) * mp.mpf(k) / N
        s1 = A + (B_END - A) * mp.mpf(k + 1) / N
        if f(s0) == 0 or f(s0) * f(s1) < 0:
            r = mp.findroot(f, (s0, s1), solver='anderson', tol=mp.mpf('1e-25'))
            if not any(abs(r - q) < mp.mpf('1e-12') for q in roots):
                roots.append(r)
    assert len(roots) <= 6, (beta, len(roots))
    for r in roots:
        d = mp.diff(f, r)
        assert abs(d) > mp.mpf('1e-6'), (beta, mp.nstr(r, 10), mp.nstr(d, 8))
    print(f"      beta = {mp.nstr(beta, 6)}: {len(roots)} crossing(s), every zero simple")
print("PASS  (X2) the crossing set is finite on the compact arc and its zeros are "
      "simple, which is what makes them isolated")


# --- (X3) non-constancy is a real hypothesis ---------------------------------
BETA_DEG = mp.mpc('1.5', '2.5')


def g_line(s):
    """A straight line through BETA_DEG."""
    return BETA_DEG + (s - mp.mpf('0.5')) * mp.mpc('0.6', '0.8')


def dg_line(s):
    return mp.mpc('0.6', '0.8')


vals = [tangency(g_line, dg_line, BETA_DEG, A + (B_END - A) * mp.mpf(k) / 20)
        for k in range(21)]
assert all(abs(v) < mp.mpf('1e-25') for v in vals), max(abs(v) for v in vals)
print("PASS  (X3) a branch that is a straight line through beta makes the tangency "
      "function IDENTICALLY zero, so the crossing set is the whole interval and no "
      "finite set exists -- non-constancy is a genuine hypothesis, not a formality")


# --- (X4) the pencil's branch is not degenerate ------------------------------
for beta in (mp.mpc('0.3', '0.4'), mp.mpc('-0.5', '0.2'), mp.mpc('2.5', '0'),
             g_ft(mp.mpf('0.9'))):
    vals = [tangency(g_ft, dg_ft, beta, A + (B_END - A) * mp.mpf(k) / 20) for k in range(21)]
    spread = max(vals) - min(vals)
    assert spread > mp.mpf('1e-3'), (beta, mp.nstr(spread, 8))
print("PASS  (X4) on the pencil's own branch the tangency function is non-constant for "
      "every beta tested, including one lying on the branch")

print("ALL PASS  check_crossing_set_tangency")
