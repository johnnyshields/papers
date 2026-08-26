#!/usr/bin/env python3
r"""Paper section `subsec:proof` (Proof of the discrepancy bound), the band
parameter `\eps` of `eq:amplitude-deletion` and `eq:retained-range`.

The composition that builds an `FTPhaseSupply` from the dominance bound bundles
`\eps` together with the bound stated at that `\eps`, so a producer must choose
one `\eps` meeting two constraints at once:

  * the band clause -- every amplitude zero of the open arc `(0, \pi/r)` lies in
    the closed band `[\eps, \pi/r - \eps]`, which wants `\eps` SMALL; and
  * the dominance bound itself, whose windows are cut at a radius that depends
    on `\eps`.

Read as a quantitative pair these pull opposite ways, and a producer squeezed
between them would have to trade one against the other.  **They do not conflict,
and the reason is structural rather than quantitative**: the dominance bound's
whole dependence on `\eps` runs through the CARDINALITY of the amplitude
divisor, which is a bounded monotone integer function of `1/\eps` and therefore
eventually constant.  Both constraints hold on one interval `(0, \eps_0)`.

This script establishes that on an exactly-parametrized pencil, against the
definitions as they are written rather than against a paraphrase of them.

  (E1) The branch is exact and simple.  For `Q(t) = 1 - t` and `r = 2` the real-`z`
       locus is `\tau(\theta) = 2\cos\theta`, so the branch point is
       `t_+(\theta) = 2\cos\theta e^{i\theta} = 1 + e^{2i\theta}` -- the upper half
       of the unit circle about 1 -- with `z(\theta) = 1/(4\cos^2\theta)` real,
       `arg t_+(\theta) = \theta` exactly, and `D'(t_+) = i\tan\theta \ne 0`.
       Asserted, not assumed: this is the sample, so what it IS gets checked.

  (E2) The divisor is computed from its definition verbatim -- the arguments of
       the roots of `B`, filtered by BOTH clauses (membership in the band, and
       vanishing of the amplitude) -- with the cofactor obtained by actual
       polynomial division, cross-checked against `D'(t_+)`.

  (E3) The second filter clause is load-bearing.  `B` carries a root whose
       argument lies inside the band but which is NOT on the branch, so the
       argument filter alone would admit it and the amplitude clause rejects it.
       A test where both clauses agree on every root cannot see this.

  (E4) Stabilization, with the threshold in closed form.  The divisor is
       non-decreasing as `\eps` decreases, bounded by the number of distinct
       roots of `B`, and constant below
       `\eps_0 = \min_j \min(\theta_j, \pi/r - \theta_j)` over the branch
       arguments `\theta_j` -- asserted against the closed form, not against a
       drift between successive `\eps`.

  (E5) The threshold is not vacuous.  Crossing each of the two thresholds the
       sample was built to have DROPS the count, so `\eps_0` is where something
       happens rather than a bound quoted below the whole sweep.

  (E6) The window radius inherits it.  `windowRadius` reads `S` only through
       `S.card` and takes a constant `\nu`, so it is EXACTLY equal at two
       different `\eps` below `\eps_0` and differs across the threshold.  The
       equality is asserted exactly, since a step function is what is claimed.

  (E7) The band clause holds on the same interval, so one `\eps` serves both.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 40

R = 2
PI_R = mp.pi / R
NU = 4  # max(deg B, 1) for the B built below; the constant multiplicity weight
SIGMA = mp.mpf('0.5')


# --- the pencil, exactly parametrized -----------------------------------------
def q_eval(t):
    """Q(t) = 1 - t."""
    return 1 - t


def branch(theta):
    """t_+(theta) = 2 cos(theta) e^{i theta}, the real-z locus of Q + z t^2."""
    return 2 * mp.cos(theta) * mp.expj(theta)


def z_of(theta):
    """z(theta) = 1/(4 cos^2 theta)."""
    return 1 / (4 * mp.cos(theta) ** 2)


def den_eval(z, t):
    """ftDen Q r z evaluated at t:  Q(t) + z t^r."""
    return q_eval(t) + z * t ** R


def den_deriv(z, t):
    """d/dt [Q(t) + z t^r] = -1 + r z t^{r-1}."""
    return -1 + R * z * t ** (R - 1)


# (E1) the sample IS what it is claimed to be
for theta in [mp.mpf(s) for s in ('0.15', '0.3', '0.7', '1.1', '1.45')]:
    t = branch(theta)
    z = z_of(theta)
    assert abs(den_eval(z, t)) < mp.mpf('1e-30'), (theta, den_eval(z, t))
    assert abs(mp.im(z)) == 0
    assert abs(mp.arg(t) - theta) < mp.mpf('1e-30'), (theta, mp.arg(t))
    assert abs(t - (1 + mp.expj(2 * theta))) < mp.mpf('1e-30')
    # simple root, with the closed form the docstring names
    assert abs(den_deriv(z, t) - 1j * mp.tan(theta)) < mp.mpf('1e-30')
    assert abs(den_deriv(z, t)) > mp.mpf('1e-10')
print("PASS  (E1) the branch t_+ = 1 + e^{2i theta} solves the pencil with real z, "
      "arg t_+ = theta exactly, and D'(t_+) = i tan(theta) is nonzero")


# --- B, built so that both filter clauses are exercised ------------------------
THETA_ON = [mp.mpf('0.3'), mp.mpf('1.1')]          # roots ON the branch
OFF = mp.mpf('0.5') * mp.expj(mp.mpf('0.7'))       # arg in band, NOT on branch

roots = []
for th in THETA_ON:
    roots += [branch(th), mp.conj(branch(th))]
roots += [OFF, mp.conj(OFF)]


def b_eval(t):
    out = mp.mpc(1)
    for w in roots:
        out *= (t - w)
    return out


# B has real coefficients (conjugate-closed root multiset) and B(0) != 0
assert abs(mp.im(b_eval(mp.mpf('0.37')))) < mp.mpf('1e-30')
assert abs(b_eval(0)) > mp.mpf('1e-10')
# the off-branch root really is off the branch, at an argument inside the arc
assert mp.mpf(0) < mp.arg(OFF) < PI_R
assert abs(OFF - branch(mp.arg(OFF))) > mp.mpf('0.9'), abs(OFF - branch(mp.arg(OFF)))
print("PASS  (E1') B has real coefficients, B(0) != 0, two roots on the branch and "
      "one off it whose argument nonetheless lies inside the arc")


# --- the divisor, from the definition -----------------------------------------
def cofactor_at(z, tau):
    """(ftDen Q r z /_m (X - tau)) evaluated at tau, by synthetic division on the
    coefficient list of Q + z X^r, and independently as D'(tau)."""
    # Q + z X^2 = (1) + (-1) X + z X^2, ascending -> descending
    desc = [z, mp.mpc(-1), mp.mpc(1)]
    out, acc = [], mp.mpc(0)
    for c in desc[:-1]:
        acc = acc * tau + c
        out.append(acc)
    quotient_at_tau = mp.mpc(0)
    for c in out:
        quotient_at_tau = quotient_at_tau * tau + c
    return quotient_at_tau


def ft_amp(theta):
    """ftAmp Q B r (z theta) (ftPrincipal tau theta) = -B(t_+)/cofactor(t_+)."""
    t = branch(theta)
    z = z_of(theta)
    cof = cofactor_at(z, t)
    assert abs(cof - den_deriv(z, t)) < mp.mpf('1e-28'), (theta, cof, den_deriv(z, t))
    return -b_eval(t) / cof


def divisor(eps):
    """ftAmplitudeDivisor Q B r z tau eps (pi/r - eps): the arguments of the roots
    of B, filtered by membership in the band AND vanishing of the amplitude."""
    lo, hi = eps, PI_R - eps
    cand = sorted({mp.nstr(mp.arg(w), 25) for w in roots})
    out = []
    for s in cand:
        th = mp.mpf(s)
        if not (lo <= th <= hi):
            continue
        if abs(ft_amp(th)) < mp.mpf('1e-20'):
            out.append(th)
    return out


# (E3) the amplitude clause rejects what the argument clause admits
th_off = mp.arg(OFF)
assert mp.mpf('0.05') <= th_off <= PI_R - mp.mpf('0.05')
assert abs(ft_amp(th_off)) > mp.mpf('1e-3'), abs(ft_amp(th_off))
assert th_off not in divisor(mp.mpf('0.05'))
print(f"PASS  (E3) the off-branch root's argument {mp.nstr(th_off, 6)} sits inside the "
      f"band and |ftAmp| = {mp.nstr(abs(ft_amp(th_off)), 6)} there, so the amplitude "
      f"clause -- not the band clause -- is what excludes it")


# (E4) stabilization, against the closed-form threshold
EPS0 = min(min(th, PI_R - th) for th in THETA_ON)
assert EPS0 == mp.mpf('0.3'), EPS0
below = [EPS0 / k for k in (2, 5, 17, 1000)]
cards = {len(divisor(e)) for e in below}
assert cards == {2}, cards
assert len(divisor(EPS0 / 2)) <= len({mp.nstr(mp.arg(w), 25) for w in roots})
print(f"PASS  (E4) the divisor has card 2 at every eps below "
      f"eps_0 = {mp.nstr(EPS0, 6)} = min_j min(theta_j, pi/r - theta_j), and never "
      f"exceeds the {len({mp.nstr(mp.arg(w), 25) for w in roots})} distinct root arguments of B")

# monotone as eps decreases
ladder = [mp.mpf(s) for s in ('0.6', '0.45', '0.35', '0.25', '0.05', '0.001')]
seq = [len(divisor(e)) for e in ladder]
assert all(a <= b for a, b in zip(seq, seq[1:])), seq
print(f"PASS  (E4') the count is non-decreasing as eps shrinks: {seq}")


# (E5) the thresholds are load-bearing -- crossing each one drops the count
EPS1 = PI_R - max(THETA_ON)          # 1.1 leaves the band above this
assert len(divisor(EPS0 * mp.mpf('0.99'))) == 2
assert len(divisor(EPS0 * mp.mpf('1.01'))) == 1
assert len(divisor(EPS1 * mp.mpf('0.99'))) == 1
assert len(divisor(EPS1 * mp.mpf('1.01'))) == 0
print(f"PASS  (E5) the count steps 2 -> 1 across eps_0 = {mp.nstr(EPS0, 6)} and "
      f"1 -> 0 across {mp.nstr(EPS1, 6)}, so the threshold is where the behaviour "
      f"changes rather than a bound quoted below the whole sweep")


# (E6) the window radius reads the divisor only through its cardinality
def window_radius(eps, M):
    """windowRadius sigma S nu M theta_j with nu constant:
       exp(-((-log sigma)/(2 card S)) * M / nu)."""
    n = len(divisor(eps))
    assert n > 0, "the radius is only used where the divisor is nonempty"
    return mp.exp(-((-mp.log(SIGMA)) / (2 * n)) * M / NU)


for M in (1, 8, 64, 4096):
    a, b = window_radius(EPS0 / 2, M), window_radius(EPS0 / 1000, M)
    assert a == b, (M, a, b)          # exact: a step function is claimed
    c = window_radius(EPS0 * mp.mpf('1.01'), M)
    assert c != a, (M, c, a)
print("PASS  (E6) the window radius is EXACTLY equal at two eps below eps_0 -- it "
      "reads S only through S.card and takes a constant nu -- and differs across "
      "the threshold, so the dependence is real and has merely stopped stepping")


# (E7) the band clause holds on the same interval
def amplitude_zeros_on_open_arc():
    out = []
    for w in roots:
        th = mp.arg(w)
        if mp.mpf(0) < th < PI_R and abs(ft_amp(th)) < mp.mpf('1e-20'):
            out.append(th)
    return out


zs = amplitude_zeros_on_open_arc()
assert sorted(mp.nstr(t, 12) for t in zs) == sorted(mp.nstr(t, 12) for t in THETA_ON)
for e in below:
    assert all(e <= th <= PI_R - e for th in zs), e
print(f"PASS  (E7) every amplitude zero of the open arc lies in [eps, pi/r - eps] "
      f"for each eps below eps_0, so the band clause and the stabilized dominance "
      f"constants are met by one and the same eps")

print("ALL PASS  check_band_epsilon_stabilizes")
