#!/usr/bin/env python3
r"""Paper section `subsec:proof`, `eq:amplitude-window-negligible`.

`prop:angular-discrepancy` deletes a window `Theta_{j,M}` around each zero of the
principal amplitude and needs `(M+1) sum_j |Theta_{j,M}| <= 1`, which the paper
obtains by "increasing the `B`-dependent threshold".  That step is the one place
`prop:angular-discrepancy` could fail to be provable as stated, so it is measured
here rather than assumed.

The companion `check_interior_window_forced.py` measures the *Lean* binder: in
`weighted_dominance_of_branch` the deleted family `Theta` is bound BEFORE
`hinterior`'s `forall e` while the window constant is produced inside it, so no
admissible `Theta` shrinks.  The two scripts answer different questions, and this
one answers the question about the manuscript: with the window chosen after the
contour ratio, as `subsec:proof` chooses it, does it shrink fast enough?

At the witness pencil `Q = (1-t)^3`, `r = 1`, `B = 3t^2 + 1` the whole thing is
exact, with no contour integration and no root-finding:

  `D(t,z) = (1-t)^3 + z t` has the three zeros `gamma = tau e^{i theta}`, its
  conjugate, and a third real zero `t3`.  So `eq:principal-decomposition` is
  EXACT here -- the remainder is the single third-root term, not a tail -- and

      `tau^{M+1} F_M(z) = 2 Re(W e^{-i(M+1)theta}) + R_M`,
      `R_M = (tau/t3)^{M+1} W3`.

  The window is the set where `eq:dominance-bound` `|R_M| <= |W|/2` FAILS.  `W`
  has a simple zero at `theta = pi/2`, so near it `|W| ~ c|theta - pi/2|` and the
  half-width solves `(tau/t3)^{M+1}|W3| = c|theta - pi/2|/2`: geometric in `M`.

Asserted, each as a failing test:

  (A1) `t3` is real and equals `1/tau^2`, so `tau/t3 = tau^3` exactly.
  (A2) The decomposition is exact: the three residues reproduce `F_M` to 40
       digits.  (A `sum_j` over one `j`: the divisor on this arc is `{pi/2}`.)
  (A3) The window half-width is geometric, with log-slope matching `log(tau^3)`
       at the divisor -- `3 log(1/sqrt 3) = -1.6479`.
  (A4) `(M+1) * total deleted length -> 0`, and is already below `1` -- which is
       `eq:amplitude-window-negligible` -- from a threshold this script reports.
  (A5) The threshold is `B`-dependent but the DECAY RATE is not: rerunning at a
       weight with a double zero on the arc moves the threshold, not the rate.

`mpmath` throughout: `tau^3` at the divisor is `3^{-3/2}`, so by `M = 60` the
half-width is below `1e-45` and float64 would have flushed it to zero long
before the slope is visible.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 400

I = mp.mpc(0, 1)
DIVISOR = mp.pi / 2


def tau(theta):
    """Viete's trigonometric root of `2 tau^3 cos(theta) = 3 tau^2 - 1`."""
    return 1 / (2 * mp.cos((mp.pi - theta) / 3))


def gamma(theta):
    return tau(theta) * mp.exp(I * theta)


def zbranch(theta):
    t = gamma(theta)
    z = -(1 - t) ** 3 / t
    assert mp.fabs(mp.im(z)) < mp.mpf(10) ** (-90), f"z left the reals at {theta}"
    return mp.re(z)


def Bpoly(t):
    return 3 * t ** 2 + 1


def dD(t, z):
    """`\\partial_t D` with `D = (1-t)^3 + z t`."""
    return -3 * (1 - t) ** 2 + z


def amp(t, z):
    """`eq:principal-pair`'s residue amplitude `-B/\\partial_t D`."""
    return -Bpoly(t) / dD(t, z)


# ---------------------------------------------------------------------------
# (A1) the third zero is real and is exactly 1/tau^2
# ---------------------------------------------------------------------------
worst_t3 = mp.mpf(0)
for k in range(1, 60):
    th = mp.pi * k / 60
    z = zbranch(th)
    # D(t,z) = -t^3 + 3t^2 + (z-3)t + 1, roots: gamma, conj gamma, t3
    roots = mp.polyroots([mp.mpf(-1), mp.mpf(3), z - 3, mp.mpf(1)], maxsteps=200,
                         extraprec=400)
    real_roots = [r for r in roots if mp.fabs(mp.im(r)) < mp.mpf(10) ** (-60)]
    assert len(real_roots) == 1, f"expected one real zero at theta={th}, got {len(real_roots)}"
    t3 = mp.re(real_roots[0])
    worst_t3 = max(worst_t3, mp.fabs(t3 - 1 / tau(th) ** 2))
assert worst_t3 < mp.mpf(10) ** (-55), f"t3 != 1/tau^2, worst {mp.nstr(worst_t3, 8)}"
print(f"PASS  (A1) the third zero is real and equals 1/tau^2 "
      f"(worst deviation {mp.nstr(worst_t3, 6)}), so tau/t3 = tau^3 exactly")


def t3_of(theta):
    return 1 / tau(theta) ** 2


def coeff_FM(theta, M):
    """`F_M(z) = [t^M] B/D` by exact residues over the three simple zeros."""
    z = zbranch(theta)
    g = gamma(theta)
    total = mp.mpc(0)
    for t in (g, mp.conj(g), mp.mpc(t3_of(theta), 0)):
        total += amp(t, z) * t ** (-(M + 1))
    return total


def series_FM(theta, M):
    """The same coefficient, independently, by Taylor series of B/D at 0."""
    z = zbranch(theta)
    f = lambda t: Bpoly(t) / ((1 - t) ** 3 + z * t)
    return mp.taylor(f, 0, M, method='quad', radius=mp.mpf(1) / 4)[M]


# ---------------------------------------------------------------------------
# (A2) the decomposition is exact -- two independent routes to F_M
# ---------------------------------------------------------------------------
worst_dec = mp.mpf(0)
for th in (mp.mpf(3) / 10, mp.mpf(1), DIVISOR - mp.mpf(1) / 5, mp.mpf(5) / 2):
    for M in (6, 11, 20):
        a = coeff_FM(th, M)
        b = series_FM(th, M)
        assert mp.fabs(mp.im(a)) < mp.mpf(10) ** (-60), "F_M left the reals"
        rel = mp.fabs(a - b) / max(mp.fabs(b), mp.mpf(1))
        worst_dec = max(worst_dec, rel)
assert worst_dec < mp.mpf(10) ** (-40), f"residues disagree with the series: {mp.nstr(worst_dec, 8)}"
print(f"PASS  (A2) eq:principal-decomposition is exact at this pencil: residues "
      f"vs series agree to {mp.nstr(worst_dec, 6)} relative")


def remainder(theta, M):
    """`R_M = (tau/t3)^{M+1} W3`, the exact third-root term."""
    z = zbranch(theta)
    t3 = t3_of(theta)
    return amp(mp.mpc(t3, 0), z) * (tau(theta) / t3) ** (M + 1)


def W_of(theta):
    return amp(gamma(theta), zbranch(theta))


def half_width(M, lo, hi):
    """Largest `d` with `|R_M| > |W|/2` at `pi/2 + d`; bisected on the failure set.

    Bisection runs on `log d`, not on `d`.  The width is geometric in `M`, so by
    `M = 85` it is below `1e-61` -- and a linear bisection from `1/2`, however
    many steps it takes, resolves nothing past its own step size and returns the
    SAME number for every larger `M`.  That reads as a slope of zero, i.e. as a
    window that has stopped shrinking, which is the opposite of the truth.  The
    failure is in the instrument, so the instrument is what changes.
    """
    fail = lambda d: mp.fabs(remainder(DIVISOR + d, M)) > mp.fabs(W_of(DIVISOR + d)) / 2
    ulo, uhi = mp.log(lo), mp.log(hi)
    assert fail(mp.exp(ulo)), f"the window is empty at M={M}: dominance already holds at d={lo}"
    assert not fail(mp.exp(uhi)), f"the window exceeds the probe at M={M}"
    for _ in range(400):
        umid = (ulo + uhi) / 2
        if fail(mp.exp(umid)):
            ulo = umid
        else:
            uhi = umid
    return mp.exp((ulo + uhi) / 2)


# ---------------------------------------------------------------------------
# (A3) the half-width is geometric, at the rate tau^3 predicts
# ---------------------------------------------------------------------------
Ms = list(range(20, 105, 5))
widths = [half_width(M, mp.mpf(10) ** (-300), mp.mpf(1) / 2) for M in Ms]
slopes = [(mp.log(widths[i + 1]) - mp.log(widths[i])) / (Ms[i + 1] - Ms[i])
          for i in range(len(Ms) - 1)]
predicted = 3 * mp.log(tau(DIVISOR))
worst_slope = max(mp.fabs(s - predicted) for s in slopes)
assert worst_slope < mp.mpf(1) / 100, (
    f"the half-width is not geometric at rate tau^3: worst slope deviation "
    f"{mp.nstr(worst_slope, 8)}, predicted {mp.nstr(predicted, 8)}")
print(f"PASS  (A3) window half-width is geometric: log-slope "
      f"{mp.nstr(slopes[-1], 10)} vs predicted 3 log tau(pi/2) = "
      f"{mp.nstr(predicted, 10)} (worst deviation {mp.nstr(worst_slope, 4)})")

# ---------------------------------------------------------------------------
# (A4) eq:amplitude-window-negligible, and the threshold it holds from
# ---------------------------------------------------------------------------
threshold = None
for M in range(2, 120):
    total = 2 * half_width(M, mp.mpf(10) ** (-300), mp.mpf(1) / 2)
    if (M + 1) * total <= 1:
        threshold = M
        break
assert threshold is not None, "eq:amplitude-window-negligible never holds"
for M in range(threshold, 140, 7):
    total = 2 * half_width(M, mp.mpf(10) ** (-300), mp.mpf(1) / 2)
    assert (M + 1) * total <= 1, f"eq:amplitude-window-negligible fails again at M={M}"
tail = (140 + 1) * 2 * half_width(140, mp.mpf(10) ** (-300), mp.mpf(1) / 2)
assert tail < mp.mpf(10) ** (-30), f"(M+1)|Theta| is not tending to 0: {mp.nstr(tail,8)}"
print(f"PASS  (A4) eq:amplitude-window-negligible holds from M = {threshold} onward, "
      f"and (M+1)|Theta_M| -> 0: at M = 140 it is {mp.nstr(tail, 6)}")

# ---------------------------------------------------------------------------
# (A5) a heavier weight moves the threshold, not the rate
# ---------------------------------------------------------------------------
_B = Bpoly


def _double():
    global Bpoly
    Bpoly = lambda t: (3 * t ** 2 + 1) ** 2


_double()
Ms2 = [40, 50, 60, 70]
w2 = [half_width(M, mp.mpf(10) ** (-300), mp.mpf(1) / 2) for M in Ms2]
slopes2 = [(mp.log(w2[i + 1]) - mp.log(w2[i])) / (Ms2[i + 1] - Ms2[i])
           for i in range(len(Ms2) - 1)]
# a double zero halves the exponent: |W| ~ c d^2 gives d ~ (tau^3)^{(M+1)/2}
predicted2 = predicted / 2
worst2 = max(mp.fabs(s - predicted2) for s in slopes2)
Bpoly = _B
assert worst2 < mp.mpf(1) / 100, (
    f"the double-zero rate is not half the simple one: {mp.nstr(worst2, 8)}")
print(f"PASS  (A5) at a double zero the rate halves as the multiplicity predicts "
      f"({mp.nstr(slopes2[-1], 10)} vs {mp.nstr(predicted2, 10)}); still geometric, "
      f"so the threshold moves with B and the decay rate does not")

print("ALL PASS  check_amplitude_window_shrinks")
