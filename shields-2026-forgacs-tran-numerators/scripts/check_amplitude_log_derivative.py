#!/usr/bin/env python3
r"""Paper section `subsec:strong-clock`, `prop:local-strong-clock`,
`eq:local-strong-clock`; and `sec:geometry`, `eq:principal-pair`.

`prop:local-strong-clock` needs `psi = arg W` in `C^2` on a compact zero-free
subarc, with `kappa` and `kappa_2` produced at the GENERAL admissible pencil
rather than at one witness.  The route is closed-form and the closed form is
what is checked here, BEFORE it is written in Lean, because a sign or a missing
term in it would be discovered only after the whole chain was built on it.

`Amplitude.ftAmp_eq_ftCritical` gives `W = -gamma B(gamma)/E(gamma)` with
`E = t Q'(t) - r Q(t)` (`Geometry.ftCritical`).  `E` carries no `z`, so `W` is a
rational function of `gamma` ALONE and no second-order theory of the spectral
parameter is needed.  Hence

    W'/W  = gamma' L(gamma),          L(t) = 1/t + B'(t)/B(t) - E'(t)/E(t)
    psi'  = Im(gamma' L(gamma))
    psi'' = Im(gamma'' L(gamma) + (gamma')^2 L'(gamma))

with `gamma'' = e^{i theta}(tau'' + 2 i tau' - tau)`.

Asserted, each as a failing test, at the witness pencil `Q = (1-t)^3`, `r = 1`,
`B = 3t^2 + 1`, on the subarc `[1.75, 2.55]` that `check_cubic_strong_clock.py`
uses -- off both endpoints and clear of the amplitude divisor at `pi/2`:

  (L1) `-gamma B(gamma)/E(gamma)` equals the residue amplitude `-B/D_t`, so the
       entry point is the same object the dominance work uses.
  (L2) `psi'` from the closed form matches a high-order numerical derivative of
       `arg W`.
  (L3) `psi''` from the closed form matches a numerical second derivative --
       this is the assertion that catches a missing `(gamma')^2 L'` term, which
       the first-derivative check cannot see.
  (L4) The two constants the general route must reproduce:
       `max|psi'| = 0.7754`, `max|psi''| = 0.0512`.
  (L5) `E(gamma)` and `B(gamma)` stay away from zero on the subarc, so `L` is
       bounded there -- which is what makes the compactness step legitimate
       rather than merely plausible.

`mpmath` throughout.  `psi''` is ~0.05 against a `psi'` of ~0.78, so a
second-order finite difference in float64 would be reporting its own truncation
error rather than the quantity.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 60

I = mp.mpc(0, 1)
SUB_LO, SUB_HI = mp.mpf('1.75'), mp.mpf('2.55')
R = 1


def tau(theta):
    return 1 / (2 * mp.cos((mp.pi - theta) / 3))


def gamma(theta):
    return tau(theta) * mp.exp(I * theta)


def Qp(t):
    return (1 - t) ** 3


def dQ(t):
    return -3 * (1 - t) ** 2


def Bp(t):
    return 3 * t ** 2 + 1


def dB(t):
    return 6 * t


def E(t):
    return t * dQ(t) - R * Qp(t)


def dE(t):
    # E' = Q' + t Q'' - r Q' = (1-r) Q' + t Q''
    d2Q = 6 * (1 - t)
    return (1 - R) * dQ(t) + t * d2Q


def zbranch(theta):
    t = gamma(theta)
    z = -Qp(t) / t ** R
    assert mp.fabs(mp.im(z)) < mp.mpf(10) ** (-45), f"z left the reals at {theta}"
    return mp.re(z)


def W_residue(theta):
    """`-B/partial_t D`, the residue amplitude the dominance work uses."""
    t = gamma(theta)
    dD = dQ(t) + R * zbranch(theta) * t ** (R - 1)
    return -Bp(t) / dD


def W_critical(theta):
    """`-gamma B(gamma)/E(gamma)`, the `ftAmp_eq_ftCritical` form."""
    t = gamma(theta)
    return -t * Bp(t) / E(t)


# ---------------------------------------------------------------------------
# (L1) the two forms of W agree
# ---------------------------------------------------------------------------
worst = mp.mpf(0)
for k in range(1, 40):
    th = SUB_LO + (SUB_HI - SUB_LO) * k / 40
    a, b = W_residue(th), W_critical(th)
    worst = max(worst, abs(a - b) / abs(b))
assert worst < mp.mpf(10) ** (-45), f"the two forms of W disagree: {mp.nstr(worst, 8)}"
print(f"PASS  (L1) -gamma B(gamma)/E(gamma) = -B/D_t on the subarc, worst "
      f"relative {mp.nstr(worst, 6)}")


def L(t):
    return 1 / t + dB(t) / Bp(t) - dE(t) / E(t)


def dL(t):
    d2B = mp.mpf(6)
    d3Q = mp.mpf(-6)
    d2Q = 6 * (1 - t)
    d2E = (1 - R) * d2Q + d2Q + t * d3Q
    return (-1 / t ** 2
            + (d2B * Bp(t) - dB(t) ** 2) / Bp(t) ** 2
            - (d2E * E(t) - dE(t) ** 2) / E(t) ** 2)


def tau_d(theta):
    return mp.diff(tau, theta)


def tau_dd(theta):
    return mp.diff(tau, theta, 2)


def gamma_d(theta):
    return mp.exp(I * theta) * (tau_d(theta) + I * tau(theta))


def gamma_dd(theta):
    return mp.exp(I * theta) * (tau_dd(theta) + 2 * I * tau_d(theta) - tau(theta))


def psi(theta):
    return mp.arg(W_critical(theta))


def psi_d_closed(theta):
    return mp.im(gamma_d(theta) * L(gamma(theta)))


def psi_dd_closed(theta):
    g, gd, gdd = gamma(theta), gamma_d(theta), gamma_dd(theta)
    return mp.im(gdd * L(g) + gd ** 2 * dL(g))


# ---------------------------------------------------------------------------
# (L2) psi' closed form vs numerical
# ---------------------------------------------------------------------------
worst1 = mp.mpf(0)
for k in range(1, 30):
    th = SUB_LO + (SUB_HI - SUB_LO) * k / 30
    num = mp.diff(psi, th)
    worst1 = max(worst1, abs(num - psi_d_closed(th)))
assert worst1 < mp.mpf(10) ** (-25), f"psi' closed form is wrong: {mp.nstr(worst1, 8)}"
print(f"PASS  (L2) psi' = Im(gamma' L(gamma)) matches the numerical derivative, "
      f"worst {mp.nstr(worst1, 6)}")

# ---------------------------------------------------------------------------
# (L3) psi'' closed form vs numerical -- catches a dropped (gamma')^2 L' term
# ---------------------------------------------------------------------------
worst2 = mp.mpf(0)
for k in range(1, 30):
    th = SUB_LO + (SUB_HI - SUB_LO) * k / 30
    num = mp.diff(psi, th, 2)
    worst2 = max(worst2, abs(num - psi_dd_closed(th)))
assert worst2 < mp.mpf(10) ** (-20), f"psi'' closed form is wrong: {mp.nstr(worst2, 8)}"
# and the second term is load-bearing: dropping it must break the match
bad = max(abs(mp.diff(psi, SUB_LO + (SUB_HI - SUB_LO) * k / 30, 2)
              - mp.im(gamma_dd(SUB_LO + (SUB_HI - SUB_LO) * k / 30)
                      * L(gamma(SUB_LO + (SUB_HI - SUB_LO) * k / 30))))
          for k in range(1, 30))
assert bad > mp.mpf(1) / 100, (
    f"dropping (gamma')^2 L' changes psi'' by only {mp.nstr(bad, 8)}; the check "
    "would not detect a missing term")
print(f"PASS  (L3) psi'' = Im(gamma'' L + (gamma')^2 L') matches numerically "
      f"({mp.nstr(worst2, 6)}); dropping the second term breaks it by "
      f"{mp.nstr(bad, 6)}, so the assertion has teeth")

# ---------------------------------------------------------------------------
# (L4) the two constants the general route must reproduce
# ---------------------------------------------------------------------------
grid = [SUB_LO + (SUB_HI - SUB_LO) * k / 400 for k in range(401)]
p1 = max(abs(psi_d_closed(t)) for t in grid)
p2 = max(abs(psi_dd_closed(t)) for t in grid)
assert abs(p1 - mp.mpf('0.7754')) < mp.mpf(1) / 1000, \
    f"max|psi'| = {mp.nstr(p1, 10)}, expected 0.7754"
assert abs(p2 - mp.mpf('0.0512')) < mp.mpf(1) / 1000, \
    f"max|psi''| = {mp.nstr(p2, 10)}, expected 0.0512"
assert p2 > mp.mpf(1) / 100, "kappa_2 is not genuinely nonzero"
print(f"PASS  (L4) max|psi'| = {mp.nstr(p1, 8)} and max|psi''| = {mp.nstr(p2, 8)} "
      f"from the closed form, matching the measured constants")

# ---------------------------------------------------------------------------
# (L5) L is bounded on the subarc, which is what compactness needs
# ---------------------------------------------------------------------------
minE = min(abs(E(gamma(t))) for t in grid)
minB = min(abs(Bp(gamma(t))) for t in grid)
minT = min(abs(gamma(t)) for t in grid)
assert minE > mp.mpf(1) / 100, f"E(gamma) approaches zero on the subarc: {mp.nstr(minE, 8)}"
assert minB > mp.mpf(1) / 100, f"B(gamma) approaches zero on the subarc: {mp.nstr(minB, 8)}"
assert minT > mp.mpf(1) / 100, f"gamma approaches zero on the subarc: {mp.nstr(minT, 8)}"
print(f"PASS  (L5) on the subarc |E(gamma)| >= {mp.nstr(minE, 6)}, "
      f"|B(gamma)| >= {mp.nstr(minB, 6)}, |gamma| >= {mp.nstr(minT, 6)}, so L is "
      f"bounded and the compactness step is legitimate")

print("ALL PASS  check_amplitude_log_derivative")
