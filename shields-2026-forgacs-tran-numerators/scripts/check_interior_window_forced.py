#!/usr/bin/env python3
r"""Paper section `subsec:proof`, the deleted windows of `thm:weighted-dominance`.

`weighted_dominance_of_branch` binds the deleted-window family `Theta` BEFORE
`hinterior`'s `forall e`, while the window inequality's constant `sigma_i` is
produced inside that quantifier and depends on `e`.  The manuscript chooses the
interior parameter and the windows together, so its windows shrink like
`exp(-cM)`; the Lean binder cannot express that, and this script measures why.

At the witness pencil `Q = (1-t)^3`, `r = 1`, the branch is
`2 tau^3 cos(theta) = 3 tau^2 - 1` with `tau(theta) = 1/(2 cos((pi-theta)/3))`,
and the denominator zeros at angle `theta` are `tau e^{i theta}`, its conjugate,
and `1/tau^2`.  On the arc `[e, pi-e]`:

  (W1) `tau` is strictly decreasing, so any admissible `taumi` obeys
       `taumi >= tau(e)`.
  (W2) The third zero `1/tau^2` is real and the principal pair is not, so any
       separating radius obeys `Ri < 1/tau(e)^2` -- otherwise the
       exactly-two-zeros clause would put a real number equal to a non-real one.
  (W3) Hence `sigma_i >= taumi/Ri > tau(e)^3`, and `tau(e) -> tau(0) = 1`.
  (W4) The amplitude divisor of `B = 3t^2 + 1` on the arc is the single angle
       `pi/2`, with `B`-multiplicity one, so the window inequality reads
       `sigma_i^{M/2} <= |theta - theta_j|`.  Its infimum over admissible `e`
       is therefore `1`, at every `M`: no admissible `Theta` shrinks.

  (W5) The forced deleted set is `{theta : |theta - pi/2| < 1}`, and it does not
       swallow the arc: `pi/2 - 1 > 0`, so `(0, pi/2 - 1]` survives at every `M`.

Each is a failing assertion.  `mpmath` throughout: `tau(e)^3` approaches `1`
from below and the interesting quantity is `1 - tau(e)^{3M/2}`, which float64
would round to zero well before the trend is visible.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50


def tau(theta):
    """The branch value, Viete's trigonometric root of `2 tau^3 cos t = 3 tau^2 - 1`."""
    return 1 / (2 * mp.cos((mp.pi - theta) / 3))


def branch_residual(t, theta):
    return 2 * mp.cos(theta) * t**3 - 3 * t**2 + 1


def amplitude_zero_residual(theta):
    """`|3 gamma(theta)^2 + 1|` along the principal branch."""
    g = tau(theta) * mp.exp(1j * theta)
    return abs(3 * g**2 + 1)


def check_branch():
    """The closed form solves the branch condition and gives the exact points."""
    for k in range(1, 40):
        theta = mp.pi * k / 40
        assert abs(branch_residual(tau(theta), theta)) < mp.mpf(10) ** -40, theta
    assert abs(tau(0) - 1) < mp.mpf(10) ** -40
    assert abs(tau(mp.pi / 2) - 1 / mp.sqrt(3)) < mp.mpf(10) ** -40
    assert abs(tau(mp.pi) - mp.mpf(1) / 2) < mp.mpf(10) ** -40
    print("PASS  the closed form solves the branch and hits 1, 1/sqrt(3), 1/2")


def check_W1_W2():
    """`taumi >= tau(e)` because `tau` decreases; `Ri < 1/tau(e)^2` because the
    third zero is real and the principal pair is not."""
    for k in range(1, 60):
        e = mp.pi / 2 * k / 60
        vals = [tau(e + (mp.pi - 2 * e) * j / 50) for j in range(51)]
        assert max(vals) == vals[0], e            # the maximum is at the left endpoint
        assert all(vals[i] > vals[i + 1] for i in range(50)), e
        third = 1 / tau(e) ** 2
        assert third > 1 > tau(e), e              # the third zero is outside, the pair inside
        gamma = tau(e) * mp.exp(1j * e)
        assert abs(mp.im(gamma)) > mp.mpf(10) ** -30, e   # so a real radius cannot reach it
    print("PASS  (W1) taumi >= tau(e) and (W2) Ri < 1/tau(e)^2 across the arc")


def check_W3_W4():
    """`sigma_i > tau(e)^3 -> 1`, so the window bound's supremum is 1 at every M."""
    for M in (1, 2, 5, 20, 100, 1000):
        best = mp.mpf(0)
        for k in range(1, 26):
            e = mp.mpf(1) / 10**k if k <= 20 else mp.mpf(1) / 10**20
            sigma_lb = tau(e) ** 3
            assert sigma_lb < 1, (M, e)
            bound = sigma_lb ** (mp.mpf(M) / 2)
            assert bound > best or k > 20, (M, e)
            best = max(best, bound)
        assert best > 1 - mp.mpf(10) ** -12, (M, best)
        assert best < 1, (M, best)
    print("PASS  (W3)+(W4) sup over e of sigma_i^{M/2} is 1 at M = 1 .. 1000")


def check_W4_divisor():
    """`B = 3t^2 + 1` vanishes on the branch at `pi/2` and nowhere else on the arc."""
    assert amplitude_zero_residual(mp.pi / 2) < mp.mpf(10) ** -40
    for k in range(1, 400):
        theta = mp.pi * k / 400
        if abs(theta - mp.pi / 2) < mp.mpf(10) ** -30:
            continue
        assert amplitude_zero_residual(theta) > mp.mpf(10) ** -6, theta
    # multiplicity one: the derivative `6t` does not vanish there
    g = tau(mp.pi / 2) * mp.exp(1j * mp.pi / 2)
    assert abs(6 * g) > mp.mpf(1), abs(6 * g)
    print("PASS  (W4) the divisor on the arc is the single simple angle pi/2")


def check_W5():
    """The forced window does not swallow the arc."""
    room = mp.pi / 2 - 1
    assert room > mp.mpf("0.57") and room < mp.mpf("0.58"), room
    for theta in (mp.mpf("0.1"), mp.mpf("0.3"), room):
        assert abs(theta - mp.pi / 2) >= 1, theta
    assert abs(mp.pi / 4 - mp.pi / 2) < 1        # and it is a real deletion, not empty
    print("PASS  (W5) (0, pi/2 - 1] survives the forced window at every M")


if __name__ == "__main__":
    check_branch()
    check_W1_W2()
    check_W3_W4()
    check_W4_divisor()
    check_W5()
    print("ALL PASS: check_interior_window_forced")
