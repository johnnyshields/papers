#!/usr/bin/env python3
r"""Paper sections `sec:geometry` and `sec:dominance`, `thm:weighted-dominance`.

The constants and one refutation behind the end-to-end composition of
`weighted_dominance_of_branch` at `Q(t) = (1-t)^3`, `r = 1`, `B(t) = 3t^2 + 1`.
Each is a number the Lean composition commits to, checked here at the real
objects before anything is built against it -- the binders in that theorem have
carried a wrong number twice.

The branch is `tau(theta) = 1/(2 cos((pi-theta)/3))`, the denominator zeros at
angle `theta` are `tau e^{i theta}`, its conjugate, and `1/tau^2`, and the
spectral parameter is `z = -(1-gamma)^3/gamma`.

  (C1) The endpoint derivatives: `tau'(0) = -1/sqrt(3)`, so
       `gamma_e = -1/sqrt(3) + i` at the lower endpoint; and `tau'(pi) = 0`,
       so on the chart `d -> gamma(pi - d)` the derivative is `i/2`.  The upper
       one is stationary in modulus -- the one-sided quotient is `d/36 + O(d^3)`,
       measured rather than merely shown to vanish, which is the collision
       being quadratic.
  (C2) `nu_B = 0` and `c_B = 4`, because `B(1) = 4 != 0`: neither `B`-leg
       carries a power of `delta`, so `jp0` drops out of both.
  (C3) `c_Q = -3` on BOTH branches, from `D'(t) = -3(1-t)^2 + z`.  The two legs
       agreeing is the check, not a coincidence: `D'(third)/delta^2 -> -4` and
       `D'(gamma)/delta^2 -> 2 + 2 sqrt(3) i`, and `-3 alpha^2` reproduces each
       at its own direction.
  (C4) The directions: `alpha = 2/sqrt(3)` for the nonprincipal member
       (`omega = -1`, index 2) and `alpha_p = -1/sqrt(3) + i` for the principal
       one (`omega = e^{-i pi/3}`, index 0).  `alpha_p = gamma_e` exactly, which
       is what pins `jp0 = 0` rather than leaving it fitted.
  (C5) `z/delta^2 -> 0`, and `z ~ delta^3` -- the second is NOT needed by the
       Lean proof and is measured here only to show the first is not vacuous.
  (C7) **Why `r = 1` is the only place this composition can live.**  `hgamma0_1`
       pins `te1 = gamma(b)` and `hte1` asks `te1 != 0`, so together they need
       `tau(b) != 0` at the UPPER endpoint.  The upper cluster, meanwhile, is
       `{r-th roots of -1} \ {e^{+-i pi/r}}`, which is empty at `r = 1` AND at
       `r = 2` -- at `r = 2` the two roots `+-i` ARE the principal pair -- and
       first non-empty at `r = 3`.  And at every `r >= 2` pencil swept here,
       INCLUDING `deg Q > r`, the arc ends at `z -> infinity` with `tau -> 0`:
       the `r`-fold cluster shrinks to the origin, so `tau(b) = 0` and `hte1`
       fails.  Only `r = 1` ends at a finite collision, `tau(pi) = 1/2 > 0`.
       So the composition is available exactly where the upper cluster is
       vacuous.  This is measured over a family, not argued from one pencil,
       but it is a sweep and not a proof: it is a statement about the pencils
       swept, and the general claim would need the endpoint classification.

  (C6) **The refutation.**  At the upper endpoint `third/tau -> 8`, not `1`.  So
       a separating radius large enough to enclose the third zero (the retained
       block's `R1 = 5`) forces `n1 = 1` through `hgcard1`, and `hexp1` then
       demands `|| third/tau || -> 1` against a true limit of `8`.  The
       composition therefore takes `R1 = 1`, which encloses the principal pair
       alone and makes `n1 = 0` correct rather than convenient.

Every claim is a failing assertion.  `mpmath` throughout: (C3) and (C5) are
second- and third-order rates in `delta`, which float64 cannot separate.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 60


def tau(theta):
    return 1 / (2 * mp.cos((mp.pi - theta) / 3))


def gamma(theta):
    return tau(theta) * mp.exp(1j * theta)


def third(theta):
    return 1 / tau(theta) ** 2


def zpar(theta):
    """`z = -(1-gamma)^3/gamma`, real along the branch."""
    g = gamma(theta)
    return -(1 - g) ** 3 / g


def dprime(t, z):
    return -3 * (1 - t) ** 2 + z


TOL = mp.mpf(10) ** -20


def check_C1():
    """The two endpoint derivatives, by Richardson-free one-sided quotients."""
    for k in range(6, 16):
        d = mp.mpf(10) ** (-k)
        lower = (tau(d) - tau(0)) / d
        assert abs(lower + 1 / mp.sqrt(3)) < mp.mpf(10) ** (-k + 1), (k, lower)
        upper = (tau(mp.pi - d) - tau(mp.pi)) / d
        # the collision is quadratic: tau(pi-d) - tau(pi) = d^2/36 + O(d^4)
        assert abs(upper - d / 36) < d**3, (k, upper)
    # and the branch derivative itself
    d = mp.mpf(10) ** -12
    ge = (gamma(d) - gamma(0)) / d
    assert abs(ge - (-1 / mp.sqrt(3) + 1j)) < mp.mpf(10) ** -10, ge
    ge1 = (gamma(mp.pi - d) - gamma(mp.pi)) / d
    assert abs(ge1 - 1j / 2) < mp.mpf(10) ** -10, ge1
    assert abs(gamma(0) - 1) < TOL
    assert abs(gamma(mp.pi) + mp.mpf(1) / 2) < TOL
    print("PASS  (C1) tau'(0) = -1/sqrt(3), tau'(pi) = 0, gamma_e = -1/sqrt(3)+i and i/2")


def check_C2():
    """`B(1) = 4`, so nu_B = 0 and both B-legs are plain continuity."""
    B = lambda t: 3 * t**2 + 1
    assert abs(B(mp.mpf(1)) - 4) < TOL
    for k in range(4, 13):
        d = mp.mpf(10) ** (-k)
        assert abs(B(third(d)) - 4) < mp.mpf(10) ** (-k + 1), (k, B(third(d)))
        assert abs(B(gamma(d)) - 4) < mp.mpf(10) ** (-k + 1), (k, B(gamma(d)))
    print("PASS  (C2) nu_B = 0 and c_B = 4 on both branches")


def check_C3_C4():
    """c_Q = -3 reproduces both D'-limits through the two directions."""
    alpha = 2 / mp.sqrt(3)
    alpha_p = -1 / mp.sqrt(3) + 1j
    cQ = mp.mpf(-3)
    # the directions themselves
    for k in range(5, 14):
        d = mp.mpf(10) ** (-k)
        assert abs((1 - third(d)) / d + alpha) < mp.mpf(10) ** (-k + 1), (k,)
        assert abs((1 - gamma(d)) / d + alpha_p) < mp.mpf(10) ** (-k + 1), (k,)
    # and the two D'-limits against c_Q alpha^{rho-1}
    prev_j = prev_p = None
    for k in range(4, 11):
        d = mp.mpf(10) ** (-k)
        z = zpar(d)
        ej = dprime(third(d), z) / d**2
        ep = dprime(gamma(d), z) / d**2
        assert abs(ej - cQ * alpha**2) < mp.mpf(10) ** (-k + 1), (k, ej)
        assert abs(ep - cQ * alpha_p**2) < mp.mpf(10) ** (-k + 1), (k, ep)
        prev_j, prev_p = ej, ep
    assert abs(prev_j + 4) < mp.mpf(10) ** -8, prev_j
    assert abs(prev_p - (2 + 2 * mp.sqrt(3) * 1j)) < mp.mpf(10) ** -8, prev_p
    # alpha_p IS gamma_e -- the coincidence that pins jp0 = 0
    d = mp.mpf(10) ** -12
    assert abs(alpha_p - (gamma(d) - gamma(0)) / d) < mp.mpf(10) ** -10
    # and omega = e^{-i pi/3} is the index-0 root, omega = -1 the index-2 one
    ang = lambda j: (2 * mp.mpf(j) - 1) * mp.pi / 3
    assert abs(mp.exp(1j * ang(2)) + 1) < TOL
    assert abs(-1 * mp.exp(1j * ang(2)) / mp.sin(mp.pi / 3) - alpha) < TOL
    assert abs(-1 * mp.exp(1j * ang(0)) / mp.sin(mp.pi / 3) - alpha_p) < TOL
    print("PASS  (C3)+(C4) c_Q = -3 on both legs; alpha = 2/sqrt(3), alpha_p = gamma_e")


def check_C5():
    """z/delta^2 -> 0, and it is not vacuous: z ~ z0 delta^3 with z0 != 0."""
    ratios = []
    for k in range(3, 11):
        d = mp.mpf(10) ** (-k)
        z = zpar(d)
        assert abs(mp.im(z)) < mp.mpf(10) ** (-3 * k + 2), (k, mp.im(z))
        assert abs(z / d**2) < 10 * d, (k, abs(z / d**2))
        ratios.append(mp.re(z) / d**3)
    # z = -(1-gamma)^3/gamma and (1-gamma)/delta -> 1/sqrt(3) - i, so z0 = -(that)^3.
    # The sign is the trap: -gamma_e is what appears, not gamma_e.
    z0 = -((1 / mp.sqrt(3) - 1j) ** 3)
    assert abs(ratios[-1] - mp.re(z0)) < mp.mpf(10) ** -6, (ratios[-1], mp.re(z0))
    assert abs(mp.re(z0)) > mp.mpf("0.5"), mp.re(z0)
    print("PASS  (C5) z/delta^2 -> 0, and z ~ z0 delta^3 with z0 != 0")


def check_C6():
    """The refutation: third/tau -> 8 at the upper endpoint, not 1."""
    for k in range(3, 12):
        d = mp.mpf(10) ** (-k)
        th = mp.pi - d
        assert abs(third(th) / tau(th) - 8) < mp.mpf(10) ** (-2 * k + 3), (k,)
    assert abs(third(mp.pi) - 4) < TOL
    assert abs(tau(mp.pi) - mp.mpf(1) / 2) < TOL
    # so a radius enclosing the third zero cannot leave the upper cluster empty
    assert third(mp.pi) < 5 and tau(mp.pi) < 1 < third(mp.pi)
    # and the unit circle does leave it empty, at every angle of the window
    for k in range(1, 40):
        th = mp.pi - mp.pi / 2 * k / 40
        assert tau(th) < 1 < third(th), th
    print("PASS  (C6) third/tau -> 8, so R1 = 5 forces n1 = 1 and refutes hexp1; R1 = 1 does not")


def _minmod_pair(zeros, r, z):
    """`(tau, theta)` of the minimum-modulus root of `Q(t) + z t^r`, `Q = prod(1 - t/a)`."""
    poly = [mp.mpf(1)]
    for a in zeros:
        new = [mp.mpf(0)] * (len(poly) + 1)
        for i, c in enumerate(poly):
            new[i] += c
            new[i + 1] += -c / a
        poly = new
    while len(poly) <= r:
        poly.append(mp.mpf(0))
    poly[r] += z
    roots = mp.polyroots(list(reversed(poly)), maxsteps=300, extraprec=300)
    t0 = min(roots, key=lambda t: abs(t))
    return abs(t0), abs(mp.arg(t0))


def check_C7():
    """The upper cluster is empty exactly where `hte_1` is satisfiable."""
    # the cluster count: r-th roots of -1, minus the principal pair
    for r in range(1, 7):
        omegas = [mp.exp(1j * (2 * k + 1) * mp.pi / r) for k in range(r)]
        principal = [mp.exp(1j * mp.pi / r), mp.exp(-1j * mp.pi / r)]
        n1 = sum(1 for w in omegas
                 if all(abs(w - p) > mp.mpf(10) ** -25 for p in principal))
        assert n1 == max(0, r - 2), (r, n1)
    assert max(0, 1 - 2) == 0 and max(0, 2 - 2) == 0 and max(0, 3 - 2) == 1
    # tau at the upper endpoint: r = 1 ends finitely, r >= 2 ends at tau = 0
    pencils = [
        ([mp.mpf(1)] * 3, 3, "deg Q = r"),
        ([mp.mpf(1)], 3, "deg Q < r"),
        ([mp.mpf(1), mp.mpf(2), mp.mpf(4), mp.mpf(8)], 3, "deg Q > r"),
        ([mp.mpf(1), mp.mpf(2), mp.mpf(3), mp.mpf(5), mp.mpf(7), mp.mpf(11)], 4, "deg Q > r"),
    ]
    for zeros, r, _label in pencils:
        taus = []
        for e in (6, 9, 12):
            tau_v, th = _minmod_pair(zeros, r, mp.mpf(10) ** e)
            taus.append(tau_v)
            # the arc has not ended: the pair is still off the real axis
            assert th < mp.pi / r, (r, e, th)
            assert th / (mp.pi / r) > mp.mpf("0.98"), (r, e, th)
        assert taus[0] > taus[1] > taus[2], (r, taus)
        assert taus[-1] < mp.mpf(10) ** -3, (r, taus[-1])
    # r = 1 is different: the arc ENDS at a finite z, with tau bounded away from 0
    tau_end = tau(mp.pi)
    assert abs(tau_end - mp.mpf(1) / 2) < TOL, tau_end
    assert abs(zpar(mp.pi) - mp.mpf(27) / 4) < mp.mpf(10) ** -25, zpar(mp.pi)
    print("PASS  (C7) upper cluster empty for r <= 2, first non-empty at r = 3;")
    print("      tau -> 0 at the upper endpoint for every r >= 2 pencil swept, tau(pi) = 1/2 at r = 1")


if __name__ == "__main__":
    check_C1()
    check_C2()
    check_C3_C4()
    check_C5()
    check_C6()
    check_C7()
    print("ALL PASS: check_cubic_composition")
