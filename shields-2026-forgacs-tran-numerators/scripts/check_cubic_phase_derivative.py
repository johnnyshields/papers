#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `lem:amplitude-divisor` and
`eq:phase-derivative-bound`, at `Q(t) = (1-t)^3`, `r = 1`, `B(t) = 3t^2 + 1`.

`eq:phase-derivative-bound` asserts that a continuous branch `psi = arg W` has
`|psi'| <= kappa` on every component of the arc minus the amplitude's zero set.
This script settles, at the cubic pencil and at real numbers, the three facts a
formal proof of that bound consumes.

  (P1) The branch has the closed form `tau(theta) = 1/(2 cos((pi-theta)/3))`,
       i.e. it solves `2 tau^3 cos theta - 3 tau^2 + 1 = 0` and lies in `(0,1]`
       on `[0,pi]`.  Checked against a root solve of the branch cubic.

  (P2) The residue amplitude collapses to a rational function of the branch
       point alone:

           W = -B(gamma)/D_t(gamma) = gamma (3 gamma^2 + 1)
                                      / ((1-gamma)^2 (2 gamma + 1)).

       Checked against `W` assembled from `z = -(1-gamma)^3/gamma` and
       `D_t(t) = -3(1-t)^2 + z`.  This is what makes `psi'` elementary: the
       only zero of `W` on the open arc is `3 gamma^2 + 1 = 0`, at
       `theta = pi/2`, and `gamma = 0`, `gamma = 1`, `gamma = -1/2` are all off
       the open arc.

  (P3) `psi' = Im(W'/W)` is FINITE, and its size and sign are measured rather
       than assumed.  `W'/W = gamma' L(gamma)` with

           L(t) = 1/t + 6t/(3t^2+1) + 2/(1-t) - 2/(2t+1),
           gamma' = e^{i theta}(tau' + i tau).

       Two things are checked: the closed-form `W'/W` against a central
       difference of `log W`, and the maximum of `|Im(W'/W)|` over the retained
       set `|theta - pi/2| >= 1` intersected with the open arc.  The blow-up at
       `theta = pi/2` is REAL, not imaginary -- the simple zero of `W` there
       contributes `nu/(theta - theta_j)` to `W'/W` with `nu = 1` and a real
       coefficient, so it cancels out of the imaginary part.  That cancellation
       is `lem:amplitude-divisor`'s last paragraph and is measured here as (P3c).
"""

import math

import mpmath as mp

mp.mp.dps = 40


def tau_closed(theta):
    return 1 / (2 * mp.cos((mp.pi - theta) / 3))


def tau_solved(theta):
    """The unique root of the branch cubic in (0,1], found without the formula."""
    return mp.findroot(
        lambda t: 2 * mp.cos(theta) * t**3 - 3 * t**2 + 1, mp.mpf("0.75")
    )


def tau_prime(theta):
    phi = (mp.pi - theta) / 3
    return -mp.sin(phi) / (6 * mp.cos(phi) ** 2)


def gamma(theta):
    return tau_closed(theta) * mp.exp(1j * theta)


def gamma_prime(theta):
    return mp.exp(1j * theta) * (tau_prime(theta) + 1j * tau_closed(theta))


def amp_assembled(theta):
    """`W = -B(gamma)/D_t(gamma)`, built the way the definition does."""
    g = gamma(theta)
    z = -((1 - g) ** 3) / g
    dt = -3 * (1 - g) ** 2 + z
    return -(3 * g**2 + 1) / dt


def amp_rational(theta):
    g = gamma(theta)
    return g * (3 * g**2 + 1) / ((1 - g) ** 2 * (2 * g + 1))


def log_deriv(theta):
    """`W'/W = gamma' L(gamma)`."""
    g = gamma(theta)
    L = 1 / g + 6 * g / (3 * g**2 + 1) + 2 / (1 - g) - 2 / (2 * g + 1)
    return gamma_prime(theta) * L


def check_P1():
    print("(P1) tau closed form against a root solve of the branch cubic")
    worst = mp.mpf(0)
    for k in range(1, 200):
        theta = mp.pi * k / 200
        tc, ts = tau_closed(theta), tau_solved(theta)
        assert abs(tc - ts) < mp.mpf("1e-30"), (theta, tc, ts)
        assert 0 < tc <= 1, (theta, tc)
        resid = 2 * mp.cos(theta) * tc**3 - 3 * tc**2 + 1
        worst = max(worst, abs(resid))
    assert tau_closed(0) == 1 or abs(tau_closed(0) - 1) < mp.mpf("1e-35")
    assert abs(tau_closed(mp.pi) - mp.mpf("0.5")) < mp.mpf("1e-35")
    assert abs(tau_closed(mp.pi / 2) - 1 / mp.sqrt(3)) < mp.mpf("1e-35")
    print(f"      max |2 tau^3 cos - 3 tau^2 + 1| = {mp.nstr(worst, 5)}")
    print(f"      tau(0) = {mp.nstr(tau_closed(0), 10)}, "
          f"tau(pi/2) = {mp.nstr(tau_closed(mp.pi/2), 10)}, "
          f"tau(pi) = {mp.nstr(tau_closed(mp.pi), 10)}")


def check_P2():
    print("(P2) W = gamma(3 gamma^2+1)/((1-gamma)^2(2 gamma+1))")
    worst = mp.mpf(0)
    for k in range(1, 200):
        theta = mp.pi * k / 200
        a, b = amp_assembled(theta), amp_rational(theta)
        worst = max(worst, abs(a - b))
        assert abs(a - b) < mp.mpf("1e-28") * max(1, abs(a)), (theta, a, b)
    print(f"      max |assembled - rational| = {mp.nstr(worst, 5)}")
    z0 = amp_rational(mp.pi / 2)
    print(f"      W(pi/2) = {mp.nstr(z0, 5)}   (the amplitude's only interior zero)")
    assert abs(z0) < mp.mpf("1e-30")


def check_P3():
    print("(P3a) W'/W against a central difference of log W")
    h = mp.mpf("1e-12")
    worst = mp.mpf(0)
    for k in range(1, 200):
        theta = mp.pi * k / 200
        if abs(theta - mp.pi / 2) < mp.mpf("0.05"):
            continue
        num = (mp.log(amp_rational(theta + h)) - mp.log(amp_rational(theta - h))) / (2 * h)
        worst = max(worst, abs(num - log_deriv(theta)))
    print(f"      max |closed form - central difference| = {mp.nstr(worst, 5)}")
    assert worst < mp.mpf("1e-18")

    print("(P3b) sup |Im(W'/W)| on the retained set |theta - pi/2| >= 1")
    best, arg = mp.mpf(0), None
    N = 4000
    for k in range(1, N):
        theta = mp.pi * k / N
        if abs(theta - mp.pi / 2) < 1:
            continue
        v = abs(mp.im(log_deriv(theta)))
        if v > best:
            best, arg = v, theta
    print(f"      sup = {mp.nstr(best, 8)} at theta = {mp.nstr(arg, 8)}")
    print(f"      so any M with M + 1 > {mp.nstr(best, 6)} makes Phi_M strictly increasing;")
    print(f"      M >= {int(math.ceil(float(best)))} suffices on the whole retained set")
    assert best < 50

    print("(P3c) the blow-up at theta = pi/2 is real: Im(W'/W) stays bounded")
    for e in ["1e-1", "1e-2", "1e-3", "1e-4", "1e-6"]:
        theta = mp.pi / 2 + mp.mpf(e)
        d = log_deriv(theta)
        print(f"      theta = pi/2 + {e:>6}: Re = {mp.nstr(mp.re(d), 8):>14}"
              f"   Im = {mp.nstr(mp.im(d), 8):>14}")
    d = log_deriv(mp.pi / 2 + mp.mpf("1e-6"))
    assert abs(mp.re(d)) > mp.mpf("1e5")
    assert abs(mp.im(d)) < 10

    print("(P3d) sign and size of Im(W'/W) at sample angles of the retained set")
    for t in ["0.1", "0.4", "0.5", "1.0", "2.6", "2.9", "3.0"]:
        theta = mp.mpf(t)
        if theta <= 0 or theta >= mp.pi:
            continue
        d = log_deriv(theta)
        print(f"      theta = {t:>4}: psi' = Im(W'/W) = {mp.nstr(mp.im(d), 10)}")

    print("(P3e) psi' is of ONE sign, and the band is narrow")
    lo = mp.mpf(10) ** 9
    hi = -lo
    N = 20000
    for k in range(1, N):
        theta = mp.pi * k / N
        if abs(theta - mp.pi / 2) < mp.mpf("1e-3"):
            continue
        v = mp.im(log_deriv(theta))
        lo, hi = min(lo, v), max(hi, v)
    print(f"      psi' ranges over [{mp.nstr(lo, 10)}, {mp.nstr(hi, 10)}]")
    assert lo > 0
    assert hi < mp.mpf("1.1667")
    # the two ends are the extremes, and both are rational limits
    print(f"      theta -> 0+  : psi' -> {mp.nstr(mp.im(log_deriv(mp.mpf('1e-12'))), 12)}"
          f"   (7/6 = {mp.nstr(mp.mpf(7)/6, 12)})")
    print(f"      theta -> pi- : psi' -> {mp.nstr(mp.im(log_deriv(mp.pi - mp.mpf('1e-12'))), 12)}"
          f"   (47/63 = {mp.nstr(mp.mpf(47)/63, 12)})")
    assert abs(mp.im(log_deriv(mp.mpf("1e-12"))) - mp.mpf(7) / 6) < mp.mpf("1e-9")
    assert abs(mp.im(log_deriv(mp.pi - mp.mpf("1e-12"))) - mp.mpf(47) / 63) < mp.mpf("1e-9")
    print("      so kappa = 7/6 serves the whole arc, and M >= 1 clears it: M + 1 >= 2 > 7/6")


def psi_closed(t):
    """The closed form of `psi'` as a rational function of `tau`."""
    return 1 + 2 * (t**4 + t**2 + 1) / (t**4 + 3) - mp.mpf(2) / 3 - 2 * (
        2 * t**2 + 1) / (3 * (t**2 + 2))


def check_P5():
    print("(P5) psi' is a rational function of tau alone")
    worst = mp.mpf(0)
    N = 3000
    for k in range(1, N):
        theta = mp.pi * k / N
        if abs(theta - mp.pi / 2) < mp.mpf("1e-3"):
            continue
        worst = max(worst, abs(mp.im(log_deriv(theta)) - psi_closed(tau_closed(theta))))
    print(f"      max |Im(W'/W) - closed form| over the arc = {mp.nstr(worst, 6)}")
    assert worst < mp.mpf("1e-25")
    for name, t, exact in [("tau = 1     (theta -> 0)", mp.mpf(1), mp.mpf(7) / 6),
                           ("tau = 1/sqrt3 (theta = pi/2)", 1 / mp.sqrt(3), mp.mpf(11) / 14),
                           ("tau = 1/2   (theta -> pi)", mp.mpf(1) / 2, mp.mpf(47) / 63)]:
        v = psi_closed(t)
        print(f"      {name:<28} psi' = {mp.nstr(v, 12)}  = {mp.nstr(exact, 12)}")
        assert abs(v - exact) < mp.mpf("1e-30")
    # the bound the Lean proof uses, and that it is not tight
    hi = max(psi_closed(mp.mpf(k) / 2000) for k in range(1, 2001))
    lo = min(psi_closed(mp.mpf(k) / 2000) for k in range(1, 2001))
    print(f"      over 0 < tau <= 1: psi' in [{mp.nstr(lo, 8)}, {mp.nstr(hi, 8)}], bound used = 1.5")
    assert hi <= mp.mpf("1.5")
    assert lo >= mp.mpf("-1.5")


def check_P4():
    print("(P4) the endpoints of the retained set at the deleted window |t-pi/2|<1")
    for theta in [mp.pi / 2 - 1, mp.pi / 2 + 1]:
        d = log_deriv(theta)
        print(f"      theta = {mp.nstr(theta, 8)}: |W| = {mp.nstr(abs(amp_rational(theta)), 8)}"
              f"   psi' = {mp.nstr(mp.im(d), 8)}")
        assert abs(amp_rational(theta)) > mp.mpf("1e-3")


if __name__ == "__main__":
    check_P1()
    check_P2()
    check_P3()
    check_P4()
    check_P5()
    print("ALL PASS")
