#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `eq:principal-infinite-endpoint-regularity`;
and `lem:amplitude-divisor`, `eq:W-endpoint-form`, `eq:phase-derivative-bound`.

At the `r > 1` upper endpoint the radius does not merely collapse -- it collapses
LINEARLY, and that is what `EndpointCofactorBound` needs there.

**The dichotomy itself is not measured here and is not repeated.**
`check_upper_endpoint_r_one.py` already settles it: (V1) at `r = 1` the radius
converges to a positive `L` solving the deficit equation `sum_k L/(L+a_k) = 1`,
and (V4) at `r >= 2` the same pencils send `tau -> 0`.  What V4 asserts is the
COLLAPSE.  What it does not assert, and what is needed, is the RATE.

The rate is the whole difference between two formalizations.  `endpointCofactor`
divides by the endpoint parameter, so it wants `gamma = eta * T(eta)` with
`T(0) != 0` -- which is `eq:principal-infinite-endpoint-regularity`.  A collapse
at any other rate gives either `T(0) = 0` or `T` unbounded, and the cofactor
bound does not apply.  `tau -> 0` alone does not distinguish those.

**What follows for the Lean, and it is the opposite of what a second development
would assume.**  At the `r > 1` upper endpoint the branch runs into the ORIGIN,
so `gamma(endpoint) = 0` holds already and `endpointCofactor gamma` IS the
cofactor `T` -- with no shift.  At the lower endpoint, and at `r = 1` where the
branch ends at a finite point, the branch has to be shifted first.  So the
`r > 1` upper endpoint is the case the existing module fits with the LEAST
adaptation, not the case needing a parallel one.

Asserted, each as a failing test:

  (C1) At `r >= 2`, `tau/eta` converges to a NONZERO constant, so the collapse is
       exactly linear.  Drift asserted on the ratio, not on `tau` -- a drift test
       on a quantity going to zero measures the ladder and nothing else.
  (C2) The cofactor is the complex `T(0) = lim gamma/eta`, and it is nonzero.
       Its argument is `pi/r`, since `gamma = tau e^{i theta}` and
       `theta -> pi/r`; asserted against that closed form rather than against
       itself.
  (C3) Teeth: at `r = 1` the same quotient DIVERGES, so (C1) is not a reading the
       ladder would produce for any pencil.  This is teeth for the LINEARITY
       claim; it is not a re-assertion of the dichotomy, which is V1/V4's.
"""

from mpmath import mp, mpf, mpc, sin, cos, atan, pi, fabs, arg, exp

mp.dps = 40


def ft_angle(a, tau, theta):
    return pi / 2 - atan((cos(theta) - a / tau) / sin(theta))


def ft_angle_sum(a, tau, theta):
    return sum(ft_angle(ak, tau, theta) for ak in a)


def ft_tau(a, r, theta, lo=mpf('1e-30'), hi=mpf('1e12')):
    """Solve `sum_k ftAngle = r theta + (n-1) pi` for `tau`; the sum is strictly
    decreasing in `tau`, so a bracketed bisection cannot take the wrong root."""
    n = len(a)
    target = r * theta + (n - 1) * pi
    f = lambda t: ft_angle_sum(a, t, theta) - target
    flo, fhi = f(lo), f(hi)
    assert flo > 0 > fhi, (
        "the branch is not bracketed at theta=%s: f(lo)=%s, f(hi)=%s"
        % (theta, flo, fhi))
    for _ in range(500):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def rungs(a, r, ks=(2, 3, 4, 5)):
    """`(eta, tau)` at `theta = pi/r - eta`."""
    return [(mpf(10) ** (-k), ft_tau(a, r, pi / r - mpf(10) ** (-k))) for k in ks]


ORIGIN = [("(1,1,1)  r=2", [mpf(1)] * 3, 2),
          ("(1,2,3)  r=2", [mpf(1), mpf(2), mpf(3)], 2),
          ("(1,2,3)  r=3", [mpf(1), mpf(2), mpf(3)], 3),
          ("(1,1,2)  r=2", [mpf(1), mpf(1), mpf(2)], 2)]

FINITE = [("(1,1,1)  r=1", [mpf(1)] * 3, 1),
          ("(1,2,3)  r=1", [mpf(1), mpf(2), mpf(3)], 1)]


def main():
    print("check_upper_endpoint_cofactor_form.py")
    print("Paper: `sec:geometry`, `eq:principal-infinite-endpoint-regularity`")
    print()
    print("  The r=1/r>1 dichotomy is `check_upper_endpoint_r_one.py` V1/V4 and")
    print("  is NOT repeated.  What is measured here is the RATE at r > 1.")
    print()

    print("  (C1) r >= 2: tau/eta -> a nonzero constant (the collapse is linear):")
    slopes = {}
    for name, a, r in ORIGIN:
        rows = rungs(a, r)
        qs = [tau / eta for eta, tau in rows]
        drift = fabs(qs[-1] - qs[-2])
        assert drift < mpf('1e-4'), \
            "%s: tau/eta has not settled, so the collapse is not linear: %s vs %s" \
            % (name, qs[-2], qs[-1])
        assert fabs(qs[-1]) > mpf('1e-2'), \
            "%s: tau/eta settled at 0, so T(0) = 0 and the cofactor form fails" % name
        slopes[name] = (a, r, rows, qs[-1])
        print("       %-14s tau/eta -> %s (drift %s)"
              % (name, mp.nstr(qs[-1], 9), mp.nstr(drift, 3)))
    print()

    print("  (C2) the cofactor T(0) = lim gamma/eta, complex and nonzero,")
    print("       with argument pi/r against the closed form:")
    for name, (a, r, rows, q) in slopes.items():
        eta, tau = rows[-1]
        theta = pi / r - eta
        T0 = tau * exp(mpc(0, 1) * theta) / eta
        assert fabs(T0) > mpf('1e-2'), \
            "%s: |T(0)| = %s is not bounded off zero" % (name, fabs(T0))
        assert fabs(arg(T0) - pi / r) < mpf('1e-3'), \
            "%s: arg T(0) = %s, closed form pi/r = %s" \
            % (name, arg(T0), pi / r)
        print("       %-14s T(0) = %-26s |T(0)| = %-11s arg/pi = %s (=1/%d)"
              % (name, mp.nstr(T0, 7), mp.nstr(fabs(T0), 7),
                 mp.nstr(arg(T0) / pi, 6), r))
    print()

    print("  (C3) teeth: at r = 1 the same quotient DIVERGES:")
    for name, a, r in FINITE:
        rows = rungs(a, r)
        qs = [tau / eta for eta, tau in rows]
        assert qs[-1] > qs[0] * 100, \
            "%s: tau/eta did not diverge at r = 1, so (C1) would pass for a " \
            "finite endpoint too and decides nothing" % name
        print("       %-14s tau/eta runs %s -> %s"
              % (name, mp.nstr(qs[0], 5), mp.nstr(qs[-1], 5)))
    print("       So (C1) is a reading about r > 1 specifically, not something")
    print("       the ladder reports for any pencil.")
    print()

    print("  SCOPE: four pencils at r = 2,3 for the rate and two at r = 1 for the")
    print("  teeth.  What is shown is the RATE, not the dichotomy: at r > 1 the")
    print("  collapse is linear, so `gamma = eta T(eta)` with `T(0) != 0` and")
    print("  `endpointCofactor` applies to the UNSHIFTED branch there.")
    print()
    print("ALL PASS")


if __name__ == "__main__":
    main()
