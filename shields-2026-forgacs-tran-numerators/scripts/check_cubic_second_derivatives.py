r"""Paper subsection `subsec:strong-clock` (Local phase quantization and strong-clock spacing).

Targets the second-derivative layer `eq:local-strong-clock`'s `O(M^{-3})` term consumes, at the
witness pencil `Q = (1-t)^3`, `r = 1`, `B = 3t^2 + 1`.

`eq:phase-derivative-bound` gives `psi' = Im(W'/W)` with `W'/W = gamma' L(gamma)` for a fixed
rational `L`, so `psi'' = Im(gamma'' L(gamma) + (gamma')^2 L'(gamma))`.  The Lean tree asserts
five closed forms to get there, and each is checked here against numerical differentiation
rather than re-derived by hand:

    tau    = 1/(2 cos phi),  phi = (pi - theta)/3          `cubicTau_closed_form`
    tau'   = -sin phi / (6 cos phi ^ 2)                    `cubicTauDeriv`
    tau''  = (cos phi ^ 2 + 2 sin phi ^ 2)/(18 cos phi^3)  `cubicTauDeriv2`
    gamma' = e^{i theta}(tau' + i tau)                     `cubicGammaDeriv`
    gamma''= e^{i theta}(tau'' + 2 i tau' - tau)           `cubicGammaDeriv2`
    L(t)   = 1/t + 6t/(3t^2+1) + 2/(1-t) - 2/(2t+1)        `cubicAmpLogDeriv`
    L'(t)  = -1/t^2 + 6(1-3t^2)/(3t^2+1)^2
             + 2/(1-t)^2 + 4/(2t+1)^2                      `cubicAmpLogDeriv2`
    W''    = (L'(gamma)gamma'' -> logd' , plus logd^2) W   `cubicAmpDeriv2`

`tau''` is kept in the `sin`/`cos` form the quotient rule produces rather than reduced to
`(2 - cos^2)/(18 cos^3)`; both are asserted equal here, because the Lean chose the unreduced
form precisely so that no Pythagorean rewrite stands between the statement and its proof, and
a reader meeting the reduced form elsewhere should be able to see they are the same function.

TWO CLOSED FORMS FOR THE BRANCH ARE IN CIRCULATION and they are asserted equal here.  The Lean
tree carries `1/(2 cos((pi-theta)/3))`; the anchored-window script carries
`tan((theta-pi)/3)/(tan((theta-pi)/3) cos theta - sin theta)`, obtained by solving the real and
imaginary parts of `1 - tau e^{i theta} = rho e^{i phi}`.  Nothing checks that those are the
same function, and if they were not, one of two scripts would be measuring the wrong branch.

Numerical differentiation is `mpmath.diff` at 60 digits, never a finite difference in float64.
The midpoint `theta = pi/2` is skipped throughout: `B` vanishes on the branch there, which is
the whole amplitude divisor at this pencil, and `psi` jumps by `pi` across it -- a different
hypothesis, not a numerical inconvenience.
"""

from mpmath import mp, mpf, mpc, fabs, pi, cos, sin, tan, exp, diff

mp.dps = 60

I = mpc(0, 1)
TOL = mpf(10) ** (-25)


def phi(t):
    return (pi - t) / 3


def tau(t):
    return 1 / (2 * cos(phi(t)))


def tau1(t):
    return -sin(phi(t)) / (6 * cos(phi(t)) ** 2)


def tau2(t):
    return (cos(phi(t)) ** 2 + 2 * sin(phi(t)) ** 2) / (18 * cos(phi(t)) ** 3)


def tau2_reduced(t):
    return (2 - cos(phi(t)) ** 2) / (18 * cos(phi(t)) ** 3)


def tau_script(t):
    """The anchored-window script's closed form, for the cross-check."""
    T = tan((t - pi) / 3)
    return T / (T * cos(t) - sin(t))


def gam(t):
    return tau(t) * exp(I * t)


def gam1(t):
    return exp(I * t) * (tau1(t) + I * tau(t))


def gam2(t):
    return exp(I * t) * (tau2(t) + 2 * I * tau1(t) - tau(t))


def L(x):
    return 1 / x + 6 * x / (3 * x ** 2 + 1) + 2 / (1 - x) - 2 / (2 * x + 1)


def Lp(x):
    return (-1 / x ** 2 + 6 * (1 - 3 * x ** 2) / (3 * x ** 2 + 1) ** 2
            + 2 / (1 - x) ** 2 + 4 / (2 * x + 1) ** 2)


def W(t):
    g = gam(t)
    return g * (3 * g ** 2 + 1) / ((1 - g) ** 2 * (2 * g + 1))


def logd(t):
    """`cubicAmpLogDeriv`."""
    return gam1(t) * L(gam(t))


def logd2(t):
    """`cubicAmpLogDeriv2`."""
    return gam2(t) * L(gam(t)) + gam1(t) ** 2 * Lp(gam(t))


def ddW(t):
    """`cubicAmpDeriv2`, which the tree defines as `(L' + L^2)W`."""
    return (logd2(t) + logd(t) ** 2) * W(t)


# --------------------------------------------------------------------------
# The two closed forms for the branch radius are the same function.
# --------------------------------------------------------------------------

worst_forms = mpf(0)
for k in range(1, 2000):
    th = pi * mpf(k) / mpf(2000)
    worst_forms = max(worst_forms, fabs(tau(th) - tau_script(th)) / fabs(tau(th)))
assert worst_forms < mpf(10) ** (-40), \
    f"the Lean tree's tau and the anchored-window script's tau are different functions: " \
    f"{mp.nstr(worst_forms, 8)} relative"
print(f"PASS  1/(2 cos((pi-theta)/3)) and tan((theta-pi)/3)/(tan(...)cos theta - sin theta) "
      f"agree to {mp.nstr(worst_forms, 6)} relative on 1999 interior angles")
assert fabs(tau(mpf(0)) - 1) < TOL and fabs(tau(pi) - mpf('0.5')) < TOL, \
    "the branch endpoints are not tau(0) = 1 and tau(pi) = 1/2"
print("      endpoints check out: tau(0) = 1 (the triple zero) and tau(pi) = 1/2")


# --------------------------------------------------------------------------
# Every asserted derivative against numerical differentiation.
# --------------------------------------------------------------------------

claims = {
    "tau'   (cubicTauDeriv)":        (tau1, lambda t: diff(tau, t)),
    "tau''  (cubicTauDeriv2)":       (tau2, lambda t: diff(tau1, t)),
    "tau''  reduced == unreduced":   (tau2, tau2_reduced),
    "gamma' (cubicGammaDeriv)":      (gam1, lambda t: diff(gam, t)),
    "gamma''(cubicGammaDeriv2)":     (gam2, lambda t: diff(gam1, t)),
    "L'     (the cofactor)":         (lambda t: Lp(gam(t)), lambda t: diff(L, gam(t))),
    "W'     (cubicAmpLogDeriv * W)": (lambda t: logd(t) * W(t), lambda t: diff(W, t)),
    "(W'/W)'(cubicAmpLogDeriv2)":    (logd2, lambda t: diff(logd, t)),
    "W''    (cubicAmpDeriv2)":       (ddW, lambda t: diff(lambda s: logd(s) * W(s), t)),
}

worst = {name: mpf(0) for name in claims}
samples = 0
for k in range(1, 60):
    th = pi * mpf(k) / mpf(60)
    if fabs(th - pi / 2) < mpf('0.02'):
        continue
    samples += 1
    for name, (closed, reference) in claims.items():
        worst[name] = max(worst[name], fabs(closed(th) - reference(th)))

print(f"\n      {samples} angles of (0,pi), the amplitude divisor at pi/2 excluded")
for name, v in worst.items():
    print(f"      {name:32s} worst absolute error = {mp.nstr(v, 6)}")
    assert v < TOL, f"the closed form for {name} is wrong: {mp.nstr(v, 8)}"
print("\nPASS  every closed form of the second-derivative layer matches numerical "
      "differentiation")


# --------------------------------------------------------------------------
# `psi''` on the subarc the strong-clock check uses, and it is what kappa_2 is.
# --------------------------------------------------------------------------

best = mpf(0)
best_th = None
for k in range(0, 801):
    th = mpf('1.75') + (mpf('2.55') - mpf('1.75')) * mpf(k) / mpf(800)
    v = fabs(logd2(th).imag)
    if v > best:
        best, best_th = v, th
print(f"\n      max |psi''| on [1.75, 2.55] = {mp.nstr(best, 8)} at theta = "
      f"{mp.nstr(best_th, 6)}")
assert best < mpf('0.06'), \
    f"psi'' on the subarc is {mp.nstr(best,8)}, not the small constant kappa_2 is taken to be"
print("PASS  psi'' is bounded on the subarc, and Im(cubicAmpLogDeriv2) is what bounds it")

print("\nALL PASS  check_cubic_second_derivatives.py")
