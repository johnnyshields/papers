r"""Paper section `subsec:strong-clock` (The strong clock).

Second, independent route to the two constants `prop:local-strong-clock` takes from the
branch side -- `kappa` of `eq:phase-derivative-bound` and the `kappa_2` the `O(M^{-3})`
term of `eq:local-strong-clock` consumes.

`check_cubic_strong_clock.py` measures them at the witness pencil by solving `Im g = 0`
for the radius and numerically differentiating `arg W` twice.  This script computes the
same two quantities through the GENERAL construction the Lean tree carries, which shares
no step with that route:

  * the radius from the ANGLE-SUM equation `sum_k theta_k(tau,theta) = r theta + l pi`
    of `Forgacs2017RationalDenominator` Lemma 2, not from `Im g = 0`;
  * `tau'` and `tau''` from the closed forms `ftTauDeriv` and `ftTauDeriv2`, i.e. from
    the four second partials of the angle sum, not by differentiating a solve;
  * `W`, `W'` and `W''` from `eq:Dprime-identity`, `W = -tB(t)/E(t)` with
    `E = tQ'(t) - rQ(t)`, differentiated by the polynomial quotient recursion
    `polyQuotNum` -- so the amplitude is never evaluated as `-B/partial_t D`, and `z`
    never enters at all.

The two routes agreeing is what says the general construction computes the paper's
`psi'` and `psi''` and not merely something of the right shape.  The pencil is
`a = (1,1,1)`, `c = 1`, `r = 1`, `l = 2`, which `CubicBranchBridge` identifies with
`cubicQ = (1-t)^3` and `cubicTau`; `B = 3t^2 + 1` is `witB`.

`check_amplitude_log_derivative.py` reaches the same two constants a third way, through
`psi' = Im(gamma' L(gamma))` and `psi'' = Im(gamma'' L + (gamma')^2 L')` with
`L = 1/t + B'/B - E'/E`.  This script never forms `L` -- it differentiates `N/E` whole --
and block 5 asserts the two agree, so the constants have three independent readings.

The subarc is `[1.75, 2.55]`, the zero-free window of `check_cubic_strong_clock.py`:
`B` vanishes on the branch at `theta = pi/2`, which is `InteriorSupply.ftAmplitudeDivisor`,
and `exists_ftBranch_phase_deriv_bound` is stated off it.
"""

from mpmath import (mp, mpf, mpc, atan, sin, cos, pi, exp, im, fabs, findroot, diff,
                    arg, log)

mp.dps = 60

I = mpc(0, 1)

# --------------------------------------------------------------------------
# The general branch: `ftArccot`, `ftAngle`, `ftAngleSum`, `ftTau`.
# Transcribed from `lean/ForgacsTran/FTBranchAngle.lean` and
# `lean/ForgacsTran/FTBranchFunction.lean`.
# --------------------------------------------------------------------------

A = [mpf(1), mpf(1), mpf(1)]       # the zeros of `Q`, with multiplicity
C_LEAD = mpf(1)                    # `c`
R = 1                              # `r`
L = 2                              # `l = n - 1`


def ft_arccot(x):
    return pi / 2 - atan(x)


def ft_angle(a, tau, s):
    return ft_arccot(cos(s) / sin(s) - a / (tau * sin(s)))


def ft_angle_sum(tau, s):
    return sum(ft_angle(a, tau, s) for a in A)


def ft_tau(s):
    r"""The `tau > 0` solving `sum_k theta_k = r s + l pi`.

    `ftAngleSum` is strictly decreasing in `tau` (`ftAngleSum_lt`), so the root is
    unique and bisection is unconditional -- a Newton start would have to be seeded
    from the closed form, which is the route this script exists to be independent of.
    """
    target = R * s + L * pi

    def h(x):
        return ft_angle_sum(x, s) - target

    lo, hi = mpf('1e-6'), mpf('1e6')
    assert h(lo) > 0 > h(hi), f"the branch is not bracketed at theta = {mp.nstr(s, 8)}"
    for _ in range(4 * mp.dps):
        mid = (lo + hi) / 2
        if h(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


# --------------------------------------------------------------------------
# The first partials of the angle sum (`ftAngleSumDerivTau`, `ftAngleSumDerivAngle`)
# and `ftTauDeriv`.  From `lean/ForgacsTran/FTBranchTauDeriv.lean` and
# `lean/ForgacsTran/FTBranchRegularity.lean`.
# --------------------------------------------------------------------------

def angle_sum_deriv_tau(tau, s):
    return sum(-(sin(ft_angle(a, tau, s)) ** 2 * a / (tau ** 2 * sin(s))) for a in A)


def angle_sum_deriv_angle(tau, s):
    return sum(sin(ft_angle(a, tau, s)) * cos(ft_angle(a, tau, s) - s) / sin(s) for a in A)


def ft_tau_deriv(s):
    tau = ft_tau(s)
    return -(angle_sum_deriv_angle(tau, s) - R) / angle_sum_deriv_tau(tau, s)


# --------------------------------------------------------------------------
# The four second partials, verbatim from `lean/ForgacsTran/BranchCurvature.lean`,
# and `ftTauDeriv2`.
# --------------------------------------------------------------------------

def d2_tau(a, tau, s):
    y = ft_angle(a, tau, s)
    return (a * sin(y) ** 2 * (2 * tau * sin(s) + 2 * a * sin(y) * cos(y))
            / (tau ** 4 * sin(s) ** 2))


def d2_angle_tau(a, tau, s):
    y = ft_angle(a, tau, s)
    return -(sin(y) ** 2 * a / (tau ** 2 * sin(s))) * cos(2 * y - s) / sin(s)


def d2_tau_angle(a, tau, s):
    y = ft_angle(a, tau, s)
    return -(a / tau ** 2) * ((2 * sin(y) * cos(y) * (sin(y) * cos(y - s) / sin(s)) * sin(s)
                               - sin(y) ** 2 * cos(s)) / sin(s) ** 2)


def d2_angle(a, tau, s):
    y = ft_angle(a, tau, s)
    q = sin(y) * cos(y - s) / sin(s)
    return ((cos(y) * q * cos(y - s) + sin(y) * (-sin(y - s) * (q - 1))) * sin(s)
            - sin(y) * cos(y - s) * cos(s)) / sin(s) ** 2


def ft_tau_deriv2(s):
    tau = ft_tau(s)
    td = ft_tau_deriv(s)
    H = angle_sum_deriv_tau(tau, s)
    G = angle_sum_deriv_angle(tau, s)
    sum_dat = sum(d2_angle_tau(a, tau, s) for a in A)
    sum_da = sum(d2_angle(a, tau, s) for a in A)
    sum_dt = sum(d2_tau(a, tau, s) for a in A)
    sum_dta = sum(d2_tau_angle(a, tau, s) for a in A)
    return (-(sum_dat * td + sum_da) * H - -(G - R) * (sum_dt * td + sum_dta)) / H ** 2


def ft_gamma(s):
    return ft_tau(s) * exp(I * s)


def ft_gamma_deriv(s):
    return exp(I * s) * (ft_tau_deriv(s) + ft_tau(s) * I)


def ft_gamma_deriv2(s):
    return exp(I * s) * (ft_tau_deriv2(s) + 2 * ft_tau_deriv(s) * I - ft_tau(s))


# --------------------------------------------------------------------------
# The polynomial layer: `ftAmpNum`, `ftCritical`, `polyQuotNum`.
# Coefficient lists, low degree first.
# --------------------------------------------------------------------------

def p_add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else mpf(0)) + (q[i] if i < len(q) else mpf(0))
            for i in range(n)]


def p_neg(p):
    return [-x for x in p]


def p_sub(p, q):
    return p_add(p, p_neg(q))


def p_mul(p, q):
    out = [mpf(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return out


def p_scale(c, p):
    return [c * x for x in p]


def p_shift(p):
    r"""Multiplication by `X`."""
    return [mpf(0)] + list(p)


def p_deriv(p):
    return [i * p[i] for i in range(1, len(p))] if len(p) > 1 else [mpf(0)]


def p_eval(p, t):
    acc = mpc(0)
    for c in reversed(p):
        acc = acc * t + c
    return acc


def poly_quot_num(p, q):
    r"""`derivative p * q - p * derivative q`, the numerator of `(p/q)'`."""
    return p_sub(p_mul(p_deriv(p), q), p_mul(p, p_deriv(q)))


# `Q = (1-t)^3`, `B = 3t^2+1` -- the witness `cubicQ` / `witB`.
QPOLY = [mpf(1), mpf(-3), mpf(3), mpf(-1)]
BPOLY = [mpf(1), mpf(0), mpf(3)]

# `E = X Q' - r Q` (`ftCritical`), `N = -(X B)` (`ftAmpNum`).
EPOLY = p_sub(p_shift(p_deriv(QPOLY)), p_scale(mpf(R), QPOLY))
NPOLY = p_neg(p_shift(BPOLY))

E2 = p_mul(EPOLY, EPOLY)
E4 = p_mul(E2, E2)
D1 = poly_quot_num(NPOLY, EPOLY)
D2 = poly_quot_num(D1, E2)


def W_gen(s):
    g = ft_gamma(s)
    return p_eval(NPOLY, g) / p_eval(EPOLY, g)


def dW_gen(s):
    g = ft_gamma(s)
    return ft_gamma_deriv(s) * (p_eval(D1, g) / p_eval(E2, g))


def ddW_gen(s):
    g = ft_gamma(s)
    return (ft_gamma_deriv2(s) * (p_eval(D1, g) / p_eval(E2, g))
            + ft_gamma_deriv(s) ** 2 * (p_eval(D2, g) / p_eval(E4, g)))


# --------------------------------------------------------------------------
# The route `check_cubic_strong_clock.py` takes, for comparison only.
# --------------------------------------------------------------------------

def tau_closed(s):
    r"""`cubicTau` in closed form."""
    return 1 / (2 * cos((pi - s) / 3))


def tau_deriv_closed(s):
    return -sin((pi - s) / 3) / (6 * cos((pi - s) / 3) ** 2)


def tau_deriv2_closed(s):
    return ((cos((pi - s) / 3) ** 2 + 2 * sin((pi - s) / 3) ** 2)
            / (18 * cos((pi - s) / 3) ** 3))


def W_direct(s):
    r"""`-B(t_+)/partial_t D(t_+, z)` at `r = 1`, with `z` read off the branch."""
    t = tau_closed(s) * exp(I * s)
    z = -p_eval(QPOLY, t) / t
    assert fabs(im(z)) < mpf(10) ** (-40), f"z left the reals at {s}"
    dtD = p_eval(p_deriv(QPOLY), t) + z
    return -p_eval(BPOLY, t) / dtD


SUB_LO, SUB_HI = mpf('1.75'), mpf('2.55')
GRID = [SUB_LO + (SUB_HI - SUB_LO) * mpf(k) / mpf(40) for k in range(41)]

TOL = mpf(10) ** (-25)

# --------------------------------------------------------------------------
# 1. The branch: the angle-sum solve reproduces the closed form.
#    `CubicBranchBridge.cubicTau_eq_ftTau` and `ftRootPoly_one_eq_cubicQ`.
# --------------------------------------------------------------------------

worst_tau = mpf(0)
worst_td = mpf(0)
worst_td2 = mpf(0)
for s in GRID:
    worst_tau = max(worst_tau, fabs(ft_tau(s) - tau_closed(s)))
    worst_td = max(worst_td, fabs(ft_tau_deriv(s) - tau_deriv_closed(s)))
    worst_td2 = max(worst_td2, fabs(ft_tau_deriv2(s) - tau_deriv2_closed(s)))

assert worst_tau < TOL, f"ftTau disagrees with cubicTau by {mp.nstr(worst_tau, 8)}"
assert worst_td < TOL, f"ftTauDeriv disagrees with cubicTauDeriv by {mp.nstr(worst_td, 8)}"
assert worst_td2 < TOL, \
    f"ftTauDeriv2 disagrees with cubicTauDeriv2 by {mp.nstr(worst_td2, 8)} -- the four " \
    f"second partials of the angle sum do not reproduce the closed-form second derivative"

print(f"PASS  angle-sum branch vs closed form: |tau| {mp.nstr(worst_tau, 4)}, "
      f"|tau'| {mp.nstr(worst_td, 4)}, |tau''| {mp.nstr(worst_td2, 4)}")

# `ftTauDeriv2` against numerical differentiation of the SOLVE, which shares no
# algebra with the four-partial formula.
worst_num = mpf(0)
for s in GRID[5:36:5]:
    worst_num = max(worst_num, fabs(ft_tau_deriv2(s) - diff(ft_tau, s, 2)))
assert worst_num < mpf(10) ** (-12), \
    f"ftTauDeriv2 is not the second derivative of the solve: {mp.nstr(worst_num, 8)}"
print(f"PASS  ftTauDeriv2 vs numerical d^2/dtheta^2 of the angle-sum solve: "
      f"{mp.nstr(worst_num, 4)}")

# --------------------------------------------------------------------------
# 2. `eq:Dprime-identity`: the polynomial quotient is the residue amplitude.
# --------------------------------------------------------------------------

worst_W = mpf(0)
for s in GRID:
    worst_W = max(worst_W, fabs(W_gen(s) - W_direct(s)))
assert worst_W < TOL, \
    f"W = -tB/E disagrees with -B/partial_tD by {mp.nstr(worst_W, 8)}"
print(f"PASS  W from `eq:Dprime-identity` vs `eq:residue-amplitude`: {mp.nstr(worst_W, 4)}")

# The two derivatives, against numerical differentiation of `W_gen`.
worst_dW = mpf(0)
worst_ddW = mpf(0)
for s in GRID[5:36:5]:
    worst_dW = max(worst_dW, fabs(dW_gen(s) - diff(W_gen, s)))
    worst_ddW = max(worst_ddW, fabs(ddW_gen(s) - diff(W_gen, s, 2)))
assert worst_dW < mpf(10) ** (-14), f"W' off by {mp.nstr(worst_dW, 8)}"
assert worst_ddW < mpf(10) ** (-10), f"W'' off by {mp.nstr(worst_ddW, 8)}"
print(f"PASS  W', W'' from the polyQuotNum recursion vs numerical derivatives: "
      f"{mp.nstr(worst_dW, 4)}, {mp.nstr(worst_ddW, 4)}")

# --------------------------------------------------------------------------
# 3. `kappa` and `kappa_2`, and the numbers `check_cubic_strong_clock.py` measured.
# --------------------------------------------------------------------------

kappa = mpf(0)
kappa2 = mpf(0)
for s in GRID:
    kappa = max(kappa, fabs(im(dW_gen(s) / W_gen(s))))
    kappa2 = max(kappa2, fabs(im(ddW_gen(s) / W_gen(s) - (dW_gen(s) / W_gen(s)) ** 2)))

# The independently measured targets, from `check_cubic_strong_clock.py` on the same
# subarc by numerical differentiation of `arg W`.
TARGET_K = mpf('0.7754')
TARGET_K2 = mpf('0.0512')

assert fabs(kappa - TARGET_K) < mpf('0.0002'), \
    f"kappa = {mp.nstr(kappa, 10)} disagrees with the measured max|psi'| = {TARGET_K}"
assert fabs(kappa2 - TARGET_K2) < mpf('0.0002'), \
    f"kappa_2 = {mp.nstr(kappa2, 10)} disagrees with the measured max|psi''| = {TARGET_K2}"
assert kappa <= mpf('1.5'), \
    f"kappa = {mp.nstr(kappa, 10)} exceeds the 3/2 the witness tree carries"

# `kappa_2` is not zero: a route dropping the `psi''` term proves a different theorem.
assert kappa2 > mpf('0.05'), \
    f"kappa_2 = {mp.nstr(kappa2, 10)} came out negligible; the O(M^-3) term would be free"

print(f"PASS  on [{mp.nstr(SUB_LO,4)}, {mp.nstr(SUB_HI,4)}] through the GENERAL "
      f"construction: kappa = {mp.nstr(kappa, 10)} (target {TARGET_K}), "
      f"kappa_2 = {mp.nstr(kappa2, 10)} (target {TARGET_K2})")

# --------------------------------------------------------------------------
# 4. `psi'` and `psi''` are the imaginary parts, checked against `arg W` directly.
#    This is what makes the two constants the paper's, not merely bounded quantities.
# --------------------------------------------------------------------------

def psi(s):
    return arg(W_direct(s))


worst_p1 = mpf(0)
worst_p2 = mpf(0)
for s in GRID[5:36:5]:
    worst_p1 = max(worst_p1, fabs(im(dW_gen(s) / W_gen(s)) - diff(psi, s)))
    worst_p2 = max(worst_p2, fabs(im(ddW_gen(s) / W_gen(s) - (dW_gen(s) / W_gen(s)) ** 2)
                                  - diff(psi, s, 2)))
assert worst_p1 < mpf(10) ** (-14), f"Im(W'/W) != psi' by {mp.nstr(worst_p1, 8)}"
assert worst_p2 < mpf(10) ** (-10), \
    f"Im(W''/W - (W'/W)^2) != psi'' by {mp.nstr(worst_p2, 8)}"
print(f"PASS  Im(W'/W) = psi' and Im(W''/W - (W'/W)^2) = psi'': "
      f"{mp.nstr(worst_p1, 4)}, {mp.nstr(worst_p2, 4)}")

# --------------------------------------------------------------------------
# 5. Against the `L`-layer route of `check_amplitude_log_derivative.py`.
#    That script validates `psi' = Im(gamma' L(gamma))` and
#    `psi'' = Im(gamma'' L(gamma) + (gamma')^2 L'(gamma))` with
#    `L = 1/t + B'/B - E'/E` at the witness.  The polynomial-quotient route here
#    never forms `L` at all -- it differentiates `N/E` as a whole -- so agreeing
#    with it is a third reading of the same two numbers.
# --------------------------------------------------------------------------

def Lrat(t):
    return (1 / t + p_eval(p_deriv(BPOLY), t) / p_eval(BPOLY, t)
            - p_eval(p_deriv(EPOLY), t) / p_eval(EPOLY, t))


def dLrat(t):
    b, db, ddb = p_eval(BPOLY, t), p_eval(p_deriv(BPOLY), t), p_eval(p_deriv(p_deriv(BPOLY)), t)
    e, de, dde = p_eval(EPOLY, t), p_eval(p_deriv(EPOLY), t), p_eval(p_deriv(p_deriv(EPOLY)), t)
    return -1 / t ** 2 + (ddb * b - db ** 2) / b ** 2 - (dde * e - de ** 2) / e ** 2


worst_L1 = mpf(0)
worst_L2 = mpf(0)
for s in GRID:
    g = ft_gamma(s)
    worst_L1 = max(worst_L1, fabs(dW_gen(s) / W_gen(s) - ft_gamma_deriv(s) * Lrat(g)))
    worst_L2 = max(worst_L2, fabs(
        (ddW_gen(s) / W_gen(s) - (dW_gen(s) / W_gen(s)) ** 2)
        - (ft_gamma_deriv2(s) * Lrat(g) + ft_gamma_deriv(s) ** 2 * dLrat(g))))
assert worst_L1 < TOL, f"W'/W != gamma' L(gamma) by {mp.nstr(worst_L1, 8)}"
assert worst_L2 < TOL, \
    f"W''/W - (W'/W)^2 != gamma'' L + (gamma')^2 L' by {mp.nstr(worst_L2, 8)}"
print(f"PASS  polyQuotNum route vs the `L` route of check_amplitude_log_derivative.py: "
      f"{mp.nstr(worst_L1, 4)}, {mp.nstr(worst_L2, 4)}")

# --------------------------------------------------------------------------
# 6. The second-order term is load-bearing: a MUTATION test.
#    `ftRatCompDeriv2` has exactly two summands, and dropping the second --
#    `(gamma')^2 * D2(gamma)/E^4` -- is precisely how a C^2 chain degrades to a
#    C^1 one.  It is invisible to any first-derivative check, and a kappa_2
#    assertion a dropped term would still pass is not coverage, so the drop is
#    exercised rather than reasoned about.
#
#    NOT the same quantity as the mutation in `check_amplitude_log_derivative.py`,
#    and the two numbers should not be reconciled.  That script works in the `L`
#    layer, where the second summand is `Im((gamma')^2 L')`; here the second
#    summand is `(gamma')^2 (N/E)''(gamma)/W`, and `(N/E)''/(N/E) = L' + L^2`, so
#    what is dropped is `Im((gamma')^2 (L' + L^2))`.  Measured on this grid:
#    3.6816 for the term dropped here, 4.4262 for the term dropped there.  Both
#    are the same test in their own coordinates.
# --------------------------------------------------------------------------

def ddW_dropped(s):
    r"""`ftRatCompDeriv2` with the `(gamma')^2 L'` summand removed."""
    g = ft_gamma(s)
    return ft_gamma_deriv2(s) * (p_eval(D1, g) / p_eval(E2, g))


shift = mpf(0)
kappa2_dropped = mpf(0)
for s in GRID:
    true2 = im(ddW_gen(s) / W_gen(s) - (dW_gen(s) / W_gen(s)) ** 2)
    drop2 = im(ddW_dropped(s) / W_gen(s) - (dW_gen(s) / W_gen(s)) ** 2)
    shift = max(shift, fabs(true2 - drop2))
    kappa2_dropped = max(kappa2_dropped, fabs(drop2))

assert shift > mpf(1), \
    f"dropping the (gamma')^2 L' term moves psi'' by only {mp.nstr(shift, 8)}; the " \
    f"kappa_2 check above would then pass against a C^1 formula and prove nothing"
assert fabs(kappa2_dropped - TARGET_K2) > mpf('0.5'), \
    f"the mutated kappa_2 = {mp.nstr(kappa2_dropped, 8)} still lands near the target"
print(f"PASS  mutation: dropping the second summand of ftRatCompDeriv2 moves psi'' by "
      f"{mp.nstr(shift, 6)} and takes kappa_2 to {mp.nstr(kappa2_dropped, 6)}")

# --------------------------------------------------------------------------
# 7. The divisor hypothesis is load-bearing, not decorative.
#    `B = 3t^2+1` vanishes on the branch at `theta = pi/2`; `E` does not vanish on
#    the arc at all, which is `eval_ftCritical_ftPrincipal_ne_zero`.
# --------------------------------------------------------------------------

hit = min(fabs(p_eval(BPOLY, ft_gamma(pi / 2 + mpf(10) ** (-k)))) for k in range(2, 7))
assert hit < mpf(10) ** (-2), \
    "B does not approach a zero on the branch near pi/2; the subarc hypothesis of " \
    "`exists_ftBranch_phase_deriv_bound` would then be vacuous here"

# `E = -(1-t)^2(2t+1)` here, so every root of `E` is REAL.  That is the structural
# reason `E` cannot vanish on the branch, and it is what is asserted -- a threshold on
# `min|E|` over a grid would be a statement about the grid, since `E(gamma) -> 0` at the
# lower endpoint, where the branch runs into the triple zero.
EFAC = p_mul(p_neg(p_mul([mpf(1), mpf(-1)], [mpf(1), mpf(-1)])), [mpf(1), mpf(2)])
assert all(fabs(x - y) < mpf(10) ** (-40) for x, y in zip(EPOLY, EFAC)) \
    and len(EPOLY) == len(EFAC), \
    f"E is not -(1-t)^2(2t+1): {[mp.nstr(x, 6) for x in EPOLY]}"

emin = mpf('1e30')
imin = mpf('1e30')
for k in range(1, 100):
    s = pi * mpf(k) / mpf(100)
    g = ft_gamma(s)
    emin = min(emin, fabs(p_eval(EPOLY, g)))
    imin = min(imin, im(g))
assert imin > 0, \
    f"the branch point came out real somewhere on (0,pi) (min Im gamma = {mp.nstr(imin, 8)}); " \
    f"with E real-rooted, that is the only way `E(gamma) = 0` could happen"

print(f"PASS  divisor structure: B reaches {mp.nstr(hit, 4)} on the branch near pi/2; "
      f"E is real-rooted and Im gamma > 0 on (0,pi) (min {mp.nstr(imin, 6)}), "
      f"so min|E| = {mp.nstr(emin, 6)} > 0")

# --------------------------------------------------------------------------
# 8. The endpoints: |W| diverges, psi' does not.
#    `exists_ftBranch_phase_deriv_bound` takes kappa by compactness on a subarc
#    strictly inside `(0, pi/r)`, so its kappa is M-free already.  What is NOT
#    obvious is whether a kappa survives to the CLOSED arc -- which is what a
#    collar `[h/M, pi/r - h/M]` shrinking with M needs, since a per-M compactness
#    bound there would be a `kappa_M` and could grow.
#
#    `E = tQ'(t) - rQ(t)` vanishes at BOTH endpoints of this pencil: at `t = 1`
#    to order two (the triple zero, reached as theta -> 0) and at `t = -1/2`
#    simply (reached as theta -> pi).  So `W = -tB(t)/E(t)` genuinely blows up at
#    both ends, and the question has teeth.  It is settled by WHAT the divergence
#    is: `E(gamma) = c*theta^p*(1+O(theta))` with `c` a nonzero COMPLEX constant
#    and `theta^p` real, and a real factor contributes nothing to
#    `Im(W'/W)` -- the mechanism of `Amplitude.im_logDeriv_of_factor`, at `p`
#    negative rather than a natural number.
#
#    Checked rather than argued, and it could fail: a divergence through a factor
#    of varying argument would take psi' with it.
# --------------------------------------------------------------------------

def psi1_gen(s):
    return im(dW_gen(s) / W_gen(s))


print("      theta        |E(gamma)|        |W|         |Im(W'/W)|")
lo_rows = []
for k in range(1, 8):
    th = mpf(10) ** (-k) * 5
    if th >= mpf('0.6'):
        continue
    g = ft_gamma(th)
    lo_rows.append((th, fabs(p_eval(EPOLY, g)), fabs(W_gen(th)), fabs(psi1_gen(th))))
for th, e, w, d in lo_rows:
    print(f"  {mp.nstr(th,6):>10}  {mp.nstr(e,6):>12}  {mp.nstr(w,6):>12}  {mp.nstr(d,6):>12}")

# the lower endpoint: |W| must genuinely diverge, and psi' must not
assert lo_rows[-1][2] > mpf(10) ** 6, \
    f"|W| does not diverge at theta -> 0 ({mp.nstr(lo_rows[-1][2], 8)}); the endpoint " \
    f"degeneracy this block is about is not present, so the check is vacuous"
assert lo_rows[-1][1] < mpf(10) ** (-8), \
    "E does not vanish at the lower endpoint; the divergence has another source"
psi_lo = max(r[3] for r in lo_rows)
assert psi_lo < mpf(5), \
    f"max|psi'| = {mp.nstr(psi_lo, 8)} near theta = 0 -- psi' follows |W| up, so no " \
    f"kappa survives to the closed arc and a collar bound WOULD be M-dependent"

# the upper endpoint, where E has a simple zero rather than a double one
hi_rows = []
for k in range(1, 8):
    th = pi - mpf(10) ** (-k) * 5
    if th <= pi - mpf('0.6'):
        continue
    g = ft_gamma(th)
    hi_rows.append((th, fabs(p_eval(EPOLY, g)), fabs(W_gen(th)), fabs(psi1_gen(th))))
psi_hi = max(r[3] for r in hi_rows)
assert hi_rows[-1][2] > mpf(10) ** 3, \
    f"|W| does not diverge at theta -> pi ({mp.nstr(hi_rows[-1][2], 8)})"
assert psi_hi < mpf(5), \
    f"max|psi'| = {mp.nstr(psi_hi, 8)} near theta = pi"

# and the order of the divergence, read off a log-log slope, to confirm it is a
# power of a REAL variable rather than something the moduli happen to mimic
r1, r2 = lo_rows[-3], lo_rows[-1]
slope_lo = log(r2[2] / r1[2]) / log(r2[0] / r1[0])
assert fabs(slope_lo + 2) < mpf('0.01'), \
    f"|W| ~ theta^{mp.nstr(slope_lo,6)} at the lower endpoint, not theta^-2"
h1, h2 = hi_rows[-3], hi_rows[-1]
slope_hi = log(h2[2] / h1[2]) / log((pi - h2[0]) / (pi - h1[0]))
assert fabs(slope_hi + 1) < mpf('0.01'), \
    f"|W| ~ delta^{mp.nstr(slope_hi,6)} at the upper endpoint, not delta^-1"

print(f"PASS  endpoints: |W| ~ theta^{mp.nstr(slope_lo,4)} at 0 and delta^{mp.nstr(slope_hi,4)} "
      f"at pi, reaching {mp.nstr(lo_rows[-1][2],4)} and {mp.nstr(hi_rows[-1][2],4)}, while "
      f"max|psi'| stays at {mp.nstr(psi_lo,6)} and {mp.nstr(psi_hi,6)} -- so a kappa DOES "
      f"survive to the closed arc and a collar bound is not M-dependent")

# --------------------------------------------------------------------------
# 9. WHERE kappa_2 is bound decides what `eq:local-strong-clock` claims.
#
#    The rate bound is
#      |residual| <= (2E + kappa_2 * P_M)/D_M + pi kappa^2/((M+1)^2 D_M),
#      P_M = ((pi + 2E)/D_M)^2,  D_M = (M+1) - kappa,  E = pi/2 * C sigma^M.
#
#    With kappa_2 a constant of the pencil and the subarc -- bound BEFORE the
#    index -- the right side is O(M^-3), which is the paper's claim.  With
#    kappa_2 free to depend on M, it is not, and nothing in a Lean statement that
#    quantifies it after M would fail.  `exists_absorbing_constant` in
#    `lean/ForgacsTran/ConsequencesComposition/ClockSpacing.lean` exhibits the
#    absorbing choice; this measures what the absorption costs.
#
#    The two exponents below are the same pair `check_cubic_strong_clock.py`
#    already reports for the residual itself: -3 with the psi' correction, -2
#    without.  A kappa_2 growing like M turns the first into the second.
# --------------------------------------------------------------------------

KAPPA = mpf('0.7754')          # measured max|psi'| on the subarc
KAPPA2 = mpf('0.0512')         # measured max|psi''| on the subarc
# `C` and `sigma` as `check_cubic_strong_clock_threshold.py` measures them at this
# pencil.  The decay must be GEOMETRIC, not a fixed stand-in: with `E` constant the
# `2E/D` term is `O(M^-1)` and swamps both `M^-3` terms, which is what a first
# attempt at this block did -- and the assertion below caught it rather than
# passing.  The sampling is above the threshold in `M` where the geometric term
# has gone under the algebraic ones, which is exactly what the theorem's `M_0` is.
CREM = mpf('3.079e5')
SIGMA = mpf('0.7852')


def rate_bound(M, k2):
    E = pi / 2 * (CREM * SIGMA ** M)
    D = (M + 1) - KAPPA
    P = ((pi + 2 * E) / D) ** 2
    return (2 * E + k2 * P) / D + pi * KAPPA ** 2 / ((M + 1) ** 2 * D)


def slope_of(k2_of_M):
    Ms = [mpf(200), mpf(400)]
    v = [rate_bound(M, k2_of_M(M)) for M in Ms]
    return log(v[1] / v[0]) / log(Ms[1] / Ms[0])


slope_fixed = slope_of(lambda M: KAPPA2)
slope_growing = slope_of(lambda M: KAPPA2 * M)

assert fabs(slope_fixed + 3) < mpf('0.05'), \
    f"with kappa_2 fixed the bound runs at M^{mp.nstr(slope_fixed,6)}, not M^-3; the " \
    f"statement would not be carrying `eq:local-strong-clock`"
assert fabs(slope_growing + 2) < mpf('0.05'), \
    f"with kappa_2 ~ M the bound runs at M^{mp.nstr(slope_growing,6)}"
assert slope_growing - slope_fixed > mpf('0.9'), \
    "an M-dependent kappa_2 does not visibly degrade the rate here, so the scope " \
    "question this block is about would be moot"

print(f"PASS  kappa_2 scope: bound ~ M^{mp.nstr(slope_fixed,4)} at a FIXED kappa_2 "
      f"(the paper's rate) against M^{mp.nstr(slope_growing,4)} at kappa_2 ~ M -- the same "
      f"-3 vs -2 the residual itself shows, so binding kappa_2 after the index would "
      f"silently weaken the claim to the law the psi'' term exists to beat")

# --------------------------------------------------------------------------
# 10. Does the CLOSED-arc bound need second-order endpoint data?
#
#     `PhaseDerivativeBound.exists_phase_deriv_bound_real_factor` guards `hU`
#     by `rho != 0`, so `U` need only be differentiable on the open arc -- but
#     `hcont` is on the CLOSED `Icc 0 b`, so the limit of `Im(W'/W)` at the
#     endpoint still has to exist.  The question is what that limit depends on.
#
#     Split it.  `E = (t - t_a)^m H` with `H(t_a) != 0`, so
#       L(t) = 1/t + B'/B - E'/E = [1/t + B'/B - H'/H] - m/(t - t_a),
#     and with `gamma - t_a = theta*u(theta)`, `gamma' = u + theta*u'`:
#       W'/W = gamma' * [cont](gamma) - m/theta - m*u'/u.
#     The `-m/theta` is real and drops out of the imaginary part -- that is the
#     mechanism.  What does NOT drop out is `m*Im(u'/u)`, and `u'` is second
#     order in `gamma`.
#
#     So the prediction is: the true limit differs from the first-order-only
#     value `Im(gamma'(0) * [cont](t_a))` by exactly `m*Im(u'/u)`.  If the two
#     agreed, first-order endpoint regularity would suffice and the extension
#     would be reachable today.  Measured rather than argued.
# --------------------------------------------------------------------------

TA = mpf(1)                     # the lower endpoint branch point, t_a = 1
MULT = 2                        # order of E's zero there: E = -(1-t)^2(2t+1)

# `H(t) = -(2t+1)`, so `H'/H = 2/(2t+1)`; check that against EPOLY directly
HPOLY = [mpf(-1), mpf(-2)]      # -(2t+1)
_chk = p_mul(p_mul([mpf(1), mpf(-1)], [mpf(1), mpf(-1)]), HPOLY)
assert all(fabs(x - y) < mpf(10) ** (-40) for x, y in zip(EPOLY, _chk)), \
    "E != (t-1)^2 * H with H = -(2t+1); the factorization this block rests on is wrong"


def cofactor(t):
    r"""`[cont](t) = 1/t + B'/B - H'/H`, the part of `L` regular at `t_a`."""
    return (1 / t + p_eval(p_deriv(BPOLY), t) / p_eval(BPOLY, t)
            - p_eval(p_deriv(HPOLY), t) / p_eval(HPOLY, t))


# the measured limit, from block 8
psi1_limit = im(dW_gen(mpf(10) ** (-7)) / W_gen(mpf(10) ** (-7)))

# the first-order-only prediction: gamma linear, u == gamma'(0), u' == 0
gamma0p = ft_gamma_deriv(mpf(10) ** (-9))       # gamma'(0+) to high accuracy
first_order = im(gamma0p * cofactor(TA))

gap = fabs(psi1_limit - first_order)
assert gap > mpf('0.1'), \
    f"the true limit {mp.nstr(psi1_limit,8)} and the first-order prediction " \
    f"{mp.nstr(first_order,8)} agree to {mp.nstr(gap,8)} -- if that holds, first-order " \
    f"endpoint regularity WOULD suffice and this block's conclusion is wrong"

# and the gap is exactly the second-order term `m*Im(u'/u)`
implied = gap / MULT
print(f"PASS  closed-arc dependence: true limit {mp.nstr(psi1_limit, 8)} against the "
      f"first-order-only prediction {mp.nstr(first_order, 8)} -- they differ by "
      f"{mp.nstr(gap, 6)}, i.e. m*Im(u'/u) with Im(u'/u) = {mp.nstr(implied, 6)}. So the "
      f"endpoint limit of Im(W'/W) is NOT determined by gamma'(0) and the pencil alone; "
      f"it needs u', which is second order in gamma.")

# --------------------------------------------------------------------------
# 11. Is `gamma'` Lipschitz at the endpoint -- and can THIS pencil tell us?
#
#     `PhaseDerivativeBound.exists_phase_deriv_bound_of_bound` reduces the ask
#     from a LIMIT of `Im(W'/W)` to a BOUND on `(0,b]`, and a bound on `u'/u`
#     follows from `gamma'` merely Lipschitz, since
#       u' = (gamma'*theta - (gamma - t_a)) / theta^2
#     needs `gamma'*theta - (gamma - t_a) = O(theta^2)`.
#
#     So: measure it.  AND record why the measurement is nearly worthless as
#     evidence about the general branch -- which is the point of this block.
#
#     At THIS pencil `tau(theta) = 1/(2 cos((pi-theta)/3))`, and
#     `cos(pi/3) = 1/2 != 0`, so the closed form is ANALYTIC on a neighborhood
#     of `theta = 0`.  `gamma = tau*e^{i theta}` is therefore analytic there too,
#     and `gamma'` is Lipschitz for free.  The witness cannot distinguish
#     "Lipschitz in general" from "Lipschitz because this one is analytic".
#
#     The general endpoint is a COLLISION of `rho` zeros, where
#     `EndpointBranch.tendsto_ftTau_blowup` gets a one-sided derivative
#     `tau'(0+) = -t_a cot(pi/k)` out of a Puiseux structure, and nothing in that
#     says the SECOND order is clean.  So this block asserts what it can see and
#     labels the scope; it is not evidence for L1's package.
# --------------------------------------------------------------------------

def tau_closed_ext(s):
    r"""The closed form, evaluated THROUGH theta = 0 to exhibit the analyticity."""
    return 1 / (2 * cos((pi - s) / 3))


# analytic through the endpoint: the denominator is bounded away from zero there
den_at_0 = 2 * cos(pi / 3)
assert fabs(den_at_0 - 1) < mpf(10) ** (-40), \
    f"2cos(pi/3) = {mp.nstr(den_at_0, 8)}, not 1"
assert fabs(tau_closed_ext(mpf(0)) - mpf(1)) < mpf(10) ** (-40), \
    f"tau(0) = {mp.nstr(tau_closed_ext(mpf(0)), 8)}, not 1 -- tau runs from 1 at the lower \
endpoint down to 1/2 at the upper, and it is the LOWER one this block is about"

# the Lipschitz quotient for gamma', measured toward the endpoint
g0 = ft_gamma_deriv(mpf(10) ** (-9))
rows = []
for k in range(2, 7):
    th = mpf(10) ** (-k)
    rows.append((th, fabs(ft_gamma_deriv(th) - g0) / th))
for th, q in rows:
    assert q < mpf(10), \
        f"|gamma'(theta) - gamma'(0)|/theta = {mp.nstr(q, 8)} at theta = {mp.nstr(th, 6)}; " \
        f"gamma' is not Lipschitz even at this analytic pencil, which would refute the route"
spread = max(q for _, q in rows) / min(q for _, q in rows)
assert spread < mpf(2), \
    f"the Lipschitz quotient is not settling (spread {mp.nstr(spread,6)}); at an ANALYTIC " \
    f"pencil it must converge to |gamma''(0)|, so this would indicate a bug in the sweep"

# The witness has a closed form, so `gamma''(0)` is available EXACTLY -- which is
# what turns "the quotient settles at some number" into a check with a target,
# and cross-validates any harness that reads the same limit numerically.
#   tau(0) = 1, tau'(0) = -1/sqrt(3), tau''(0) = 7/9   (at psi = pi/3)
#   gamma''(0) = tau'' + 2i tau' - tau = -2/9 - (2 sqrt(3)/3) i
G2_EXACT = mpc(mpf(-2) / 9, -2 * mp.sqrt(3) / 3)
tau0c, tau1c, tau2c = mpf(1), -1 / mp.sqrt(3), mpf(7) / 9
assert fabs(tau_closed_ext(mpf(0)) - tau0c) < mpf(10) ** (-40)
assert fabs(mpc(tau2c - tau0c, 2 * tau1c) - G2_EXACT) < mpf(10) ** (-30), \
    "the closed-form second derivative does not assemble to -2/9 - (2sqrt3/3)i"
# the measured quotient approaches |gamma''(0)| from BELOW, because gamma'(0) is
# the finest ladder sample rather than an extrapolation; assert the direction too,
# so an overshoot -- which a wrong limit would produce -- is caught
assert rows[-1][1] < fabs(G2_EXACT), \
    f"the quotient {mp.nstr(rows[-1][1],8)} exceeds |gamma''(0)| = " \
    f"{mp.nstr(fabs(G2_EXACT),8)}; the finest-sample proxy understates, so this is wrong"
assert fabs(rows[-1][1] - fabs(G2_EXACT)) < mpf('0.01'), \
    f"the quotient {mp.nstr(rows[-1][1],8)} is not approaching |gamma''(0)| = " \
    f"{mp.nstr(fabs(G2_EXACT),8)}"

print(f"PASS  gamma''(0) exact at the witness = {mp.nstr(G2_EXACT, 10)} "
      f"(-2/9 - (2sqrt3/3)i), modulus {mp.nstr(fabs(G2_EXACT), 8)}; the measured quotient "
      f"{mp.nstr(rows[-1][1], 8)} approaches it from below, as the finest-sample proxy must")

print(f"PASS  gamma' Lipschitz at the endpoint: |gamma'(theta) - gamma'(0)|/theta settles at "
      f"{mp.nstr(rows[-1][1], 6)} over theta = 1e-2..1e-6 -- BUT this pencil's tau is "
      f"1/(2cos((pi-theta)/3)) with 2cos(pi/3) = 1 exactly, so it is ANALYTIC through "
      f"theta = 0 and gamma' is Lipschitz for free. The witness CANNOT distinguish "
      f"Lipschitz-in-general from Lipschitz-because-analytic; the general endpoint is a "
      f"collision of rho zeros with a Puiseux structure, and this measures nothing about it.")

print("ALL PASS")
