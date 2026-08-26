r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude).

Targets `cor:linear-phase-variation` and `eq:linear-phase-variation` at a zero of `B` lying
**on** the viewing arc, where the manuscript's statement sums the variation over the
components of `(0,\pi/r) \setminus \{W=0\}`.  `linear_phase_variation_components_regular`
covers that case; what is measured here is the value the summed variation actually takes on
the tree's own witness pencil, against the constants the corollary produces.

The witness pencil already in the tree is exactly such a case, which is worth stating because
it is not obvious from either side: `B = 3t^2+1` vanishes at `t = \pm i/\sqrt3`, and the branch
of `Q = (1-t)^3`, `r = 1` passes through `i/\sqrt3` at `\theta = \pi/2` -- `\tau(\pi/2)` is
`1/\sqrt3` to every digit checked below.  So `cubicQ`/`witB` is not merely a convenient pencil
for this question, it is a pencil on the excluded side of it, and `pi/2` is the single angle of
the amplitude divisor `cubicWitness_hinterior` already carries.

What is checked: the summed variation over the two components is finite, converges as the
excised collar around the divisor shrinks, and sits under `\kappa_0 + (\mathcal{K}_\gamma +
\pi)\deg B` with the constants computed rather than assumed.  `\mathcal{K}_\gamma` is the total
rotation of the branch's tangent, which is what `lem:viewing-angle` charges the vantage point.

The branch is used in closed form, `tau = tan((theta-pi)/3)/(tan((theta-pi)/3)cos theta -
sin theta)`, for the reason recorded in `check_anchored_window_counts.py`: a root-finder is
solving the zero function at `theta = 0` and is cube-root conditioned near it.
"""

from mpmath import (mp, mpf, mpc, fabs, im, re, exp, pi, log, tan, cos, sin, sqrt,
                    diff, quad, arg, polyroots)

mp.dps = 60

I = mpc(0, 1)
DEG_B = 2
DIVISOR = pi / 2


def tau(theta):
    T = tan((theta - pi) / 3)
    return T / (T * cos(theta) - sin(theta))


def gamma(theta):
    r"""The principal point `t_+(\theta) = \tau(\theta)e^{i\theta}` of `eq:principal-pair`."""
    return tau(theta) * exp(I * theta)


def zbranch(theta):
    t = gamma(theta)
    z = -(1 - t) ** 3 / t
    assert fabs(im(z)) < mpf(10) ** (-40), f"z left the reals at {theta}"
    return re(z)


def Bpoly(t):
    return 3 * t ** 2 + 1


def W(theta):
    t = gamma(theta)
    return -Bpoly(t) / (-3 * (1 - t) ** 2 + zbranch(theta))


# --------------------------------------------------------------------------
# 1. The divisor really is on the arc, and it is a simple zero of W.
# --------------------------------------------------------------------------

t_div = gamma(DIVISOR)
assert fabs(tau(DIVISOR) - 1 / sqrt(3)) < mpf(10) ** (-45), \
    f"tau(pi/2) = {mp.nstr(tau(DIVISOR),20)} is not 1/sqrt(3); the divisor is not on the branch"
assert fabs(Bpoly(t_div)) < mpf(10) ** (-40), \
    f"B does not vanish at the branch point over pi/2: {Bpoly(t_div)}"
print(f"PASS  the branch meets a zero of B on the arc: tau(pi/2) = 1/sqrt(3) = "
      f"{mp.nstr(tau(DIVISOR), 20)}, B(gamma(pi/2)) = {mp.nstr(fabs(Bpoly(t_div)), 6)}")

# and it is the ONLY one on the arc: the other zero of B is the conjugate, off the upper branch
other = [r for r in polyroots([mpf(3), mpf(0), mpf(1)]) if im(r) < 0]
assert len(other) == 1 and fabs(other[0] + I / sqrt(3)) < mpf(10) ** (-40), \
    "B's second zero is not the conjugate; the divisor may have more than one point"
print("PASS  the divisor is the single angle pi/2 -- B's other zero is the conjugate, "
      "which lies on the reflected branch")


# --------------------------------------------------------------------------
# 2. The summed variation over the components, as the collar shrinks.
#    Var_I arg W = \int_I |Im (W'/W)| d\theta.
# --------------------------------------------------------------------------

def dlog_im(f, theta):
    return im(diff(f, theta) / f(theta))


def variation(f, lo, hi):
    return quad(lambda th: fabs(dlog_im(f, th)), [lo, hi])


# The quadrature is validated against a case with an exact answer before it is trusted on
# one without: `arg gamma(theta) = theta` identically, since `gamma = tau e^{i theta}` with
# `tau > 0`, so the variation of `arg gamma` over any interval MUST be its length.
for lo, hi in ((mpf('0.001'), mpf('0.8')), (mpf('0.8'), mpf('1.5')), (mpf('1.65'), mpf('2.4'))):
    v = variation(gamma, lo, hi)
    assert fabs(v - (hi - lo)) < mpf(10) ** (-25), \
        f"the variation quadrature is wrong: Var arg gamma on ({lo},{hi}) came out {v}, " \
        f"not the span {hi - lo}"
print("PASS  variation quadrature validated: Var arg gamma equals the angular span exactly")

print()
prev = None
for eps in (mpf('1e-2'), mpf('1e-3'), mpf('1e-4'), mpf('1e-5')):
    lo = variation(W, eps, DIVISOR - eps)
    hi = variation(W, DIVISOR + eps, pi - eps)
    total = lo + hi
    print(f"      collar eps = {mp.nstr(eps,4):>8s}   Var(0,pi/2) = {mp.nstr(lo,10)}   "
          f"Var(pi/2,pi) = {mp.nstr(hi,10)}   sum = {mp.nstr(total,10)}")
    if prev is not None:
        assert fabs(total - prev) < mpf('0.05'), (
            f"the summed variation is NOT converging as the collar shrinks "
            f"({mp.nstr(prev,8)} -> {mp.nstr(total,8)}); `eq:linear-phase-variation` would be "
            f"infinite on this arc rather than merely unformalized")
    prev = total

summed = prev
print(f"\nPASS  summed variation over the components converges to "
      f"{mp.nstr(summed, 10)} as the collar shrinks")


# --------------------------------------------------------------------------
# 3. The bound: kappa_0 + (K_gamma + pi) deg B, with K_gamma computed.
# --------------------------------------------------------------------------

def gamma_deriv(theta):
    return diff(gamma, theta)


K_gamma = quad(lambda th: fabs(im(diff(gamma_deriv, th) / gamma_deriv(th))),
               [mpf('1e-5'), pi - mpf('1e-5')])
kappa_1 = K_gamma + pi
bound_without_k0 = kappa_1 * DEG_B

print(f"      K_gamma (total rotation of the branch tangent) = {mp.nstr(K_gamma, 10)}")
print(f"      kappa_1 = K_gamma + pi = {mp.nstr(kappa_1, 10)},  "
      f"kappa_1 * deg B = {mp.nstr(bound_without_k0, 10)}")

assert summed <= bound_without_k0, (
    f"summed variation {mp.nstr(summed,8)} exceeds kappa_1*deg B = "
    f"{mp.nstr(bound_without_k0,8)} even before kappa_0; the corollary's form would not "
    f"survive a zero of B on the arc")

slack = bound_without_k0 - summed
print(f"\nPASS  eq:linear-phase-variation holds across the divisor: "
      f"{mp.nstr(summed, 8)} <= {mp.nstr(bound_without_k0, 8)}, "
      f"slack {mp.nstr(slack, 8)} available for kappa_0")


# --------------------------------------------------------------------------
# 4. Neither constant sees B -- the uniformity separating clause 3 of
#    `thm:main` from clause 2.  K_gamma is a property of the branch alone,
#    so changing B must not move it.
# --------------------------------------------------------------------------

K_again = quad(lambda th: fabs(im(diff(gamma_deriv, th) / gamma_deriv(th))),
               [mpf('1e-5'), pi - mpf('1e-5')])
assert fabs(K_gamma - K_again) < mpf(10) ** (-20), "K_gamma is not reproducible"

# B enters `variation` and nothing else; recompute the variation at a DIFFERENT B with a
# different degree and check K_gamma is untouched, which is the whole content of "neither
# constant sees B".
def W2(theta):
    t = gamma(theta)
    return -(t ** 4 + 2) / (-3 * (1 - t) ** 2 + zbranch(theta))


v2 = variation(W2, mpf('1e-5'), pi - mpf('1e-5'))
assert v2 <= kappa_1 * 4, \
    f"at deg B = 4 the variation {mp.nstr(v2,8)} exceeds kappa_1*deg B = {mp.nstr(kappa_1*4,8)}"
print(f"PASS  kappa_1 = {mp.nstr(kappa_1, 8)} is a property of the branch alone: at "
      f"deg B = 4 (B = t^4+2, no zero on the arc) the variation is {mp.nstr(v2, 8)} "
      f"<= {mp.nstr(kappa_1 * 4, 8)}, with the same kappa_1")

# A numerical coincidence worth naming, so a later reader does not take it for structure.
# The summed variation and `K_gamma` both come out at 2.6180, agreeing to five digits, and both
# sit at `5 pi/6`.  It is a coincidence of this pencil's totals, not an identity: on
# sub-intervals the two separate cleanly -- on `(0.001, 0.8)` the variation of `arg W` is
# 0.7926 against 0.5946 for `arg gamma'`.  The check below pins that separation, so if a
# future edit makes the two agree pointwise it will fail rather than read as confirmation.
sub_W = variation(W, mpf('0.001'), mpf('0.8'))
sub_G = variation(gamma_deriv, mpf('0.001'), mpf('0.8'))
assert fabs(sub_W - sub_G) > mpf('0.15'), (
    f"Var arg W and Var arg gamma' agree on a subinterval ({mp.nstr(sub_W,8)} vs "
    f"{mp.nstr(sub_G,8)}); the global near-equality is then structural or a bug in the "
    f"variation, and either way this script's constants need re-deriving")
print(f"PASS  the global agreement of the summed variation with K_gamma is coincidence: "
      f"on (0.001, 0.8) they are {mp.nstr(sub_W, 8)} and {mp.nstr(sub_G, 8)}")

print("ALL PASS  check_phase_variation_on_divisor.py")
