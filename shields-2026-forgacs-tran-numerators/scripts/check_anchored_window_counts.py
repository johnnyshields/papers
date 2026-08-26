r"""Paper subsection `subsec:proof` (Angular discrepancy and proof of the main theorem).

Targets `eq:angular-discrepancy` on the windows the existing coverage EXCLUDES.

The formalized cubic instance of `prop:angular-discrepancy` counts only windows that
straddle the midpoint of the arc with `2h/M` clearance at both ends.  Two families are left
out, and `cor:angular-rigidity` consumes exactly one of them: `eq:angular-clock` brackets a
zero's index between counts on windows **anchored** at the endpoint, `alpha = 0`, which the
clearance condition forbids.  Whether the bound survives there is not a formality -- the
branch degenerates at both ends of the arc, the deleted window of `eq:retained-range` sits at
`h/M`, and if the endpoint contributed a number of zeros growing with `M` the rigidity
corollary would be false as stated rather than merely unformalized.

Three families are swept here, over the witness pencil `Q = (1-t)^3`, `r = 1`, `B = 3t^2+1`:

  anchored-low    (0, beta)          the family `eq:angular-clock` needs
  anchored-high   (alpha, pi)        its mirror, where the branch runs to infinity
  interior-offset (alpha, beta)      not straddling pi/2, the other excluded family

The discrepancy is reported as a MAXIMUM over each family and tracked across a ladder in `M`,
so a constant that is really growing shows up as growth rather than as one lucky sample.

All counting is done on `G_M(theta) = tau^{M+1}F_M(z(theta))`, whose zeros in `theta`
correspond one-to-one to the zeros of `F_M` in the angular window because `z` is strictly
monotone along the branch.  `F_M` is evaluated through the defining recurrence of
`eq:F-M-def`, never Horner, and a precision-adequacy margin is asserted at every `M`.

THE BRANCH IS IN CLOSED FORM HERE, and using it rather than a root-finder is what makes the
anchored family measurable at all.  With `Q = (1-t)^3` and `r = 1`, `z` is real exactly when
`3\arg(1-t) - \theta \equiv 0 \pmod \pi`, and taking real and imaginary parts of
`1 - \tau e^{i\theta} = \rho e^{i\varphi}` at `\varphi = (\theta-\pi)/3` solves for `\tau`
outright:

    tau(theta) = tan((theta-pi)/3) / (tan((theta-pi)/3) cos theta - sin theta).

A root-finder on `\Im g = 0` cannot be used at the very place this script needs to look.  At
`theta = 0` the whole ray is real, so `\Im g` vanishes IDENTICALLY and `findroot` is solving
the zero function -- it returns whatever its starting point drifts to, silently.  Approaching
`theta = 0` it is barely better: `Q` has a triple zero at `t = 1`, so the solve is cube-root
conditioned there and loses two thirds of its digits, and `Im g` carries a second positive
zero above 1 that an unbracketed start falls into.  A first version of this script used
`findroot` and reported the anchored discrepancy GROWING with `M`, which would have refuted
`eq:angular-discrepancy` on the family `cor:angular-rigidity` consumes.  It was an artifact of
the solver at the anchor.  The closed form is checked against the solver in the interior, where
the solver is sound, so the two routes are cross-validated rather than one simply replacing the
other.
"""

from mpmath import (mp, mpf, mpc, fabs, im, re, exp, pi, findroot, log, tan, cos, sin,
                    polyroots)

mp.dps = 170

I = mpc(0, 1)
BCO = [mpf(1), mpf(0), mpf(3)]


def tau(theta):
    r"""The branch radius in closed form; see the module docstring for the derivation."""
    T = tan((theta - pi) / 3)
    den = T * cos(theta) - sin(theta)
    assert fabs(den) > mpf(10) ** (-40), (
        f"branch parameterization degenerate at theta={theta}; at theta = pi/r the principal "
        f"pair collides on the real axis, which is why the arc of `eq:ab-def` is open there")
    v = T / den
    assert v > 0, f"branch radius nonpositive at theta={theta}: {v}"
    return v


def tau_by_solver(theta):
    """The same radius by root-finding, for the interior cross-check only.

    The root is BRACKETED before it is refined, and that is not a nicety.  `Im g` has a
    second positive zero above 1, and a Newton start fixed at 0.9 falls into it for
    `theta` below about `2pi/15` -- the two routes then disagree by up to 0.39 relative
    while both are individually converged.  The minimum-modulus branch is the SMALLEST
    positive zero, so scanning (0,1] for the first sign change and refining inside that
    bracket picks it by construction, with no appeal to the closed form being tested.
    """
    e = exp(I * theta)
    f = lambda x: im((1 - x * e) ** 3 / (x * e))
    steps = 4000
    prev_x = mpf(1) / mpf(steps)
    prev = f(prev_x)
    for i in range(2, steps + 1):
        x = mpf(i) / mpf(steps)
        v = f(x)
        if prev == 0:
            return prev_x
        if (prev < 0) != (v < 0):
            return findroot(f, (prev_x, x), solver='anderson', tol=mpf(10) ** (-120))
        prev_x, prev = x, v
    raise AssertionError(f"no sign change of Im g on (0,1] at theta={theta}")


def zbranch(theta):
    t = tau(theta) * exp(I * theta)
    z = -(1 - t) ** 3 / t
    assert fabs(im(z)) < mpf(10) ** (-60), f"z left the reals at theta={theta}"
    return re(z)


# Two routes to the same radius, converging in the interior where the solver is sound.
# The comparison runs on [0.5, pi - 0.1] ONLY.  Outside that the solver is not a valid
# second route and a disagreement would say nothing: at `theta = 0` it is solving the zero
# function, and near it the triple zero of `Q` at `t = 1` makes the solve cube-root
# conditioned.  Restricting to where the reference instrument is sound is the point of a
# two-route check; comparing against it where it is known broken is not.
worst_route = mpf(0)
for k in range(0, 31):
    th = mpf('0.5') + (pi - mpf('0.1') - mpf('0.5')) * mpf(k) / mpf(30)
    a, b = tau(th), tau_by_solver(th)
    worst_route = max(worst_route, fabs(a - b) / fabs(b))
    # and the defining property, on the closed form: t_+ is a MINIMUM-modulus root of D
    t = a * exp(I * th)
    zz = -(1 - t) ** 3 / t
    assert fabs(im(zz)) < mpf(10) ** (-60), f"closed form left the reals at {th}"
    rts = polyroots([mpf(-1), mpf(3), re(zz) - 3, mpf(1)], maxsteps=200, extraprec=300)
    assert fabs(fabs(t) - min(fabs(r) for r in rts)) < mpf(10) ** (-25), \
        f"closed-form branch is not the minimum-modulus root at theta={th}"
assert worst_route < mpf(10) ** (-40), \
    f"closed form and solver disagree by {mp.nstr(worst_route,8)} relative"
print(f"PASS  closed-form branch agrees with the root-finder to "
      f"{mp.nstr(worst_route, 6)} relative on [0.5, pi-0.1], and is the minimum-modulus "
      f"root of D at every one of those angles")


def coeff_F(M, z):
    c = []
    for m in range(M + 1):
        v = BCO[m] if m < len(BCO) else mpf(0)
        if m >= 1:
            v -= (z - 3) * c[m - 1]
        if m >= 2:
            v -= 3 * c[m - 2]
        if m >= 3:
            v += c[m - 3]
        c.append(v)
    return c[M], max(fabs(x) for x in c)


def G(M, theta):
    val, big = coeff_F(M, zbranch(theta))
    margin = mp.dps - (log(max(big, mpf(1))) / log(10))
    assert margin > 40, \
        f"precision margin collapsed to {mp.nstr(margin,6)} digits at M={M}; raise mp.dps"
    return tau(theta) ** (M + 1) * val


def count_zeros(M, lo, hi, per_expected=14):
    """Count sign changes of `G_M` on (lo, hi), sampling densely enough to resolve them.

    The expected spacing is `pi/(M+1)`, so the sample count is pinned to the window's
    expected zero count rather than to a fixed number -- a fixed grid would under-resolve
    the wide windows and waste time on the narrow ones.  `per_expected` samples per
    expected zero is a 7-fold oversample of the Nyquist rate for a `cos((M+1)theta - psi)`.
    """
    expected = (M + 1) * (hi - lo) / pi
    samples = max(200, int(per_expected * float(expected)) + 50)
    n = 0
    prev = G(M, lo)
    for k in range(1, samples + 1):
        th = lo + (hi - lo) * mpf(k) / mpf(samples)
        v = G(M, th)
        if prev != 0 and v != 0 and (prev < 0) != (v < 0):
            n += 1
        prev = v
    return n, expected


LADDER = [30, 45, 65, 95, 140]

FAMILIES = {
    "anchored-low   (0, beta)": [
        (mpf(0), b) for b in
        (mpf('0.40'), mpf('0.90'), mpf('1.60'), mpf('2.30'), mpf('2.90'))
    ],
    # The arc `(0, pi/r)` is OPEN at the top, and it has to be: at `theta = pi` the
    # principal pair `t_\pm = \tau e^{\pm i\theta}` collides on the negative real axis, so
    # `eq:principal-pair` has no two distinct members there and the branch parameterization
    # is a genuine `0/0`.  The upper-anchored family therefore runs to `pi` exclusive.  The
    # exclusion costs no zero: the spacing is `pi/(M+1)`, and the gap left here is below
    # `10^{-30}` at every `M` in the ladder.
    "anchored-high  (alpha, pi-)": [
        (a, pi - mpf(10) ** (-30)) for a in
        (mpf('0.25'), mpf('0.90'), mpf('1.60'), mpf('2.30'), mpf('2.95'))
    ],
    "interior-offset (no pi/2)": [
        (mpf('0.20'), mpf('1.40')), (mpf('0.35'), mpf('1.50')),
        (mpf('1.70'), mpf('2.60')), (mpf('1.90'), mpf('3.00')),
        (mpf('0.10'), mpf('0.80')), (mpf('2.40'), mpf('3.05')),
    ],
}

results = {}
for name, windows in FAMILIES.items():
    print(f"\n  {name}")
    per_M = []
    for M in LADDER:
        worst = mpf(0)
        worst_w = None
        for (a, b) in windows:
            n, expected = count_zeros(M, a, b)
            d = fabs(mpf(n) - expected)
            if d > worst:
                worst, worst_w = d, (a, b, n, expected)
        per_M.append(worst)
        a, b, n, expected = worst_w
        print(f"      M = {M:4d}   worst |Z - (M+1)(b-a)/pi| = {mp.nstr(worst, 6):>10s}"
              f"   at (a,b) = ({mp.nstr(a,3)}, {mp.nstr(b,3)})"
              f"   Z = {n}, expected = {mp.nstr(expected, 7)}")
    results[name] = per_M

    # The claim is a CONSTANT: the discrepancy must not grow with M.  A bound that
    # grows even logarithmically would refute `eq:angular-discrepancy` on this family.
    first_half = max(per_M[:2])
    second_half = max(per_M[-2:])
    assert second_half <= first_half + 1, (
        f"discrepancy GROWS with M on the {name} family: "
        f"{mp.nstr(first_half,6)} at small M against {mp.nstr(second_half,6)} at large M -- "
        f"eq:angular-discrepancy would be false as stated on these windows, not merely "
        f"unformalized")
    assert max(per_M) < mpf(6), \
        f"discrepancy {mp.nstr(max(per_M),6)} on {name} is larger than any plausible C_0 + C_1 K"

allworst = max(max(v) for v in results.values())
print(f"\nPASS  every family bounded and non-growing across M = {LADDER[0]}..{LADDER[-1]}; "
      f"worst discrepancy anywhere = {mp.nstr(allworst, 6)}")


# --------------------------------------------------------------------------
# The endpoint contributes O(1) zeros, not O(M) -- the mechanism behind the
# anchored bound, checked directly rather than inferred from the totals above.
# The deleted window of `eq:retained-range` has width h/M, so it can hold at
# most about h/pi zeros however large M is.
# --------------------------------------------------------------------------

print()
for h in (mpf(1), mpf(3), mpf(8)):
    counts = []
    for M in LADDER:
        n, _ = count_zeros(M, mpf(10) ** (-9), h / mpf(M), per_expected=40)
        counts.append(n)
    cap = int(float(h / pi)) + 2
    print(f"      h = {mp.nstr(h,3):>5s}   zeros in (0, h/M] across the ladder: {counts}"
          f"   cap h/pi + 2 = {cap}")
    assert max(counts) <= cap, \
        f"the deleted endpoint window (0, {h}/M] holds {max(counts)} zeros, above the " \
        f"h/pi + 2 = {cap} its width allows -- the endpoint is NOT an O(1) contribution"

print("\nPASS  the endpoint window holds O(1) zeros at every M, which is why anchoring "
      "at alpha = 0 costs only a constant")
print("ALL PASS  check_anchored_window_counts.py")
