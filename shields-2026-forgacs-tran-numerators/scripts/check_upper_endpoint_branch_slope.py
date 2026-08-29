r"""Paper section `sec:geometry` (`lem:principal-endpoint-regularity`,
`eq:principal-infinite-endpoint-regularity`), at the UPPER arc endpoint with `r >= 2`.

The branch radius solves `sum_k arccot(cot(th) - a_k/(tau sin th)) = r th + l pi` with
`arccot = pi/2 - arctan` and `l = n - 1`.  At the upper endpoint of a `r >= 2` arc the
branch runs into the origin, `tau -> 0`, and the question the endpoint collar bound needs
answered is whether it does so at a nonzero RATE -- `exists_bound_im_logDeriv_ftAmp_origin`
asks for a one-sided derivative of the branch there with `dgamma(0) != 0`.

It does, and the argument is not asymptotic at all -- which is the point of this file.
`arccot` inverts exactly, with a constant that depends on the sign: `arccot(x) = arctan(1/x)`
for `x > 0` and `pi + arctan(1/x)` for `x < 0`.  Since `tau sin(th) > 0` on the arc, the sign
of `x_k = (tau cos(th) - a_k)/(tau sin(th))` is the sign of `tau cos(th) - a_k`.  So with

    m(tau, th) := #{k : tau cos(th) > a_k},

the branch equation at `l = n - 1` is, EXACTLY,

    G(tau, th) := sum_k arctan(tau sin(th) / (tau cos(th) - a_k)) - r th - (m - 1) pi = 0.

**The constant is not universal, and transferring it is the trap.**  At the origin end
`tau -> 0`, so `m = 0` and the constant is `-pi`.  At the lower endpoint with a SIMPLE
smallest zero `tau_0 > x_1`, so `m = 1` and the constant is `0`.  Both are asserted below,
and each residual is `~1e-40` at its own end and `pi` at the other.

At `(tau, th) = (0, pi/r)` we have `G = 0` and

    dG/dtau = -sin(pi/r) sum_k 1/a_k,     dG/dth = -r,

so the implicit function theorem gives `tau` as an analytic function of `th` there, with

    tau'(pi/r-) = -r / (sin(pi/r) sum_k 1/a_k),

and the expansion `tau(th) = (pi - r th)/(sin(th) sum_k 1/a_k) + O((pi/r - th)^2)` is a
consequence rather than the argument.

**The load-bearing hypothesis is the nonvanishing `dG/dtau`, not analyticity.**  `G` is
analytic at the lower endpoint too, and the IFT still does not apply there: every arctan
argument carries a factor `sin(th)`, so `dG/dtau = O(th)` and vanishes in the limit.  What
survives is `(dG/dtau)/th`, which is why the lower end needs a rescaling and this end does
not.  Do not read "analytic" as the reason this works.

`sin(pi/r)` is what makes this an `r >= 2` statement, and it is exactly why the `r = 1`
witnesses never meet this endpoint: there the arc ends at `pi`, the slope formula divides
by `sin(pi) = 0`, and the branch does not reach the origin linearly at all.

The same rearrangement at the LOWER endpoint is where the two ends part, and not in the
way one would guess.  It survives at a SIMPLE smallest zero: `tau(0+)` is not any `a_k` at
all, every denominator stays bounded away from `0`, and `G` is analytic there too.  It
fails only at a REPEATED smallest zero, where `tau(0+) = x_1` is itself a zero of the
pencil, so `tau cos(th) - x_1 -> 0` -- and it does so QUADRATICALLY, `~ -1.5 th^2` at the
witness below, which is why the first derivative vanishes there and the second is the
object `check_tau_second_derivative_limit.py` is about.  So the multiplicity governs the
ORDER of the degeneracy at the lower end, and there is no degeneracy at the upper one.

Checked at `a = (1, 2, 4)`, `n = 3`, `l = 2`, `r = 2`, so the arc is `(0, pi/2)` and the
predicted slope is `-2/(1 * 7/4) = -8/7`.  Also checked at `r = 3` and at a repeated
`a = (1, 1, 3, 3)`, to confirm the formula sees only `sum 1/a_k` and not the multiplicity
structure that governs the other end.

Every claim is an `assert`; mpmath only, no float in the loop.
"""

import mpmath as mp

mp.mp.dps = 40


def angle_sum(a, tau, th):
    """`ftAngleSum`: sum of `ftArccot(cot(th) - a_k/(tau sin(th)))`."""
    c = mp.cos(th) / mp.sin(th)
    s = mp.sin(th)
    return mp.fsum(mp.pi / 2 - mp.atan(c - ak / (tau * s)) for ak in a)


def tau(a, r, l, th):
    """Solve the branch equation for `tau` at `th`.  The sum is strictly decreasing in
    `tau`, so a bracket plus bisection is exact to working precision."""
    target = r * th + l * mp.pi
    lo, hi = mp.mpf(10) ** -60, mp.mpf(1)
    while angle_sum(a, hi, th) > target:
        hi *= 2
        assert hi < mp.mpf(10) ** 20, "no upper bracket"
    while angle_sum(a, lo, th) < target:
        lo /= 2
        assert lo > mp.mpf(10) ** -300, "no lower bracket"
    for _ in range(400):
        mid = mp.sqrt(lo * hi) if lo > 0 else (lo + hi) / 2
        if angle_sum(a, mid, th) > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def predicted_slope(a, r):
    return -mp.mpf(r) / (mp.sin(mp.pi / r) * mp.fsum(1 / mp.mpf(ak) for ak in a))


CASES = [
    ((1, 2, 4), 2, 2),
    ((1, 2, 4), 3, 2),
    ((1, 1, 3, 3), 2, 3),
]

for a, r, l in CASES:
    end = mp.pi / r
    C = predicted_slope(a, r)
    assert C < 0, (a, r, C)

    # the branch really does reach the origin at this end, and it is monotone doing so
    prev_t = None
    for k in range(1, 9):
        d = mp.mpf(10) ** (-k)
        th = end - d
        t = tau(a, r, l, th)

        # the branch equation is solved to working precision
        assert abs(angle_sum(a, t, th) - (r * th + l * mp.pi)) < mp.mpf(10) ** -25, (a, r, k)

        assert t > 0
        if prev_t is not None:
            assert t < prev_t, ("tau must decrease toward the endpoint", a, r, k)
        prev_t = t

        # the rate: the divided difference against the endpoint value `tau(pi/r) = 0`
        slope = (0 - t) / d
        err = abs(slope - C)
        assert err < mp.mpf(10) ** (-k + 1), (a, r, k, slope, C, err)

    # the slope is nonzero, which is what the collar bound's `dgamma(0) != 0` asks for
    assert abs(C) > mp.mpf("0.1"), (a, r, C)

# ---- the second-order half, which is what the collar's `hlip` reduces to ----------------
# `exists_bound_im_logDeriv_ftAmp_origin` also wants `||dgamma(th) - dgamma(0)|| <= L th`
# near the endpoint.  Through `BranchSupply.exists_lipschitz_of_bound_of_continuousWithinAt`
# that is a bound on the branch's second derivative there, and the expansion above says the
# remainder past the linear term is quadratic.  Measured as `|tau - C d| <= K d^2` with one
# `K` across eight decades, `K` estimated at the coarsest and then held fixed.
for a, r, l in CASES:
    end = mp.pi / r
    C = predicted_slope(a, r)
    K = None
    for k in range(1, 9):
        d = mp.mpf(10) ** (-k)
        t = tau(a, r, l, end - d)
        rem = abs(t - (-C) * d)
        if K is None:
            K = 4 * rem / d**2
            assert K > 0, (a, r)
        assert rem <= K * d**2, (a, r, k, rem, K * d**2)

# ---- the rearrangement is exact, which is what makes this an IFT argument ---------------
def arccot(x):
    return mp.pi / 2 - mp.atan(x)


# `arccot(x) = pi + arctan(1/x)` for `x < 0` -- Mathlib's `Real.arctan_inv_of_neg`
for x in [-mp.mpf("0.001"), -mp.mpf(1), -mp.mpf("3.7"), -mp.mpf(1000), -mp.mpf(10) ** 12]:
    assert abs(arccot(x) - (mp.pi + mp.atan(1 / x))) < mp.mpf(10) ** -35, x
# and for `x > 0` there is no `pi` at all, which is where the constant comes from
for x in [mp.mpf("0.001"), mp.mpf(1), mp.mpf("3.7"), mp.mpf(1000)]:
    assert abs(arccot(x) - mp.atan(1 / x)) < mp.mpf(10) ** -35, x


def mcount(a, tau, th):
    """`#{k : tau cos(th) > a_k}` -- the number of terms whose argument is positive, and
    so the number that contribute no `pi`."""
    return sum(1 for ak in a if tau * mp.cos(th) > mp.mpf(ak))


def G(a, r, tau, th, m=None):
    """The branch equation rearranged, at `l = n - 1`.  Exactly `0` when `tau` solves it.
    `m` defaults to the count above; passing it explicitly is how the wrong constant is
    shown to be wrong."""
    if m is None:
        m = mcount(a, tau, th)
    return (
        mp.fsum(mp.atan(tau * mp.sin(th) / (tau * mp.cos(th) - ak)) for ak in a)
        - r * th
        - (m - 1) * mp.pi
    )


# the constant is `(m-1)pi` and it DIFFERS between the two ends -- transferring it is the
# trap this block exists to close
a_c, r_c, l_c = (1, 2, 4), 2, 2
for label, th, m_here, m_there in [
    ("origin", mp.pi / r_c - mp.mpf("1e-6"), 0, 1),
    ("lower", mp.mpf("1e-6"), 1, 0),
]:
    t = tau(a_c, r_c, l_c, th)
    assert mcount(a_c, t, th) == m_here, (label, mcount(a_c, t, th))
    assert abs(G(a_c, r_c, t, th)) < mp.mpf(10) ** -30, (label, G(a_c, r_c, t, th))
    # the OTHER end's constant is wrong here, by exactly `pi`
    assert abs(abs(G(a_c, r_c, t, th, m=m_there)) - mp.pi) < mp.mpf(10) ** -30, label

# and the load-bearing hypothesis fails at the lower end: `dG/dtau` vanishes there.
# Every arctan argument carries a factor `sin(th)`, so `dG/dtau = O(th)`; what survives is
# the rescaled `(dG/dtau)/th -> -sum_k a_k/(tau_0 - a_k)^2`, which is why that end needs a
# rescaling and this one does not.
prev_err = None
for k in [3, 4, 5, 6]:
    th_lo = mp.mpf(10) ** (-k)
    t_lo = tau(a_c, r_c, l_c, th_lo)
    d_lo = mp.diff(lambda u: G(a_c, r_c, u, th_lo, m=1), t_lo)
    assert abs(d_lo) < 20 * th_lo, ("dG/dtau must be O(th) at the lower end", k, d_lo)
    limit = -mp.fsum(mp.mpf(ak) / (t_lo - mp.mpf(ak)) ** 2 for ak in a_c)
    err = abs(d_lo / th_lo - limit)
    assert err < mp.mpf(10) ** (-k + 2), (k, d_lo / th_lo, limit, err)
    if prev_err is not None:
        assert err < prev_err, (k, err, prev_err)
    prev_err = err
    assert abs(limit) > 1, (k, limit)    # nonzero after rescaling, so that end is reachable


for a, r, l in CASES:
    assert l == len(a) - 1, (a, l)
    end = mp.pi / r
    for k in [1, 2, 3, 5]:
        th = end - mp.mpf(10) ** (-k)
        t = tau(a, r, l, th)
        c, s_ = mp.cos(th) / mp.sin(th), mp.sin(th)
        assert all(c - ak / (t * s_) < 0 for ak in a), (a, r, k)
        assert mcount(a, t, th) == 0, (a, r, k)
        assert abs(G(a, r, t, th)) < mp.mpf(10) ** -25, (a, r, k, G(a, r, t, th))

    # the two partials at the endpoint, and the slope the IFT reads off them
    S = mp.fsum(1 / mp.mpf(ak) for ak in a)
    dG_dtau = mp.diff(lambda u: G(a, r, u, end, m=0), 0)
    dG_dth = mp.diff(lambda v: G(a, r, 0, v, m=0), end)
    assert abs(dG_dtau + mp.sin(end) * S) < mp.mpf(10) ** -25, (a, r, dG_dtau)
    assert abs(dG_dth + r) < mp.mpf(10) ** -25, (a, r, dG_dth)
    assert abs(dG_dtau) > mp.mpf("0.1"), (a, r)          # invertible, so the IFT applies
    assert abs(-dG_dth / dG_dtau - predicted_slope(a, r)) < mp.mpf(10) ** -25, (a, r)

# ---- where the two ends part: the lower endpoint's denominators --------------------------
# simple smallest zero -- `tau(0+)` is no `a_k`, nothing collides, `G` is analytic there too
a_simple, r_s, l_s = (1, 2, 4), 2, 2
gaps = []
for k in [2, 3, 4, 6]:
    th = mp.mpf(10) ** (-k)
    t = tau(a_simple, r_s, l_s, th)
    gaps.append(min(abs(t * mp.cos(th) - mp.mpf(ak)) for ak in a_simple))
assert all(g > mp.mpf("0.25") for g in gaps), gaps
assert all(abs(t - mp.mpf(ak)) > mp.mpf("0.25") for ak in a_simple
           for t in [tau(a_simple, r_s, l_s, mp.mpf(10) ** -6)]), "tau(0+) is not a zero"

# repeated smallest zero -- `tau(0+) = x_1` IS a zero, and the gap dies like `th^2`
a_rep, r_r, l_r = (1, 1, 3, 3), 2, 3
for k in [2, 3, 4, 6]:
    th = mp.mpf(10) ** (-k)
    t = tau(a_rep, r_r, l_r, th)
    gap = min(abs(t * mp.cos(th) - mp.mpf(ak)) for ak in a_rep)
    assert abs(gap / th**2 - mp.mpf("1.5")) < mp.mpf(10) ** (-k + 1), (k, gap / th**2)
    # so the branch arrives with zero slope, and it is the SECOND derivative that carries
    assert abs((t - 1) / th**2 + 1) < mp.mpf(10) ** (-k + 1), (k, (t - 1) / th**2)

# the exact value at the headline case
a, r, l = (1, 2, 4), 2, 2
assert abs(predicted_slope(a, r) + mp.mpf(8) / 7) < mp.mpf(10) ** -35

# and `r = 1` is where the formula breaks: the arc ends at `pi` and the denominator dies
assert abs(mp.sin(mp.pi / 1)) < mp.mpf(10) ** -35

print("check_upper_endpoint_branch_slope: OK")
