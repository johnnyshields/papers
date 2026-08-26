#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `thm:FT-geometry`, `eq:W-endpoint-form`;
and `lem:amplitude-divisor`, `eq:phase-derivative-bound`.

Can the endpoint collar bound's remaining hypothesis actually be MET, and with
what constant?

`ForgacsTran.exists_endpoint_phase_deriv_bound_of_deriv2` proves
`eq:phase-derivative-bound` on the collar from three facts, of which only one
carries a constant:

    ||gamma''(theta)|| <= L   for theta in (0, b].

Trading the endpoint Lipschitz binder for that is worth nothing if `L` does not
exist -- a hypothesis nobody can supply reads as progress and is not, and it is
the failure mode a Lean build cannot see, because a stronger hypothesis only
makes a theorem harder to APPLY and never harder to STATE.

`check_endpoint_branch_lipschitz.py` settles the harder half already: `gamma''`
has a finite LIMIT at the endpoint, asserted against closed forms at five
pencils (`gamma''(0) = beta - 1` at the `rho = 2` family, `-2/9 - 2i/sqrt(3)` at
`rho = 3`).  What that leaves open is the SUP over the whole collar rather than
the behaviour at one end of it, and the sup is what `L` is.  A finite limit at
`0` and continuity on the interior do not by themselves bound a function on
`(0, b]` -- they do once the interval is compact and the function extends, which
is the reading, but the reading is worth checking against the arithmetic before
a Lean binder is written around it.

**The curvature is computed from the EXACT first derivative, differenced once.**
`gamma'` comes off the branch equation -- `dt/dz = -t^r / D_t(t,z)` and
`dtheta/dz = Im((dt/dz)/t)`, so `gamma' = (dt/dz)/(dtheta/dz)` with no
differencing at all.  Only the second order is differenced.  Differencing
`gamma` twice instead would put the whole error budget on a root-finder's last
digits, and at `theta ~ 1e-4` that is the difference between a measurement and
a plot of the rounding.

Asserted, each as a failing test:

  (K1) `gamma''` is BOUNDED on the collar at all three pencils, and `L` is
       decided AT the endpoint: `||gamma''||` rises monotonically as
       `theta -> 0+` and its supremum is the endpoint limit, approached and not
       attained.  So `L` is not an unknown to be estimated -- it is
       `|gamma''(0)|`, which is already in closed form, and the sup is asserted
       against those closed forms rather than against itself:
       `|-2/9 - 2i/sqrt(3)|` at `rho = 3`, and `|beta - 1|` at `rho = 2`
       (`beta = R'(1)/R(1)`, so `1` at `R = 1` and `2` at `R = 1 - t/2`).
       Validating against a formula the sweep did not fit is the point: a sup
       checked only against the samples that produced it checks nothing.
  (K2) `gamma''` does not BLOW UP as `theta -> 0+`: the ratio of the largest
       `||gamma''||` over the inner decade to that over the outer decade stays
       O(1).  Teeth: a `theta^{-1/2}` curvature profile fails the same test on
       the same samples.
  (K3) the measured `L` feeds the Lean theorem's own constants to finite,
       nonempty values at every pencil -- `b' = min(b, ||gamma'(0)||/(L+1)) > 0`
       and `kappa = 3L/||gamma'(0)|| < inf`.  This is the output of
       `exists_endpoint_phase_deriv_bound_of_deriv2` instantiated at the pencils
       the paper is about, rather than at the module's own witness.
  (K4) the collar bound is not vacuous at those constants: `|Im(u'/u)|` computed
       directly along the branch stays under `kappa`, with the margin printed so
       a bound that is true only by being enormous is visible as such.

  (K5) THE LIMIT IN CLOSED FORM, which is what the compactness form of the
       collar lemma would need.  Two Taylor terms give it with no Puiseux
       anywhere: `gamma = g'(0)t + g''(0)t^2/2 + ...` divided by `t` is
       `u = g'(0) + g''(0)t/2 + ...`, so `u(0) = g'(0)` and `u'(0) = g''(0)/2`,
       whence

           lim Im(u'/u) = Im( gamma''(0) / (2 gamma'(0)) ).

       Checked against the DIRECT measurement at seven pencils spanning
       `rho = 2,3,4`, agreeing from 2e-36 to 4e-4, and reproducing the clean
       values an independent lane measured off a bisection of the angle-sum
       equation -- a different branch computation entirely -- at every pencil
       the two share: `1/3` at `(1,1,1)`, `3/4` at `(1,1,3)`, `7/10` at
       `(2,2,7)`, `1/4` at `(1,1,1,1)`, `11/10` at `(1,1,2,6)`.

       Two readings follow, and the second is the one to keep.

       At `rho = 2` the limit collapses to `|gamma''(0)| / (2 t_a)`, because
       there `gamma'(0)/t_a = i` and `gamma''(0)` is real, so the quotient is
       purely imaginary.  Asserted, and asserted to FAIL at `rho = 3` and
       `rho = 4` (0.588 against 1/3, 1.112 against 1/4), so the collapse is
       recorded as the special case it is rather than as the general formula.

       And the limit is NOT determined by `gamma'(0)`: it needs `gamma''(0)`
       too.  That is what the weaker lemma's docstring asserts, and three
       `rho = 2` pencils sharing `gamma'(0)/t_a = i` exactly reach 1.0, 0.75
       and 0.7 here -- differing precisely because `beta` differs.

  (K6) THE SLACK IN THE PROVED BOUND, priced rather than left unknown.  Lean's
       `kappa = 3L/||gamma'(0)||` against the true limit, at `rho = 2`, is
       exactly `6x`: `L = |gamma''(0)|` and `||gamma'(0)|| = t_a`, so
       `kappa = 3|gamma''(0)|/t_a` over a limit of `|gamma''(0)|/(2 t_a)`.
       The consumer wants `kappa < M+1`, a THRESHOLD on `M`, so a factor of six
       costs a threshold shift and nothing else -- which is why the bound route
       is taken and the compactness route is not built.

SCOPE: three pencils at `r = 1` for (K1)-(K4), seven for (K5); both collision
orders.  Not a proof for all `(Q,r)`.  What is shown is that `L` exists at the
pencils measured, that the constants built from it are usable numbers, and that
the limit the stronger lemma would need is elementary rather than Puiseux.
"""

from mpmath import mp, mpf, mpc, polyroots, fabs, arg, sqrt, im

mp.dps = 60

COLLAR = mpf('0.30')          # b, in radians of angular distance from the endpoint


def _pval(c, t):
    v = mpc(0)
    for a in c:
        v = v * t + a
    return v


def _pder(c):
    d = len(c) - 1
    return [c[i] * (d - i) for i in range(d)]


def branch_roots(qcoeffs, r, z):
    """Roots of `Q(t) + z t^r`, sorted by modulus.  `qcoeffs` highest first."""
    d = len(qcoeffs) - 1
    c = list(qcoeffs)
    c[d - r] = c[d - r] + z
    return sorted(polyroots(c, maxsteps=300, extraprec=300), key=lambda t: fabs(t))


def sample(qcoeffs, r, z):
    """The upper member of the minimum-modulus conjugate pair, validated."""
    roots = branch_roots(qcoeffs, r, z)
    t0, t1 = roots[0], roots[1]
    assert fabs(t0 - t1.conjugate()) < mpf('1e-30'), (
        "the two smallest roots are not a conjugate pair at z=%s: %s, %s"
        % (z, t0, t1))
    if len(roots) > 2:
        assert fabs(t0) <= fabs(roots[2]), (
            "the retained pair is not minimal in modulus at z=%s" % z)
    return t0 if t0.imag > 0 else t1


def gamma_prime_exact(qcoeffs, r, z):
    """`(theta, gamma'(theta))` off the branch equation -- nothing differenced."""
    t = sample(qcoeffs, r, z)
    Dt = _pval(_pder(qcoeffs), t) + z * r * t ** (r - 1)
    dtdz = -(t ** r) / Dt
    dthdz = (dtdz / t).imag
    assert dthdz != 0, "dtheta/dz vanished at z=%s -- theta is not a chart there" % z
    return arg(t), dtdz / dthdz


def gamma_second(qcoeffs, r, z, rel=mpf('1e-12')):
    """`(theta, gamma(theta), gamma''(theta))`, the second order differenced once."""
    h = z * rel
    th_p, gp_p = gamma_prime_exact(qcoeffs, r, z + h)
    th_m, gp_m = gamma_prime_exact(qcoeffs, r, z - h)
    dth = th_p - th_m
    assert dth != 0
    th, gp = gamma_prime_exact(qcoeffs, r, z)
    return th, sample(qcoeffs, r, z), gp, (gp_p - gp_m) / dth


def normalized_Q(roots):
    """`Q(t) = prod (1 - t/a_j)`, highest-degree coefficient first, `Q(0) = 1`.

    The paper's own normalization.  Building `Q` monic instead flips the leading
    sign at odd degree, and `branch_roots` then sweeps `z > 0` the wrong way and
    never produces a conjugate pair -- which reads as "this pencil has no branch"
    rather than as a sign error.
    """
    c = [mpf(1)]
    for a in roots:
        nxt = [mpf(0)] * (len(c) + 1)
        for i, ci in enumerate(c):
            nxt[i] += ci
            nxt[i + 1] -= ci / a
        c = nxt
    return list(reversed(c))


def collar_sweep(qcoeffs, r, n=90):
    """Samples with `theta` inside `(0, COLLAR]`, coarsest first."""
    out = []
    for i in range(n):
        z = mpf(10) ** (mpf(-1) - mpf(9) * i / (n - 1))     # 1e-1 down to 1e-10
        th, t, gp, g2 = gamma_second(qcoeffs, r, z)
        if 0 < th <= COLLAR:
            out.append((th, t, gp, g2))
    out.sort(key=lambda row: -row[0])
    return out


def main():
    print("check_endpoint_curvature_collar.py")
    print("Paper: `sec:geometry`, `eq:W-endpoint-form`, `eq:phase-derivative-bound`")
    print()

    # the last entry is `gamma''(0)` in closed form: `-2/9 - 2i/sqrt(3)` at
    # `rho = 3`, and `beta - 1` at `rho = 2` with `beta = R'(1)/R(1)`.
    cases = [
        ("A  Q=(1-t)^3, r=1        [rho=3, k=3]",
         [mpf(-1), mpf(3), mpf(-3), mpf(1)], 1, mpf(1),
         mpc(-mpf(2) / 9, -2 / sqrt(mpf(3)))),
        ("B  Q=(1-t)^2, r=1        [rho=2, k=2, unit circle, beta=0]",
         [mpf(1), mpf(-2), mpf(1)], 1, mpf(1), mpc(-1, 0)),
        ("C  Q=(1-t)^2(1-t/2), r=1 [rho=2, k=2, asymmetric, beta=-1]",
         [mpf(-1) / 2, mpf(2), mpf(-5) / 2, mpf(1)], 1, mpf(1), mpc(-2, 0)),
    ]

    results = []
    print("  (K1) `gamma''` is bounded on the collar (0, %s], and L is the"
          % mp.nstr(COLLAR, 3))
    print("       endpoint limit, checked against its closed form:")
    for name, q, r, t_a, g2_exact in cases:
        rows = collar_sweep(q, r)
        assert len(rows) >= 20, \
            "%s: only %d samples landed inside the collar" % (name, len(rows))
        norms = [fabs(g2) for (_, _, _, g2) in rows]
        L = max(norms)
        assert L < mpf(100), "%s: gamma'' is not bounded on the collar: %s" % (name, L)
        # the profile rises toward the endpoint, so the sup is the endpoint limit
        assert norms[-1] >= norms[0], \
            "%s: ||gamma''|| does not rise toward the endpoint: %s -> %s" \
            % (name, norms[0], norms[-1])
        assert fabs(L - norms[-1]) < mpf('1e-6') * L, \
            "%s: the sup %s is not the endpoint-end value %s, so the profile is " \
            "not monotone as read" % (name, L, norms[-1])
        # and it agrees with the closed form the sweep did not fit
        assert fabs(rows[-1][3] - g2_exact) < mpf('1e-3'), \
            "%s: measured gamma''(0+) = %s but the closed form is %s" \
            % (name, rows[-1][3], g2_exact)
        results.append((name, q, r, rows, L, t_a))
        print("       %-40s  L = sup||gamma''|| = %s" % (name, mp.nstr(L, 8)))
        print("       %-40s  gamma''(0+) measured %s, closed form %s"
              % ("", mp.nstr(rows[-1][3], 7), mp.nstr(g2_exact, 7)))
    print("       L is decided AT the endpoint at every pencil, so it is not a")
    print("       quantity to be estimated -- it is |gamma''(0)|, in closed form.")
    print()

    print("  (K2) `gamma''` does not blow up as theta -> 0+:")
    for name, q, r, rows, L, t_a in results:
        inner = [fabs(g2) for (th, _, _, g2) in rows if th <= mpf('1e-3')]
        outer = [fabs(g2) for (th, _, _, g2) in rows if th > mpf('1e-2')]
        assert inner and outer, "%s: the decades did not both populate" % name
        ratio = max(inner) / max(outer)
        assert ratio < mpf(5), \
            "%s: ||gamma''|| blows up toward the endpoint, ratio %s" % (name, ratio)
        print("       %-40s  inner/outer decade ratio = %s"
              % (name, mp.nstr(ratio, 6)))
    # teeth: an unbounded curvature profile fails the same test on the same thetas
    ths = [th for (th, _, _, _) in results[0][3]]
    bad_inner = max(1 / sqrt(th) for th in ths if th <= mpf('1e-3'))
    bad_outer = max(1 / sqrt(th) for th in ths if th > mpf('1e-2'))
    assert bad_inner / bad_outer > mpf(5), \
        "the theta^{-1/2} control did not fail the test, so a passing reading " \
        "above would not distinguish bounded from merely small"
    print("       teeth: a theta^{-1/2} curvature profile gives ratio %s on the"
          % mp.nstr(bad_inner / bad_outer, 6))
    print("       same thetas -- it FAILS, so the readings above are not an")
    print("       artifact of where the samples landed.")
    print()

    print("  (K3) the Lean theorem's constants, at these pencils:")
    constants = []
    for name, q, r, rows, L, t_a in results:
        g0 = fabs(rows[-1][2])                      # ||gamma'(0+)||
        assert g0 > 0, "%s: gamma'(0) vanished, h0 unmeetable" % name
        bprime = min(COLLAR, g0 / (L + 1))
        kappa = 3 * L / g0
        assert bprime > 0, "%s: the collar b' came out empty" % name
        assert kappa < mpf('1e6'), "%s: kappa is not a usable number: %s" % (name, kappa)
        constants.append((name, rows, bprime, kappa, t_a))
        print("       %-40s  L = %s, ||gamma'(0)|| = %s"
              % (name, mp.nstr(L, 6), mp.nstr(g0, 6)))
        print("       %-40s  b' = %s, kappa = 3L/||gamma'(0)|| = %s"
              % ("", mp.nstr(bprime, 6), mp.nstr(kappa, 6)))
    print()

    print("  (K4) the bound is not vacuous -- |Im(u'/u)| against kappa:")
    for name, rows, bprime, kappa, t_a in constants:
        worst = mpf(0)
        n = 0
        for (th, t, gp, g2) in rows:
            if th > bprime:
                continue
            g = t - t_a                          # gamma - t_a, the shifted branch
            u = g / th
            up = (gp * th - g) / th ** 2
            if u == 0:
                continue
            worst = max(worst, fabs(im(up / u)))
            n += 1
        assert n >= 10, "%s: only %d samples inside b'" % (name, n)
        assert worst <= kappa, \
            "%s: |Im(u'/u)| = %s exceeds kappa = %s" % (name, worst, kappa)
        print("       %-40s  sup|Im(u'/u)| = %s <= kappa = %s  (margin %sx)"
              % (name, mp.nstr(worst, 6), mp.nstr(kappa, 6),
                 mp.nstr(kappa / worst, 4) if worst > 0 else "inf"))
    print()

    print("  (K5) the limit in closed form, `Im(gamma\'\'(0)/(2 gamma\'(0)))`:")
    limit_cases = [
        ("(1,1)      rho=2", [mpf(1), mpf(1)], None, True),
        ("(1,1,1)    rho=3", [mpf(1)] * 3, mpf(1) / 3, False),
        ("(1,1,2)    rho=2", [mpf(1), mpf(1), mpf(2)], None, True),
        ("(1,1,3)    rho=2", [mpf(1), mpf(1), mpf(3)], mpf(3) / 4, True),
        ("(2,2,7)    rho=2", [mpf(2), mpf(2), mpf(7)], mpf(7) / 10, True),
        ("(1,1,1,1)  rho=4", [mpf(1)] * 4, mpf(1) / 4, False),
        ("(1,1,2,6)  rho=2", [mpf(1), mpf(1), mpf(2), mpf(6)], mpf(11) / 10, True),
    ]
    shared_i = []
    for name, roots, reported, is_rho2 in limit_cases:
        rows = collar_sweep(normalized_Q(roots), 1)
        assert rows, "%s: no samples inside the collar" % name
        th, t, gp, g2 = rows[-1]
        t_a = min(roots)
        gg = t - t_a
        direct = fabs(im(((gp * th - gg) / th ** 2) / (gg / th)))
        closed = fabs(im(g2 / (2 * gp)))
        assert fabs(direct - closed) < mpf('1e-3'), \
            "%s: the closed form %s misses the direct limit %s" % (name, closed, direct)
        if reported is not None:
            assert fabs(direct - reported) < mpf('1e-3'), \
                "%s: measured %s against the independently reported %s" \
                % (name, direct, reported)
        # the rho=2 collapse, and its failure off rho=2
        collapse = fabs(g2) / (2 * t_a)
        if is_rho2:
            assert fabs(collapse - direct) < mpf('1e-3'), \
                "%s: the rho=2 collapse |g\'\'(0)|/(2 t_a) = %s misses %s" \
                % (name, collapse, direct)
            shared_i.append((name, direct, gp / t_a, th, gp, g2))
        else:
            assert fabs(collapse - direct) > mpf('1e-2'), \
                "%s: the rho=2 collapse held off rho=2, so it is not the special " \
                "case it is recorded as" % name
        print("       %-18s direct %-12s closed %-12s reported %s"
              % (name, mp.nstr(direct, 8), mp.nstr(closed, 8),
                 mp.nstr(reported, 6) if reported is not None else "-"))
    # `gamma'(0)/t_a = i` at the rho=2 pencils, yet the limits differ.
    #
    # The tolerance is DERIVED, not guessed, and it is not the tolerance an
    # extrapolating branch computation would use.  This samples at the smallest
    # `theta` reached rather than at the endpoint, so the real part is not a few
    # times 1e-18 -- it is the first-order term, measured at exactly `-theta`,
    # and the imaginary part sits `O(theta^2)` off `1`.  A 1e-12 threshold here
    # rejects a correct reading; a threshold loose enough to pass every pencil
    # would decide nothing.  Both are scaled to the `theta` actually reached.
    slopes = []
    for name, _, ratio, th, _, _ in shared_i:
        # `Re` vanishes to FIRST order and `Im - 1` to SECOND; the coefficient of
        # each is pencil-dependent, so what is asserted is the ORDER of vanishing
        # with the coefficient bounded, and the coefficients are printed rather
        # than buried in a threshold.  Measured here: `Re/theta` from 1.0 to 2.2.
        re_coeff = fabs(ratio.real) / th
        im_coeff = fabs(ratio.imag - 1) / th ** 2
        assert re_coeff < 10, \
            "%s: Re(gamma\'(0)/t_a)/theta = %s does not look like a vanishing " \
            "first-order term, so gamma\'(0) is not purely imaginary here" \
            % (name, re_coeff)
        assert im_coeff < 10, \
            "%s: (Im(gamma\'(0)/t_a) - 1)/theta^2 = %s does not look like a " \
            "vanishing second-order term" % (name, im_coeff)
        slopes.append((name, re_coeff, im_coeff))
    print("       gamma\'(theta)/t_a -> i, Re vanishing to first order and")
    print("       Im-1 to second, with coefficients:")
    for name, rc, ic in slopes:
        print("       %-18s Re/theta = %-10s (Im-1)/theta^2 = %s"
              % (name, mp.nstr(rc, 4), mp.nstr(ic, 4)))
    spread = max(v for _, v, _, _, _, _ in shared_i) - min(v for _, v, _, _, _, _ in shared_i)
    assert spread > mpf('0.1'), \
        "the rho=2 pencils sharing gamma\'(0)/t_a = i did not separate, so this " \
        "decides nothing about whether gamma\'(0) determines the limit"
    print("       %d rho=2 pencils share gamma\'(0)/t_a = i to the sampled order"
          % len(shared_i))
    print("       spread over %s in the limit, so gamma\'(0) does not determine"
          % mp.nstr(spread, 4))
    print("       it -- gamma\'\'(0) is needed, which is the whole reason the")
    print("       bound-only lemma exists.")
    print()

    print("  (K6) the slack in the proved bound, at rho=2:")
    for name, direct, _, th, gp, g2 in shared_i:
        kappa = 3 * fabs(g2) / fabs(gp)
        assert fabs(kappa / direct - 6) < mpf('1e-2'), \
            "%s: the slack is %s, not the 6x the algebra predicts" % (name, kappa / direct)
        print("       %-18s kappa = %-10s limit = %-10s slack %sx"
              % (name, mp.nstr(kappa, 6), mp.nstr(direct, 6), mp.nstr(kappa / direct, 4)))
    print("       Exactly 6x, and the consumer wants kappa < M+1 -- a THRESHOLD")
    print("       on M -- so a factor of six costs a threshold shift and nothing")
    print("       else.  That is why the bound route is taken.")
    print()

    print("  SCOPE: three pencils at r=1 for (K1)-(K4), seven for (K5); both")
    print("  collision orders.  Not a proof for all (Q,r).  What is shown is that")
    print("  the one hypothesis")
    print("  `exists_endpoint_phase_deriv_bound_of_deriv2` still owes a constant")
    print("  for -- `||gamma''|| <= L` on the punctured collar -- is MEETABLE,")
    print("  and that the constants it builds are usable numbers rather than")
    print("  formally finite ones.")
    print()
    print("ALL PASS")


if __name__ == "__main__":
    main()
