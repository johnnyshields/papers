#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `thm:FT-geometry`, `eq:W-endpoint-form`;
and `lem:amplitude-divisor`, `eq:phase-derivative-bound`.

Is the branch derivative `gamma'` Lipschitz at the LOWER ENDPOINT?

The question is not idle geometry.  `eq:phase-derivative-bound` has to hold on
the retained range `[h/M, pi/r - h/M]` of `eq:retained-range`, which grows
toward the open arc as `M` increases, so a `kappa` obtained on a fixed
subinterval does not cover it.  Reaching the endpoint needs a bound on
`Im(W'/W)` there, and writing `gamma - t_a = theta * u(theta)`, the surviving
term is `-m * Im(u'/u)` with

    u'(theta) = (gamma'(theta) * theta - (gamma(theta) - t_a)) / theta^2.

If `gamma'` is Lipschitz at `0` then `gamma'(theta)*theta - (gamma - t_a)` is
`O(theta^2)` and `u'` is bounded, so the bound follows.  Whether `gamma'` IS
Lipschitz is what this script measures.

**The obvious pencil cannot answer it, which is the trap.**  At the witness
`Q = (1-t)^3, r = 1` the branch has the closed form
`tau = 1/(2 cos((pi-theta)/3))`, and `2 cos(pi/3) = 1` exactly -- the
denominator is bounded away from zero at the endpoint, so `tau` is ANALYTIC
through it and `gamma'` is Lipschitz for free.  Measuring there and concluding
the route is clear would be a wrong conclusion reached by a passing test.  The
general endpoint is a collision of `rho` zeros with a Puiseux structure, and
`rho <= 2` gives a different one (`k = 2`, `tau'(0+) = 0`) from the witness's
`rho = 3`.

So this measures at three pencils spanning both collision orders, and validates
the branch computation against a formula it did not fit.

**The branch is taken as the minimum-modulus root pair of `Q(t) + z t^r` swept
over real `z > 0`** -- polynomial root-finding, not a bracketed 1-D solve.  That
matters: `check_anchored_window_counts.py` records that an unbracketed solve at
the anchor silently converges to the wrong root and reported a discrepancy
growing from 2.7 to 12.2 that was entirely the solver.  Root-finding cannot fail
that way, and each sample is checked to be a genuine conjugate pair and genuinely
minimal in modulus.

Asserted, each as a failing test:

  (E1) The computation reproduces `tau'(0+) = -t_a * cot(pi/k)` of
       `lem:principal-endpoint-regularity` -- `k = 3` at the witness giving
       `-1/sqrt(3)`, and `k = 2` at both `rho = 2` pencils giving `0`.  A
       formula the sweep did not fit, so agreement is evidence the branch is
       the right one.
  (E2) `gamma'(theta)` converges as `theta -> 0+`, at all three.
  (E3) The Lipschitz quotient `|gamma'(theta) - gamma'(0+)| / theta` is BOUNDED
       and converges, at all three -- including the `rho = 2` asymmetric pencil,
       which is the case the witness cannot testify about.
       `gamma'(0+)` is taken as the FINEST ladder sample rather than
       extrapolated, so the quotient is understated at the fine end and the
       decline in the last two entries is that proxy, not convergence to zero.
       What is asserted is boundedness and absence of growth, which is what the
       argument needs; the limits are near `1.1`, `1.0` and `2.0`.
  (E6) One order further: does `gamma''` exist at the endpoint?  Bounded first
       differences are consistent with `C^{1,1}`; CONVERGING divided differences
       of `gamma'` are evidence for `C^2`, which is what analyticity in `theta`
       predicts.  For this `gamma'` is computed EXACTLY off the branch equation,
       `dt/dz = -t^r/(Q'(t) + z r t^{r-1})` and `gamma' = (dt/dz)/Im((dt/dz)/t)`,
       validated against a finite difference to `1e-19`; then `gamma''` is read
       from divided differences over the ladder, which needs no proxy for
       `gamma'(0+)` and so is free of the caveat above.  It converges at BOTH
       collision orders -- to `-2` exactly at the asymmetric `rho = 2` pencil,
       and to `-0.22215 - 1.15431i` at `rho = 3`, whose imaginary part is
       `-2/sqrt(3)`.  Teeth: a `theta^(3/2)` profile, `C^1` but not `C^2`, gives
       divided differences DIVERGING `36 -> 11396` on the same ladder.
       Both limits are pinned against EXACT values, by two independent routes:
       at `rho = 3` the closed form `tau = 1/(2 cos((pi-theta)/3))` gives
       `tau(0)=1, tau'(0)=-1/sqrt(3), tau''(0)=7/9` and
       `gamma''(0) = tau'' + 2i tau' - tau = -2/9 - 2i/sqrt(3)`; at `rho = 2`
       asymmetric a Puiseux expansion gives it directly -- with `t = 1+s` and
       `Q = s^2(1-s)/2`, the equation `s^2(1-s) + w^2(1+s) = 0` at `w^2 = 2z`
       has `s = iw - w^2 + O(w^3)`, and `theta = w + O(w^3)`, so
       `gamma = 1 + i theta - theta^2 + O(theta^3)` and `gamma''(0) = -2`
       exactly.  Neither value was fitted to the sweep.

       **`-2` is NOT a property of the quadratic collision alone.**  Carrying
       the cofactor, `Q = (1-t)^2 R(t)` with `beta = R'(1)/R(1)` gives
       `s^2(1 + beta s) + w^2(1 + s) = 0` at `w^2 = z/R(1)`, hence
       `s = i w + ((beta-1)/2) w^2` and

           gamma''(0) = beta - 1,

       so `-2` occurs exactly at `beta = -1`, which is `R = 1 - t/2`.  Asserted
       at four `rho = 2` pencils with four different cofactors -- `beta` of
       `-1`, `-1/2`, `-1/4`, `-1/9` giving `-2`, `-3/2`, `-5/4`, `-10/9` --
       each hit to `1e-4`.
       That is stronger evidence for `C^2` than a single clean number would be:
       the harness predicts a DIFFERENT value at each pencil from a closed form
       and lands on it every time.
  (E5) The method's own scope boundary, measured rather than assumed: at
       `rho = 1` there is NO conjugate pair as `z -> 0+` at all -- the two
       smallest roots stay real and distinct -- so the sweep does not reach
       that case and the `cot(pi/k)` formula is not being applied outside its
       guard.  This matches `eq:ab-def` (`a = 0` exactly when the smallest zero
       of `Q` is repeated) and matches the `2 <= rho` hypothesis carried by
       `EndpointBranch.tendsto_ftTau_blowup`, whose `s_0 = x_1 cot(pi/rho)` is
       the same constant (E1) validates against.  At `rho = 1` the lower
       endpoint sits at some `a > 0` where two REAL roots collide, which is a
       different computation and not this one.
  (E4) The check has teeth: the same quotient for a genuinely non-Lipschitz
       comparison function `theta^(1/2)` DIVERGES over the same ladder, so a
       bounded reading is not an artifact of the step sizes.

**Scope.**  Three pencils at `r = 1` is not a proof for all `(Q, r)`.  What the
data show is that the `rho = 2` case -- named as the one the witness cannot
reach -- behaves the same as `rho = 3`, and the reading that explains it is that
reparametrizing by `theta` absorbs the Puiseux exponent: at `k = 2` the
displacement is `s ~ i*sqrt(2z)` while `theta ~ sqrt(2z)`, so `s ~ i*theta`; at
`k = 3`, `s ~ z^(1/3)*omega` while `theta ~ Im(s)`, so again `s` is proportional
to `theta`.  The fractional power is in `z`, not in `theta`.  That is a reading
of the measurement, not a proof, and it is stated as one.

`mpmath` at 60 digits throughout.
"""

from mpmath import mp, mpf, mpc, polyroots, fabs, arg, sqrt, pi

mp.dps = 60


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
    assert fabs(t0 - t1.conjugate()) < mpf('1e-40'), (
        "the two smallest roots are not a conjugate pair at z=%s: %s, %s"
        % (z, t0, t1))
    if len(roots) > 2:
        assert fabs(t0) <= fabs(roots[2]), (
            "the retained pair is not minimal in modulus at z=%s" % z)
    return t0 if t0.imag > 0 else t1


def gamma_prime(qcoeffs, r, z):
    """`gamma'(theta)` at the sample, by a centered difference in `theta`."""
    h = z * mpf('1e-6')
    tp, tm = sample(qcoeffs, r, z + h), sample(qcoeffs, r, z - h)
    dth = arg(tp) - arg(tm)
    assert dth != 0
    return (tp - tm) / dth


def ladder(qcoeffs, r, kmin=3, kmax=9):
    out = []
    for k in range(kmin, kmax):
        z = mpf(10) ** (-k)
        t = sample(qcoeffs, r, z)
        out.append((arg(t), fabs(t), gamma_prime(qcoeffs, r, z)))
    return out


def run(name, qcoeffs, r, t_a, k_collision):
    rows = ladder(qcoeffs, r)
    # (E1) the endpoint slope, against a formula the sweep did not fit
    th, tau, _ = rows[-1]
    slope = (tau - mpf(1) * t_a) / th        # (tau(theta) - tau(0))/theta
    predicted = -t_a / mp.tan(pi / k_collision) if k_collision != 2 else mpf(0)
    assert fabs(slope - predicted) < mpf('1e-3'), (
        "%s: measured tau'(0+) = %s but lem:principal-endpoint-regularity "
        "predicts %s at k=%s" % (name, slope, predicted, k_collision))
    # (E2) gamma' converges
    gp_last, gp_prev = rows[-1][2], rows[-2][2]
    assert fabs(gp_last - gp_prev) < mpf('1e-2'), (
        "%s: gamma' has not settled: %s vs %s" % (name, gp_prev, gp_last))
    g0 = gp_last
    # (E3) the Lipschitz quotient is bounded and converging
    quots = [fabs(gp - g0) / th for (th, _, gp) in rows[:-1]]
    assert all(q < mpf(10) for q in quots), (
        "%s: Lipschitz quotient unbounded: %s" % (name, [mp.nstr(q, 5) for q in quots]))
    assert quots[-1] < quots[0] * 2, (
        "%s: Lipschitz quotient not settling: %s -> %s"
        % (name, mp.nstr(quots[0], 5), mp.nstr(quots[-1], 5)))
    return rows, slope, predicted, quots


def gamma_prime_exact(qcoeffs, r, z):
    """`gamma'` off the branch equation -- no finite differencing."""
    t = sample(qcoeffs, r, z)
    Dt = _pval(_pder(qcoeffs), t) + z * r * t ** (r - 1)
    dtdz = -(t ** r) / Dt
    dthdz = (dtdz / t).imag
    assert dthdz != 0
    return arg(t), dtdz / dthdz


def second_order(name, qcoeffs, r, exact=None, tol=mpf('1e-3')):
    """(E6) Divided differences of `gamma'` -- do they converge?"""
    z = mpf(10) ** (-5)
    th, gp = gamma_prime_exact(qcoeffs, r, z)
    h = z * mpf('1e-8')
    tp, tm = sample(qcoeffs, r, z + h), sample(qcoeffs, r, z - h)
    gp_fd = (tp - tm) / (arg(tp) - arg(tm))
    assert fabs(gp - gp_fd) < mpf('1e-10'), (
        "%s: exact gamma' disagrees with a finite difference: %s vs %s"
        % (name, gp, gp_fd))
    lad = [gamma_prime_exact(qcoeffs, r, mpf(10) ** (-k)) for k in range(3, 12)]
    dds = []
    for i in range(len(lad) - 1):
        (t1, g1), (t2, g2) = lad[i], lad[i + 1]
        dds.append((g1 - g2) / (t1 - t2))
    gaps = [fabs(dds[i] - dds[i + 1]) for i in range(len(dds) - 1)]
    assert gaps[-1] < gaps[0] / 10, (
        "%s: divided differences of gamma' are not converging: gaps %s"
        % (name, [mp.nstr(g, 4) for g in gaps]))
    if exact is not None:
        assert fabs(dds[-1] - exact) < tol, (
            "%s: gamma'' -> %s but the exact value is %s (gap %s)"
            % (name, dds[-1], exact, fabs(dds[-1] - exact)))
    return dds[-1], gaps[0], gaps[-1]


def scope_boundary_rho_one():
    """(E5) At `rho = 1` the smallest roots stay real -- no pair to sweep."""
    q = [mpf(1) / 2, mpf('-1.5'), mpf(1)]      # Q = (1-t)(1-t/2), simple at t=1
    z = mpf(10) ** (-3)
    roots = branch_roots(q, 1, z)
    t0, t1 = roots[0], roots[1]
    assert fabs(t0.imag) < mpf('1e-40') and fabs(t1.imag) < mpf('1e-40'), (
        "expected the two smallest roots to be REAL at rho=1, got %s, %s"
        % (t0, t1))
    assert fabs(t0 - t1) > mpf('0.5'), (
        "expected the two smallest roots to be well separated at rho=1")
    return t0.real, t1.real


def main():
    print("check_endpoint_branch_lipschitz.py -- `sec:geometry`, "
          "`eq:phase-derivative-bound`")
    print()

    cases = [
        ("A  Q=(1-t)^3, r=1   [rho=3, k=3 -- the witness, analytic endpoint]",
         [mpf(-1), mpf(3), mpf(-3), mpf(1)], 1, mpf(1), 3),
        ("B  Q=(1-t)^2, r=1   [rho=2, k=2 -- branch is exactly the unit circle]",
         [mpf(1), mpf(-2), mpf(1)], 1, mpf(1), 2),
        ("C  Q=(1-t)^2(1-t/2), r=1  [rho=2, k=2 -- asymmetric, tau not constant]",
         [mpf(-1) / 2, mpf(2), mpf(-5) / 2, mpf(1)], 1, mpf(1), 2),
    ]
    for (name, q, r, t_a, k) in cases:
        rows, slope, pred, quots = run(name, q, r, t_a, k)
        print("  %s" % name)
        print("     tau'(0+) measured %s, lem:principal-endpoint-regularity %s"
              % (mp.nstr(slope, 6), mp.nstr(pred, 6)))
        print("     gamma'(0+) = %s" % mp.nstr(rows[-1][2], 8))
        print("     Lipschitz quotient over the ladder: %s"
              % ", ".join(mp.nstr(q, 5) for q in quots))
        print()

    # (E4) teeth: a genuinely non-Lipschitz profile diverges on the same ladder
    bad = []
    for k in range(3, 9):
        th = mpf(10) ** (-k)
        bad.append(fabs(sqrt(th)) / th)
    assert bad[-1] > bad[0] * 100, (
        "the non-Lipschitz control did not diverge, so a bounded reading above "
        "would not distinguish Lipschitz from merely small: %s"
        % [mp.nstr(x, 4) for x in bad])
    print("  (E4) teeth: a theta^(1/2) profile gives quotients %s ... %s "
          "on the same ladder -- divergent, so the bounded readings above are "
          "not an artifact of the step sizes."
          % (mp.nstr(bad[0], 5), mp.nstr(bad[-1], 5)))
    exact3 = mpc(-mpf(2) / 9, -2 / sqrt(mpf(3)))     # tau''+2i tau'-tau, closed form
    # rho=2 with three cofactors: gamma''(0) = beta - 1, beta = R'(1)/R(1)
    for (nm, q, r, ex, tol) in [
            ("rho=3", [mpf(-1), mpf(3), mpf(-3), mpf(1)], 1, exact3, mpf('1e-3')),
            ("rho=2  R=1-t/2   beta=-1",
             [mpf(-1) / 2, mpf(2), mpf(-5) / 2, mpf(1)], 1, mpc(-2, 0), mpf('1e-4')),
            ("rho=2  R=1-t/3   beta=-1/2",
             [mpf(-1) / 3, mpf(5) / 3, mpf(-7) / 3, mpf(1)], 1,
             mpc(-mpf(3) / 2, 0), mpf('1e-4')),
            ("rho=2  R=1-t/5   beta=-1/4",
             [mpf(-1) / 5, mpf(7) / 5, mpf(-11) / 5, mpf(1)], 1,
             mpc(-mpf(5) / 4, 0), mpf('1e-4')),
            ("rho=2  R=1-t/10  beta=-1/9",
             [mpf(-1) / 10, mpf(12) / 10, mpf(-21) / 10, mpf(1)], 1,
             mpc(-mpf(10) / 9, 0), mpf('1e-4'))]:
        lim, g0, gN = second_order(nm, q, r, ex, tol)
        print("  (E6) %-26s gamma'' -> %s" % (nm, mp.nstr(lim, 10)))
        print("       exact %s, gap %s, successive gaps %s -> %s"
              % (mp.nstr(ex, 10), mp.nstr(fabs(lim - ex), 3),
                 mp.nstr(g0, 3), mp.nstr(gN, 3)))
    bad2 = []
    for k in range(3, 9):
        th, th2 = mpf(10) ** (-k), mpf(10) ** (-k - 1)
        bad2.append((mpf('1.5') * sqrt(th) - mpf('1.5') * sqrt(th2)) / (th - th2))
    assert bad2[-1] > bad2[0] * 100, "the C^1-but-not-C^2 control did not diverge"
    print("       teeth: theta^(3/2), C^1 but not C^2, diverges %s -> %s"
          % (mp.nstr(bad2[0], 5), mp.nstr(bad2[-1], 5)))
    print()

    r0, r1 = scope_boundary_rho_one()
    print("  (E5) scope boundary: at rho=1 the two smallest roots are REAL and "
          "distinct (%s, %s) at z=1e-3 -- no conjugate pair emerges as z->0+, "
          "so the sweep does not reach rho=1 and cot(pi/k) is never applied "
          "outside the `2 <= rho` guard that `tendsto_ftTau_blowup` carries."
          % (mp.nstr(r0, 8), mp.nstr(r1, 8)))
    print()
    print("  SCOPE: three pencils at r=1.  Not a proof for all (Q,r); what is")
    print("  shown is that the rho=2 case behaves as rho=3 does, and that the")
    print("  witness's analyticity is not what is carrying it.")
    print()
    print("ALL PASS")


if __name__ == "__main__":
    main()
