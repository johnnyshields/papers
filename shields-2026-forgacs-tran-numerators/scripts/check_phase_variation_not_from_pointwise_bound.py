"""`cor:linear-phase-variation` cannot be reached from `eq:phase-derivative-bound`.

Paper section: `cor:linear-phase-variation`, `eq:linear-phase-variation`,
`eq:phase-derivative-bound`, `subsec:proof`, `prop:angular-discrepancy`.

`eq:phase-derivative-bound` gives one `kappa` with `|psi'| <= kappa` across the
retained range, uniformly in `M`.  It is tempting to read the variation clause off
it: `sum_i Var_{I_i} psi <= kappa * (pi/r)`, a bound with no `deg B` in it at all,
which would make `cor:linear-phase-variation` unnecessary.

It does not work, and the reason is measurable.  `kappa` exists only by compactness
and grows without bound as a zero of `B` approaches the arc, while the *variation*
contributed by that zero stays below the arc constant `K_gamma + pi` however close
it comes -- which is exactly what Radon's bound says and exactly what a pointwise
supremum cannot see.  So the two constants of `eq:linear-phase-variation` are free
of `B` and `kappa` is not, and the supply's variation clause has to arrive already
summed over the blocks rather than derived from the pointwise bound.

Objects are the paper's own: the principal branch `t_+(theta) = tau(theta)e^{i theta}`
of the pencil `D(t,z) = Q(t) + z t^r` at `Q = (1-t)^3`, `r = 1`, with `tau` and `z`
solved from the reality of `z` on the fiber, and `W = -B(t_+)/D'(t_+)`
(`eq:W-def` through `AttractorPole.eval_derivative_ftDen`).

mpmath only, no float64 in the loop.
"""

from mpmath import mp, mpf, mpc, exp, pi, sin, quad, diff, polyroots, fabs, im, re

mp.dps = 40

R = 1  # r
ARC_HI = pi / R

# Q = (1 - t)^3, by coefficient, so the branch equation below is derived from Q
# rather than transcribed for it.
QC = [mpf(1), mpf(-3), mpf(3), mpf(-1)]


def Q(t):
    return sum(QC[j] * t**j for j in range(len(QC)))


def dQ(t):
    return sum(j * QC[j] * t ** (j - 1) for j in range(1, len(QC)))


def branch_roots(theta):
    """The positive real roots of `eq:principal-pair`'s branch equation.

    `z = -Q(t)/t^r` is real at `t = tau e^{i theta}` iff
    `Im(-Q(tau e^{i theta}) e^{-i r theta}) = 0`, which for real `Q = sum q_j t^j` is

        sum_j q_j sin((j - r) theta) tau^j = 0,

    a real polynomial in `tau`.  Solved exactly.

    **Not `findroot`.**  The equation has more than one positive root over part of
    the arc -- two below `pi/2` here -- and a shooting method started from a fixed
    guess silently returns whichever it converges to, which is a *different branch*
    of the pencil and at some parameters not even positive.  Nothing about the
    output looks wrong: it is a genuine root, the phase identities built on it
    still hold, and only a property of the *branch* -- that `z` is strictly
    monotone, `thm:FT-geometry` -- catches it.  That is what `check_branch` below
    asserts before anything else runs.
    """
    coeffs = [QC[j] * sin((j - R) * theta) for j in range(len(QC))]
    hi = list(reversed(coeffs))
    while len(hi) > 1 and hi[0] == 0:
        hi = hi[1:]
    if len(hi) <= 1:
        return []
    rts = polyroots(hi, maxsteps=300, extraprec=300)
    return sorted(re(w) for w in rts if fabs(im(w)) < mpf("1e-25") and re(w) > 0)


def tau_of(theta):
    """`tau(theta)` on the principal branch: the smallest positive root.

    The larger root carries `z < 0` and runs off to infinity at `theta = pi/2`;
    the smallest falls monotonically from `t_a = 1` to `1/2` with `z` rising from
    `0` to `27/4`, which is `eq:ab-def` at this pencil.

    The selection is not an inference from that: the formalization pins it.
    `CubicWitness.cubicBranchFn` is `2 cos(theta) tau^3 - 3 tau^2 + 1`, which is
    the branch equation above at this pencil, and `cubicTau_spec` puts its root in
    `Ioc 0 1` -- so the excluded root is exactly the one above `1`, which is what a
    shooting method started at `tau = 1` lands on over part of the arc.
    """
    rts = branch_roots(theta)
    assert rts, f"no positive branch root at theta = {mp.nstr(theta, 8)}"
    return rts[0]


def arc(theta):
    return tau_of(theta) * exp(1j * theta)


def z_of(theta):
    t = arc(theta)
    return re(-Q(t) / t**R)


def darc(theta):
    return diff(arc, theta)


def dD_at_branch(theta):
    """D'(t) = Q'(t) + z r t^{r-1} at t = t_+(theta)."""
    t = arc(theta)
    return dQ(t) + z_of(theta) * R * t ** (R - 1)


def W(theta, roots):
    """`eq:W-def` -- the residue amplitude at the principal branch."""
    t = arc(theta)
    num = mpc(1)
    for b in roots:
        num *= t - b
    return -num / dD_at_branch(theta)


def V(theta, roots):
    """`eq:W-on-g`'s fixed factor: everything of W that does not see a zero of B."""
    return -1 / dD_at_branch(theta)


def dlog_V_im(theta):
    return im(diff(lambda s: V(s, []), theta) / V(theta, []))


def dlog_W_im(theta, roots):
    """Im(W'/W) -- the phase derivative `eq:phase-derivative-bound` bounds."""
    return im(diff(lambda s: W(s, roots), theta) / W(theta, roots))


def root_phase_deriv_im(theta, b):
    """Im(gamma'/(gamma - b)) -- the derivative of one root's argument branch."""
    return im(darc(theta) / (arc(theta) - b))


LO = mpf("0.05")
HI = ARC_HI - mpf("0.05")


def variation_of_root(b, peak, lo=LO, hi=HI):
    """Total variation of `polarAngle gamma dgamma b` over the arc.

    Split at `peak`: the integrand is a spike of width `dist(b, arc)` sitting at
    the root's own parameter, and a quadrature that does not know where it is
    misses it entirely once that width falls under the node spacing.
    """
    return quad(lambda s: fabs(root_phase_deriv_im(s, b)), [lo, peak, hi])


def sup_root_phase_deriv(b, peak, width, lo=LO, hi=HI, n=400, m=400):
    """Supremum of the branch derivative, sampled coarsely and then at the spike.

    A uniform grid over the whole arc reports a *falling* supremum once the spike
    is narrower than the node spacing, which reads exactly like the quantity
    having stopped growing.  The refinement around `peak` at scale `width` is
    what makes the sample measure the supremum rather than the grid.
    """
    step = (hi - lo) / n
    best = max(fabs(root_phase_deriv_im(lo + k * step, b)) for k in range(n + 1))
    fine = width / 10
    for k in range(-m, m + 1):
        s = peak + k * fine
        if lo <= s <= hi:
            best = max(best, fabs(root_phase_deriv_im(s, b)))
    return best


def report(name, value):
    print(f"  {name:<46} {mp.nstr(value, 12)}")


def check_branch(n=400):
    """`thm:FT-geometry` on the model itself, before it is used for anything.

    `z` is strictly increasing along the principal branch and `tau` is continuous.
    A root-selection slip breaks both, and breaks nothing else that is checked
    downstream -- every phase identity is built from whatever `arc` returns, so it
    holds just as well on the wrong branch.
    """
    lo, hi = LO, HI
    step = (hi - lo) / n
    prev_t = prev_z = None
    maxjump = mpf(0)
    dirs = set()
    for j in range(n + 1):
        th = lo + j * step
        t = tau_of(th)
        zz = z_of(th)
        assert 0 < t <= 1, (
            f"tau must lie in Ioc 0 1 along the principal branch "
            f"(CubicWitness.cubicTau_spec); got {mp.nstr(t, 10)} at theta = "
            f"{mp.nstr(th, 8)}"
        )
        if prev_t is not None:
            maxjump = max(maxjump, fabs(t - prev_t))
            dirs.add(1 if zz > prev_z else -1)
        prev_t, prev_z = t, zz
    assert 0 < prev_t <= 1, (
        f"tau must lie in Ioc 0 1 along the principal branch "
        f"(CubicWitness.cubicTau_spec); got {mp.nstr(prev_t, 10)}"
    )
    assert dirs == {1}, (
        "z must be strictly increasing along the principal branch "
        f"(thm:FT-geometry); observed directions {dirs} -- the root selection is "
        "picking more than one branch"
    )
    assert maxjump < 20 * step, (
        f"tau jumps by {mp.nstr(maxjump, 8)} between neighboring parameters at "
        f"step {mp.nstr(step, 6)}: the branch is not continuous, so the root "
        "selection is picking more than one branch"
    )
    return maxjump


def main():
    print(__doc__.splitlines()[0])
    print()
    jump = check_branch()
    print("Branch guard (thm:FT-geometry, before anything else):")
    report("z strictly increasing along the branch", mpf(1))
    report("max |tau step| over 400 nodes", jump)
    print()

    # ---- (1) the arc constant K_gamma: variation of the tangent angle ------
    K_gamma = quad(lambda s: fabs(im(diff(darc, s) / darc(s))), [LO, HI])
    print("Arc constants (the pencil's own, free of B):")
    report("K_gamma = Var(tangent angle)", K_gamma)
    kappa1 = K_gamma + pi
    report("kappa_1 = K_gamma + pi", kappa1)
    # the denominator factor's own branch, B absent
    kappa0 = quad(lambda s: fabs(dlog_W_im(s, [])), [LO, HI])
    report("kappa_0 = Var(denominator factor branch)", kappa0)
    assert K_gamma > 0, "the tangent angle must genuinely turn"
    assert kappa0 > 0, "the denominator factor must genuinely contribute"
    print()

    # ---- (2) a zero approaching the arc: sup blows up, variation does not --
    theta0 = mpf("1.0")
    base = arc(theta0)
    outward = base / abs(base)  # move off the arc radially
    print("One zero of B approaching the arc at theta = 1.0:")
    hdr = "sup |psi_b'|"
    print(f"  {'delta':<14}{hdr:<26}{'sup * delta':<26}Var psi_b")
    sups, prods, varis = [], [], []
    for k in range(1, 5):
        delta = mpf(10) ** (-k)
        b = base + delta * outward
        s = sup_root_phase_deriv(b, theta0, delta)
        v = variation_of_root(b, theta0)
        sups.append(s)
        prods.append(s * delta)
        varis.append(v)
        print(
            f"  {mp.nstr(delta, 6):<14}{mp.nstr(s, 12):<26}"
            f"{mp.nstr(s * delta, 12):<26}{mp.nstr(v, 12)}"
        )

    # the supremum is genuinely 1/delta, not merely large: sup*delta is flat
    for k in range(1, len(sups)):
        assert sups[k] > 5 * sups[k - 1], (
            "sup |psi'| must grow at least geometrically as delta shrinks; "
            f"got {mp.nstr(sups[k-1], 8)} -> {mp.nstr(sups[k], 8)}"
        )
    ratio = max(prods) / min(prods)
    assert ratio < mpf("1.5"), (
        "sup |psi'| must be asymptotically C/delta -- sup*delta should be flat; "
        f"spread was {mp.nstr(ratio, 8)}"
    )
    # ... while every one of those variations stays under the arc constant
    for v in varis:
        assert v <= kappa1, (
            "Radon's bound must hold however close the zero comes: "
            f"Var = {mp.nstr(v, 10)} exceeded K_gamma + pi = {mp.nstr(kappa1, 10)}"
        )
    assert min(varis) > kappa1 / 100, (
        "the variations must stay a real quantity rather than collapsing to 0, "
        "or the bound above would be vacuous"
    )
    print()
    report("max Var over the four depths", max(varis))
    report("kappa_1 = K_gamma + pi", kappa1)
    print()

    # ---- (2b) the split identity the two branch terms are identified by ----
    # Im(W'/W) = Im(V'/V) + sum_b Im(gamma'/(gamma - b)).  The supply's other
    # clauses are about a branch built on W; the variation bound is about the
    # fixed factor's angle plus one viewing angle per zero of B.  Each side is
    # well formed alone, so this is the identity that says they are one object.
    print("The branch split, at the paper's own objects:")
    print(f"  {'theta':<12}{'Im(W-prime/W)':<26}{'split sum':<26}residual")
    worst = mpf(0)
    for j in range(1, 7):
        th = LO + (HI - LO) * mpf(j) / 7
        roots = []
        for i in range(3):
            p = arc(LO + (HI - LO) * mpf(i + 1) / 4)
            roots.append(p + mpf("0.05") * p / abs(p))
        lhs = dlog_W_im(th, roots)
        rhs = dlog_V_im(th) + sum(root_phase_deriv_im(th, b) for b in roots)
        res = fabs(lhs - rhs) / max(fabs(lhs), mpf(1))
        worst = max(worst, res)
        print(
            f"  {mp.nstr(th, 6):<12}{mp.nstr(lhs, 12):<26}"
            f"{mp.nstr(rhs, 12):<26}{mp.nstr(res, 6)}"
        )
    assert worst < mpf("1e-12"), (
        "Im(W'/W) must split along eq:W-on-g -- the two branch terms are one "
        f"object; worst relative residual was {mp.nstr(worst, 8)}"
    )
    # the identity must not hold for a reason that would make it empty: dropping
    # one root has to break it
    lhs = dlog_W_im(mpf("1.3"), roots)
    short = dlog_V_im(mpf("1.3")) + sum(
        root_phase_deriv_im(mpf("1.3"), b) for b in roots[:-1]
    )
    assert fabs(lhs - short) / fabs(lhs) > mpf("1e-3"), (
        "dropping a zero of B must break the split, or the check would pass on "
        "a term that contributes nothing"
    )
    print()

    # ---- (2c) is Radon's bound's own S-finiteness meetable here? ----------
    # viewing_angle_bound_components_off_arc carries a Finset S containing every
    # parameter where the tangent angle less the viewing angle is an integer
    # multiple of pi.  Nothing in the tree produces one, so the first question is
    # whether one EXISTS: it does iff those parameters are isolated.  The
    # difference lies in pi*Z exactly where dgamma/(gamma - b) is real, i.e. where
    # the viewing angle's own derivative Im(gamma'/(gamma - b)) vanishes -- which
    # is also where hasDerivAt_viewingAngle_of_polar's sin(theta - phi) vanishes,
    # so the two readings agree.  If that derivative were identically zero on any
    # subinterval, S would have to contain a whole interval and could not be a
    # Finset: the hypothesis would be unmeetable, and nothing in a build would
    # say so.
    #
    # Counting near-zero grid nodes cannot decide this at any affordable
    # resolution -- the count bottoms out at one node and the "measure" is then
    # the node spacing, not a property of the function.  Locating each zero and
    # checking it is crossed TRANSVERSALLY does, and needs no resolution at all
    # beyond finding the crossings.
    def deriv_samples(b, lo, hi, n=600):
        step = (hi - lo) / n
        return step, [root_phase_deriv_im(lo + j * step, b) for j in range(n + 1)]

    def bisect_zero(b, x0, x1, steps=40):
        f0 = root_phase_deriv_im(x0, b)
        for _ in range(steps):
            xm = (x0 + x1) / 2
            fm = root_phase_deriv_im(xm, b)
            if f0 * fm <= 0:
                x1 = xm
            else:
                x0, f0 = xm, fm
        return (x0 + x1) / 2

    print("S-finiteness: are the viewing-angle derivative's zeros isolated?")
    print(f"  {'zero of B':<26}{'crossings':<12}{'min |g| away':<18}"
          f"{'least transversality':<22}verdict")
    base1 = arc(mpf("1.0"))
    outward1 = base1 / abs(base1)
    on_arc_m = mpf("1.6")
    cases = [
        ("just off the arc, delta 0.05", base1 + mpf("0.05") * outward1, LO, HI),
        ("far off the arc, delta 1", base1 + mpf("1.0") * outward1, LO, HI),
        ("on the arc, left side", arc(on_arc_m), LO, on_arc_m - mpf("0.1")),
        ("on the arc, right side", arc(on_arc_m), on_arc_m + mpf("0.1"), HI),
    ]
    h = mpf("1e-3")
    for name, b, lo, hi in cases:
        step, vals = deriv_samples(b, lo, hi)
        idx = [j for j in range(len(vals) - 1) if vals[j] * vals[j + 1] < 0]
        zeros = [bisect_zero(b, lo + j * step, lo + (j + 1) * step) for j in idx]
        # how far the function stays from zero away from the located crossings
        away = min(
            fabs(v)
            for j, v in enumerate(vals)
            if all(fabs(lo + j * step - zc) > 2 * h for zc in zeros)
        ) if zeros else min(fabs(v) for v in vals)
        # and how decisively it leaves each crossing
        trans = min(
            (min(fabs(root_phase_deriv_im(zc - h, b)),
                 fabs(root_phase_deriv_im(zc + h, b))) for zc in zeros),
            default=None,
        )
        ok = away > mpf("1e-6") and (trans is None or trans > mpf("1e-6"))
        print(
            f"  {name:<26}{len(zeros):<12}{mp.nstr(away, 8):<18}"
            f"{('--' if trans is None else mp.nstr(trans, 8)):<22}"
            f"{'isolated' if ok else 'FLAT STRETCH'}"
        )
        assert ok, (
            f"the viewing-angle derivative is not bounded away from zero off its "
            f"crossings for {name} (min |g| = {mp.nstr(away, 8)}, least "
            f"transversality {trans}), so it may vanish on a subinterval; then "
            f"Radon's bound's S could not be a Finset and hstate would be "
            f"unmeetable"
        )
        # and few enough that viewing_angle_bound's strip partition is small
        assert len(zeros) <= 4, (
            f"the crossing set for {name} needs more than a small strip "
            f"partition: {len(zeros)} crossings"
        )
    # the test must be able to FAIL, on the same code path: an identically zero
    # derivative has no transversal crossing and is not bounded away from zero
    saved = globals()["root_phase_deriv_im"]
    try:
        globals()["root_phase_deriv_im"] = lambda theta, b: mpf(0)
        _, flat_vals = deriv_samples(base1, LO, HI, n=50)
        flat_away = min(fabs(v) for v in flat_vals)
    finally:
        globals()["root_phase_deriv_im"] = saved
    assert not (flat_away > mpf("1e-6")), (
        "the test must reject a derivative that is identically zero, or it is "
        "not a test"
    )
    print(f"  {'(flat control)':<26}{0:<12}{mp.nstr(flat_away, 8):<18}"
          f"{'--':<22}FLAT STRETCH, as it must")
    print()

    # ---- (3) eq:linear-phase-variation at growing deg B --------------------
    print("Total variation of arg W against deg B, all zeros near the arc:")
    print(f"  {'deg B':<8}{'Var(arg W)':<26}{'kappa_0 + kappa_1 deg B':<26}headroom")
    prev = None
    for kdeg in range(1, 7):
        roots = []
        for j in range(kdeg):
            th = LO + (HI - LO) * mpf(j + 1) / (kdeg + 1)
            p = arc(th)
            roots.append(p + mpf("0.01") * p / abs(p))
        var = quad(lambda s: fabs(dlog_W_im(s, roots)), [LO, HI])
        cap = kappa0 + kappa1 * kdeg
        print(
            f"  {kdeg:<8}{mp.nstr(var, 12):<26}{mp.nstr(cap, 12):<26}"
            f"{mp.nstr(cap - var, 10)}"
        )
        assert var <= cap, (
            f"eq:linear-phase-variation failed at deg B = {kdeg}: "
            f"Var = {mp.nstr(var, 10)} > {mp.nstr(cap, 10)}"
        )
        # the variation must genuinely grow with deg B, or the linear bound
        # would be a bound on a constant and would say nothing
        if prev is not None:
            assert var > prev, (
                "Var(arg W) must increase with deg B; "
                f"{mp.nstr(prev, 8)} -> {mp.nstr(var, 8)}"
            )
        prev = var
    print()

    # ---- (4) the per-block cap is quadratic ------------------------------
    print("Summed vs per-block, at J = deg B blocks:")
    print(f"  {'deg B':<8}{'summed cap':<26}{'per-block cap (J+1)x':<26}ratio")
    ratios = []
    for kdeg in range(1, 9):
        summed = kappa0 + kappa1 * kdeg
        perblock = (kdeg + 1) * summed
        ratios.append(perblock / summed)
        print(
            f"  {kdeg:<8}{mp.nstr(summed, 12):<26}{mp.nstr(perblock, 12):<26}"
            f"{mp.nstr(perblock / summed, 8)}"
        )
    assert ratios[-1] > 8, (
        "the per-block cap must be quadratic in deg B, so the ratio to the "
        "summed cap must grow linearly and without bound"
    )
    print()
    print("ALL PASS")


if __name__ == "__main__":
    main()
