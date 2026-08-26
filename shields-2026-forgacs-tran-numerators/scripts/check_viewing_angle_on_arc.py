r"""Paper section `sec:geometry` (`lem:viewing-angle`, `eq:viewing-angle-bound`).

Guards the two claims the on-arc case of `eq:viewing-angle-bound` rests on, both of which
are proved in `lean/ForgacsTran/ViewingAngle.lean` and neither of which the manuscript
states in the sharp form used there.

  SHARP FOLD   Var_[a,b] phi  <=  Var_[a,b] theta + F(a) - F(b),
               F(s) = acos(cos(theta(s) - phi(s))),

    the folded phase evaluated at the two endpoints rather than discarded against
    `0 <= F <= pi`.  This is what makes the two components of an arc through `beta`
    cost one `pi` between them rather than one each.

  ON ARC       with `beta` ON the arc at an interior parameter `m`, the summed variation
               over the components `[a,m)` and `(m,b]` is at most `K_gamma`, with NO `pi`.

Both are swept over four arcs, with the vantage point placed on the arc, off it, and at an
endpoint.  The folded phase is computed from the geometric identity

    cos(theta - phi) = Re(gamma' conj(gamma - beta)) / (|gamma'| |gamma - beta|),

which carries no branch in it -- that identity is itself the third thing checked, against a
directly lifted continuous argument.

Variations are computed by summing |increments| of a continuously lifted argument on a fine
parameter grid; that underestimates a true variation, so every assertion is made with a
tolerance that is a lower bound on the sampling error, and the tightness assertions are
one-sided in the safe direction.

mpmath at 40 digits throughout: the chord `gamma - beta` runs to zero at the meeting
parameter, and float64 loses the ratio's sign there.
"""

from mpmath import mp, mpf, mpc, cos, exp, acos, pi, fabs, re, conj, atan

mp.dps = 40

TOL = mpf(10) ** (-8)


def lift_arg(vals):
    """Continuous argument of a sampled nonvanishing path, by unwrapping."""
    out = []
    prev = None
    base = mpf(0)
    for z in vals:
        a = mp.atan2(z.imag, z.real)
        if prev is not None:
            while a + base - prev > pi:
                base -= 2 * pi
            while a + base - prev < -pi:
                base += 2 * pi
        prev = a + base
        out.append(prev)
    return out


def variation(vals):
    return sum(fabs(vals[i + 1] - vals[i]) for i in range(len(vals) - 1))


def sample(g, dg, a, b, n):
    ts = [a + (b - a) * mpf(i) / n for i in range(n + 1)]
    return ts, [g(t) for t in ts], [dg(t) for t in ts]


def folded(dgv, chord):
    """arccos of the normalized inner product of tangent with chord."""
    num = re(dgv * conj(chord))
    den = abs(dgv) * abs(chord)
    r = num / den
    if r > 1:
        r = mpf(1)
    if r < -1:
        r = mpf(-1)
    return acos(r)


ARCS = {
    # a straight line, the classical Radon witness
    "line": (lambda t: mpc(t, 1), lambda t: mpc(1, 0), mpf(-3), mpf(3)),
    # a parabola-like bend through the origin
    "bend": (lambda t: mpc(t, 5 * t ** 2), lambda t: mpc(1, 10 * t), mpf(-1), mpf(1)),
    # a circular arc
    "circle": (lambda t: exp(mpc(0, 1) * t), lambda t: mpc(0, 1) * exp(mpc(0, 1) * t),
               -pi + mpf(1) / 10, pi - mpf(1) / 10),
    # a spiral
    "spiral": (lambda t: t * exp(mpc(0, 1) * t),
               lambda t: exp(mpc(0, 1) * t) * (1 + mpc(0, 1) * t),
               mpf(1) / 100, 4 * pi),
}


def tangent_variation(g, dg, a, b, n):
    _, _, dgs = sample(g, dg, a, b, n)
    return variation(lift_arg(dgs))


# ---------------------------------------------------------------- identity

def check_cos_identity():
    """cos(theta - phi) equals the normalized tangent-chord inner product."""
    worst = mpf(0)
    for name, (g, dg, a, b) in ARCS.items():
        beta = mpc(mpf(1) / 3, -mpf(7) / 5)      # off every arc above
        ts, gs, dgs = sample(g, dg, a, b, 400)
        phi = lift_arg([z - beta for z in gs])
        th = lift_arg(dgs)
        for k in range(len(ts)):
            lhs = cos(th[k] - phi[k])
            rhs = re(dgs[k] * conj(gs[k] - beta)) / (abs(dgs[k]) * abs(gs[k] - beta))
            worst = max(worst, fabs(lhs - rhs))
    assert worst < TOL, f"cos identity off by {worst}"
    return worst


# ------------------------------------------------------------- sharp fold

def check_sharp_fold():
    """Var phi <= Var theta + F(a) - F(b), the drop form, on arcs missing beta."""
    margins = []
    for name, (g, dg, a, b) in ARCS.items():
        for beta in (mpc(mpf(1) / 3, -mpf(7) / 5), mpc(-2, 3), mpc(5, mpf(1) / 2)):
            ts, gs, dgs = sample(g, dg, a, b, 4000)
            if min(abs(z - beta) for z in gs) < mpf(1) / 100:
                continue
            phi = lift_arg([z - beta for z in gs])
            th = lift_arg(dgs)
            vphi, vth = variation(phi), variation(th)
            drop = folded(dgs[0], gs[0] - beta) - folded(dgs[-1], gs[-1] - beta)
            slack = vth + drop - vphi
            assert slack > -TOL, f"sharp fold violated on {name}, beta={beta}: {slack}"
            margins.append((name, str(beta), slack))
    return margins


# ---------------------------------------------------------------- on arc

def graded(lo, hi, toward_hi, n, depth=60):
    """A uniform grid on [lo, hi] refined geometrically toward one endpoint.

    The branch of `arg(gamma - beta)` turns fastest next to the meeting parameter, so a
    uniform grid alone undercounts its variation there -- and undercounting makes an upper
    bound look satisfied when it is not.  The geometric tail resolves it.
    """
    pts = set()
    for i in range(n + 1):
        pts.add(lo + (hi - lo) * mpf(i) / n)
    span = hi - lo
    for j in range(depth):
        d = span / mpf(2) ** (j + 1)
        pts.add(hi - d if toward_hi else lo + d)
    return sorted(pts)


def on_arc_sum(g, dg, a, b, m, n):
    """Summed variation of arg(gamma - beta) over [a,m) and (m,b], and K_gamma.

    The two components are exhausted from inside: the meeting parameter itself carries no
    branch, so each side is sampled up to a geometrically shrinking distance from it.
    """
    beta = g(m)
    total = mpf(0)
    if m > a:
        ts = graded(a, m, True, n)[:-1]
        total += variation(lift_arg([g(t) - beta for t in ts]))
    if m < b:
        ts = graded(m, b, False, n)[1:]
        total += variation(lift_arg([g(t) - beta for t in ts]))
    return total, tangent_variation(g, dg, a, b, n)


def check_on_arc():
    """With beta ON the arc the summed variation is below K_gamma -- no pi added."""
    rows = []
    for name, (g, dg, a, b) in ARCS.items():
        for frac in (mpf(0), mpf(1) / 4, mpf(1) / 2, mpf(4) / 5, mpf(1)):
            m = a + (b - a) * frac
            total, kg = on_arc_sum(g, dg, a, b, m, 4000)
            assert total <= kg + TOL, (
                f"on-arc sum exceeds K_gamma on {name} at frac={frac}: "
                f"{total} > {kg}")
            rows.append((name, str(frac), total, kg))
    return rows


def check_on_arc_tight():
    """K_gamma cannot be lowered.

    On `gamma(t) = t + i k t^2` through `beta = 0` both quantities are exact: each branch is
    monotone, so the sampled variation telescopes to the endpoint difference whatever the
    grid.  The summed viewing angle is `2 arctan k` and `K_gamma = 2 arctan 2k`, so the ratio
    climbs to one and no constant below `K_gamma` would serve.
    """
    ratios = []
    for k in (mpf(1), mpf(10), mpf(100), mpf(1000)):
        g = lambda t, k=k: mpc(t, k * t ** 2)
        dg = lambda t, k=k: mpc(1, 2 * k * t)
        total, kg = on_arc_sum(g, dg, mpf(-1), mpf(1), mpf(0), 4000)
        assert fabs(total - 2 * atan(k)) < mpf(1) / 10 ** 12, (
            f"sampled sum {total} disagrees with 2 arctan k at k={k}")
        assert fabs(kg - 2 * atan(2 * k)) < mpf(1) / 10 ** 12, (
            f"sampled K_gamma {kg} disagrees with 2 arctan 2k at k={k}")
        ratios.append((k, total / kg))
    assert all(r <= 1 + TOL for _, r in ratios), "ratio exceeded one"
    assert ratios[0][1] < ratios[-1][1], "ratio not climbing"
    exact = atan(mpf(10) ** 6) / atan(2 * mpf(10) ** 6)
    assert exact > 1 - mpf(10) ** (-6), f"exact ratio does not reach one: {exact}"
    ratios.append((mpf(10) ** 6, exact))
    return ratios


def check_off_arc_needs_pi():
    """Off the arc the pi is real: the line attains 2 arctan T -> pi with K_gamma = 0."""
    rows = []
    for T in (mpf(1), mpf(10), mpf(1000)):
        g = lambda t: mpc(t, 1)
        dg = lambda t: mpc(1, 0)
        ts, gs, dgs = sample(g, dg, -T, T, 20000)
        v = variation(lift_arg([z - mpc(0, 0) for z in gs]))
        kg = variation(lift_arg(dgs))
        assert kg < TOL, f"line tangent variation not zero: {kg}"
        assert v <= pi + TOL, f"line viewing angle exceeds pi: {v}"
        rows.append((T, v, 2 * atan(T)))
    assert rows[-1][1] > pi - mpf(1) / 100, "line does not approach pi"
    return rows


if __name__ == "__main__":
    w = check_cos_identity()
    print(f"cos(theta-phi) = Re(g' conj(g-beta))/(|g'||g-beta|): max error {mp.nstr(w, 6)}")

    print("\nSHARP FOLD  Var phi <= Var theta + F(a) - F(b)   (slack >= 0)")
    for name, beta, slack in check_sharp_fold():
        print(f"  {name:8s} beta={beta:28s} slack {mp.nstr(slack, 8)}")

    print("\nON ARC  summed variation over the two components vs K_gamma")
    for name, frac, total, kg in check_on_arc():
        print(f"  {name:8s} m at {frac:6s} of the arc: "
              f"sum {mp.nstr(total, 8)}  <=  K_gamma {mp.nstr(kg, 8)}")

    print("\nON ARC TIGHT  a sharpening bend through beta attains K_gamma")
    for k, r in check_on_arc_tight():
        print(f"  curvature {mp.nstr(k, 6):>10s}: sum/K_gamma = {mp.nstr(r, 10)}")

    print("\nOFF ARC  the pi is attained in the limit (line, K_gamma = 0)")
    for T, v, exact in check_off_arc_needs_pi():
        print(f"  T = {mp.nstr(T, 6):>8s}: variation {mp.nstr(v, 10)} "
              f"(exact 2 arctan T = {mp.nstr(exact, 10)})")

    print("\nALL PASS")
