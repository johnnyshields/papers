r"""Paper section `sec:dominance` (`thm:weighted-dominance`), `lem:amplitude-divisor`.

`interior_data_of_geometry` is met on a **subdivision** of the compact interior, one
separating radius per piece, so its amplitude floor has to be reassembled across pieces.
`InteriorSeparation.interior_data_of_pieces` does that with

    S = union of the pieces' divisors,   N = sum over S of nu_j,   L = max(hi - lo, 1),
    A' = (min over pieces of A_i) / L^N.

Two things in that formula can go wrong quietly, and this script is the guard on both.

  EXPONENT   `N` is the **total multiplicity** `sum_j nu_j`, not the number of divisor
             points `|S|`.  The two coincide exactly when every zero of `B` on the arc is
             simple, which is the case `lem:amplitude-divisor` does NOT exist for.

             The guard is on the **absorption step**, not on the constant it produces:
             the step asserts `prod_{S \ S_i} |theta - theta_j|^{nu_j} <= L^N`, and with
             the point count in the exponent that is FALSE as soon as an unowned divisor
             point is multiple.  Measured below at `3.77` against `L^{count} = 2.74`.  At the level of the final constant `|S|`
             happens to survive on this pencil, because the reassembled bound is
             pessimistic by about 50x and the slack swallows a factor of `L` -- which is
             exactly why a test of the outcome would be toothless and a test of the step
             is not.

  STRADDLE   The `L^N` factor pays for divisor points a piece does not own.  It is never
             exercised when the pieces are closed and share the divisor point on their
             boundary, so a test that splits exactly at the divisor tests nothing.  The
             adversarial split puts one divisor strictly inside each piece.

The pencil is the tree's own cubic branch, `Q = (1-t)^3`, `r = 1`, with `B` built to vanish
at two prescribed points of the arc so the split can separate them.  `B` is a product of the
real quadratics through `gamma(theta_j)` and its conjugate, so it has real coefficients and
`B(0) != 0`; squaring one factor gives that point multiplicity two, which is what makes the
exponent question bite rather than being a distinction without a difference.

The branch is used in closed form,
`tau = tan((theta-pi)/3) / (tan((theta-pi)/3) cos theta - sin theta)`, and is VERIFIED before
anything is built on it: `z = -Q(gamma)/gamma` is asserted real and `D(gamma, z)` asserted
zero, both to 25 digits.  A root-finder is not used, for the reason recorded in
`check_anchored_window_counts.py`.

mpmath at 50 digits: the floor is a ratio whose numerator and denominator both vanish at a
divisor point, and float64 cannot resolve the limit at multiplicity two.
"""

from mpmath import mp, mpf, mpc, exp, cos, sin, tan, pi, fabs, re, im, sqrt

mp.dps = 50

TOL = mpf(10) ** (-25)


def cubic_tau(theta):
    """The principal radius of `Q = (1-t)^3`, `r = 1`, in closed form."""
    u = tan((theta - pi) / 3)
    return u / (u * cos(theta) - sin(theta))


def gamma(theta):
    return cubic_tau(theta) * exp(mpc(0, 1) * theta)


def Qeval(t):
    return (1 - t) ** 3


def Qderiv(t):
    return -3 * (1 - t) ** 2


def zval(theta):
    """`z(theta) = -Q(gamma)/gamma`, real along the branch."""
    g = gamma(theta)
    return -Qeval(g) / g


def check_branch(thetas):
    """The closed form really is the branch: `z` real and `D(gamma, z) = 0`."""
    worst_im, worst_D = mpf(0), mpf(0)
    for th in thetas:
        g, z = gamma(th), zval(th)
        worst_im = max(worst_im, fabs(im(z)))
        worst_D = max(worst_D, fabs(Qeval(g) + z * g))
    assert worst_im < TOL, f"z not real along the branch: {worst_im}"
    assert worst_D < TOL, f"gamma not a denominator zero: {worst_D}"
    return worst_im, worst_D


def real_quadratic(g):
    """The real quadratic vanishing at `g` and its conjugate: t^2 - 2 Re(g) t + |g|^2."""
    a, b = 2 * re(g), fabs(g) ** 2
    return lambda t: t ** 2 - a * t + b


def make_B(points, mults):
    """`B` vanishing at `gamma(theta_j)` to order `nu_j`, real coefficients, `B(0) != 0`."""
    quads = [(real_quadratic(gamma(th)), m) for th, m in zip(points, mults)]
    def B(t):
        out = mpf(1)
        for q, m in quads:
            out *= q(t) ** m
        return out
    return B


def amp(theta, B):
    """`|W(theta)| = |B(gamma) / (Q'(gamma) - Q(gamma)/gamma)|` at `r = 1`."""
    g = gamma(theta)
    dD = Qderiv(g) + zval(theta)
    return fabs(B(g) / dD)


def divisor_product(theta, S, nu):
    out = mpf(1)
    for thj in S:
        out *= fabs(theta - thj) ** nu[thj]
    return out


def piece_constant(B, lo, hi, S, nu, n=4000):
    """`inf` over `[lo,hi]` of `Amp / prod_S |theta - theta_j|^{nu_j}`.

    At a divisor point both sides vanish to the same order, so the ratio has a finite
    positive limit; the grid simply avoids the point itself.
    """
    best = None
    for k in range(n + 1):
        th = lo + (hi - lo) * mpf(k) / n
        if any(fabs(th - thj) < mpf(10) ** -12 for thj in S):
            continue
        val = amp(th, B) / divisor_product(th, S, nu)
        best = val if best is None else min(best, val)
    return best


def leftover_worst(points, mults, pieces, L, n=2000):
    """Per piece, the absorption product against the two candidate exponents.

    The proof's chain is
    `prod_{S \\ S_i} |th - th_j|^{nu_j} <= prod_{S \\ S_i} L^{nu_j} = L^{sum nu_j}`.
    The point-count error replaces that exponent by `|S \\ S_i|`.  They come apart exactly
    on a piece whose UNOWNED divisor point is multiple, which is the configuration this
    returns per piece so the discriminating one is visible rather than averaged away.
    """
    nu = {th: m for th, m in zip(points, mults)}
    rows = []
    for (plo, phi) in pieces:
        owned = [th for th in points if plo <= th <= phi]
        rest = [th for th in points if th not in owned]
        worst = mpf(0)
        for k in range(n + 1):
            th = plo + (phi - plo) * mpf(k) / n
            prod = mpf(1)
            for thj in rest:
                prod *= fabs(th - thj) ** nu[thj]
            worst = max(worst, prod)
        nusum = sum(nu[thj] for thj in rest)
        rows.append({"lo": plo, "hi": phi, "worst": worst, "nusum": nusum,
                     "count": len(rest),
                     "ok": worst <= L ** nusum + TOL,
                     "wrong_ok": worst <= L ** len(rest) + TOL})
    return rows


def run(name, points, mults, split, e):
    lo, hi = e, pi - e
    thetas = [lo + (hi - lo) * mpf(k) / 200 for k in range(201)]
    check_branch(thetas)
    B = make_B(points, mults)
    nu = {th: m for th, m in zip(points, mults)}

    # the adversarial subdivision: one divisor strictly inside each piece
    pieces = [(lo, split), (split, hi)]
    for (plo, phi) in pieces:
        owned = [th for th in points if plo <= th <= phi]
        assert len(owned) == 1, (
            f"{name}: split at {split} does not separate the divisor: piece "
            f"[{mp.nstr(plo,4)},{mp.nstr(phi,4)}] owns {len(owned)}")

    A = [piece_constant(B, plo, phi, [th for th in points if plo <= th <= phi], nu)
         for (plo, phi) in pieces]

    S = list(points)
    N = sum(mults)                      # TOTAL multiplicity
    card = len(points)                  # the wrong exponent
    L = max(hi - lo, mpf(1))
    Amin = min(A)

    rows = leftover_worst(points, mults, pieces, L)
    Aprime = Amin / L ** N
    Atrue = piece_constant(B, lo, hi, S, nu)

    return {
        "name": name, "N": N, "card": card, "L": L, "Amin": Amin,
        "Aprime": Aprime, "Atrue": Atrue, "rows": rows,
        "step_ok": all(rw["ok"] for rw in rows),
        "step_wrong_ok": all(rw["wrong_ok"] for rw in rows),
        "ok": Aprime <= Atrue + TOL,
        "margin": Atrue / Aprime,
    }


if __name__ == "__main__":
    e = mpf(1) / 5
    simple = run("simple divisor, nu = (1,1)", [mpf(1), mpf(2)], [1, 1], mpf(3) / 2, e)
    double = run("double divisor, nu = (2,1)", [mpf(1), mpf(2)], [2, 1], mpf(3) / 2, e)

    print("Branch verified in closed form: z real and D(gamma,z) = 0 to 25 digits.\n")
    for row in (simple, double):
        print(f"{row['name']}")
        print(f"    N (total multiplicity) = {row['N']},   |S| (point count) = {row['card']}"
              f",   L = {mp.nstr(row['L'], 8)}")
        print(f"    ABSORPTION STEP, per piece:")
        for rw in row["rows"]:
            print(f"        piece [{mp.nstr(rw['lo'], 4):>6s},{mp.nstr(rw['hi'], 4):>6s}]"
                  f"  max prod = {mp.nstr(rw['worst'], 8):>12s}"
                  f"   vs L^(sum nu = {rw['nusum']}) = "
                  f"{mp.nstr(row['L'] ** rw['nusum'], 8):>12s} {'holds' if rw['ok'] else 'FAILS'}"
                  f"   vs L^(count = {rw['count']}) = "
                  f"{mp.nstr(row['L'] ** rw['count'], 8):>12s} "
                  f"{'holds' if rw['wrong_ok'] else 'FAILS -- exponent bites'}")
        print(f"    CONSTANT  min A_i = {mp.nstr(row['Amin'], 10)}"
              f",  A' = A_min/L^N = {mp.nstr(row['Aprime'], 10)}"
              f"   {'OK' if row['ok'] else 'FAILS'}")
        print(f"        true best combined A = {mp.nstr(row['Atrue'], 10)}"
              f"   (A' pessimistic by {mp.nstr(row['margin'], 6)}x)")
        print()
        assert row["step_ok"], f"{row['name']}: the L^N absorption step is violated"
        assert row["ok"], f"{row['name']}: the reassembled floor constant is too large"

    assert simple["N"] == simple["card"], "simple case: N and |S| should agree"
    assert simple["step_wrong_ok"], "simple case: |S| and N agree, so both must hold"
    assert double["N"] != double["card"], "double case: N and |S| should differ"
    assert not double["step_wrong_ok"], (
        "the point-count exponent survives the absorption step at multiplicity two -- this "
        "guard has gone toothless, most likely because the split stopped putting the "
        "MULTIPLE divisor point in the piece the other one is measured from")

    print("The straddle is real: each piece owns exactly one divisor point, so the")
    print("`L^N` factor is exercised in both directions rather than being vacuous.")
    print("The exponent is load-bearing at the step: on the piece whose UNOWNED divisor")
    print("point is double, the absorption product exceeds `L^count`, so the reassembly")
    print("would not close with the point count in place of the total multiplicity.")
    print("At the level of the FINAL CONSTANT the wrong exponent happens to survive here,")
    print("on about 50x of slack -- which is why this guard tests the step and not the")
    print("outcome.  A test of the outcome would pass on both and prove nothing.")
    print("\nALL PASS")
