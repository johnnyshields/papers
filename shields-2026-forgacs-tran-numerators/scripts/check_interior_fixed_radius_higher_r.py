r"""Paper section `sec:dominance` (`thm:weighted-dominance`), and `thm:FT-geometry`.

`check_interior_fixed_radius.py` measures whether ONE separating radius serves the whole
compact interior,

    FIXED = inf_{[e, b-e]} third / sup_{[e, b-e]} tau     (> 1 iff a single R0 exists)

against the pointwise ratio `thm:FT-geometry` actually gives.  Every pencil it sweeps has
`r = 1`, and on those the fixed form happens to hold.

`WeightedDominanceBranch.ft_weighted_dominance` lives at `2 <= r`, and carries that fixed
form as an antecedent.  So the `r = 1` measurement says nothing about whether that
antecedent is satisfiable where the theorem applies, and the two regimes are not alike:
the viewing arc is `(0, pi/r)`, and along it `tau -> 0` at the upper endpoint for every
`r`, while for `r >= 2` the whole `r`-cluster collapses with it.  `sup tau` sits at the
LOWER end of the interval and `inf third` at the UPPER end, so the comparison is between
a quantity of size `O(1)` and one that vanishes as `e -> 0`.

This script runs the same measurement at `2 <= r` with the smallest zero repeated
`rho >= 2` times, which is the hypothesis class of `ft_weighted_dominance`.  It reports
FIXED and RATIO per pencil and per interior parameter `e`, and asserts only what
`thm:FT-geometry` claims -- the POINTWISE ratio.  The fixed form is measured, not
asserted, because whether it holds is the question.

Root-finding follows `check_interior_fixed_radius.py`: mpmath `polyroots` at 60 digits,
the branch never solved for, and the principal pair identified by conjugacy rather than by
argument.
"""

from mpmath import mp, mpf, polyroots, fabs, arg, pi, conj

mp.dps = 60

# `(name, zeros a_k, r)` with `2 <= r` and the smallest zero repeated `rho >= 2` times,
# which is `ft_weighted_dominance`'s class.  `n_0 = rho - 2`, `n_1 = r - 2`.
#
# `deg D = max(n, r)`, so a pencil needs `max(n, r) >= 3` to HAVE a third modulus at all:
# `a = (1,1)` with `r = 2` has degree two, the principal pair is the whole root set, and the
# comparison this script measures is not defined there.  Such a pencil yields no samples
# rather than a wrong number -- the good failure -- but a silent skip would quietly shrink
# what "every pencil" ranges over, so `assert_no_silent_skips` below names any pencil that
# produced nothing and fails.  `r = 2` is carried deliberately and with `n > r`: it is the
# regime where a global radius has the best chance, so a sweep that reached only `r >= 3`
# would not have tested the side that could have passed.
PENCILS = [
    ("double 1,1,3      r=2", [1, 1, 3],    2),
    ("triple 1,1,1      r=2", [1, 1, 1],    2),
    ("quad   1,1,1,1    r=2", [1, 1, 1, 1], 2),
    ("double 1,1,5      r=2", [1, 1, 5],    2),
    ("triple 1,1,1      r=3", [1, 1, 1],    3),
    ("quad   1,1,1,1    r=3", [1, 1, 1, 1], 3),
    ("double 1,1,5      r=3", [1, 1, 5],    3),
    ("triple 1,1,1,7    r=4", [1, 1, 1, 7], 4),
]

E_FRACS = [mpf(1) / 4, mpf(1) / 8, mpf(1) / 20, mpf(1) / 50]


def den_coeffs(a, r, z):
    """Coefficients of D(t,z) = prod_k (a_k - t) + z t^r, highest degree first."""
    poly = [mpf(1)]
    for ak in a:
        new = [mpf(0)] * (len(poly) + 1)
        for i, c in enumerate(poly):
            new[i] += mpf(ak) * c
            new[i + 1] -= c
        poly = new
    while len(poly) <= r:
        poly.append(mpf(0))
    poly[r] += z
    return list(reversed(poly))


def pair_and_third(a, r, z):
    """(tau, theta, third) at spectral parameter z, or None if no nonreal minimal pair."""
    cs = den_coeffs(a, r, z)
    try:
        roots = polyroots(cs, maxsteps=800, extraprec=1200)
    except Exception:
        return None
    roots = sorted(roots, key=lambda w: fabs(w))
    if len(roots) < 3:
        return None
    w0, w1 = roots[0], roots[1]
    if fabs(w0.imag) < mpf(10) ** -20:
        return None
    if fabs(w1 - conj(w0)) > mpf(10) ** -20 * max(mpf(1), fabs(w0)):
        return None
    return fabs(w0), fabs(arg(w0)), fabs(roots[2])


def sweep(a, r, n):
    """Both signs of the spectral parameter, logarithmic in |z|."""
    out = []
    for sgn in (mpf(1), mpf(-1)):
        for i in range(n + 1):
            u = mpf(-8) + mpf(18) * mpf(i) / n
            got = pair_and_third(a, r, sgn * mpf(10) ** u)
            if got is not None:
                out.append(got)
    return out


def report(a, r):
    data = sweep(a, r, 2500)
    if not data:
        return None, None
    b = pi / r
    span = (min(th for (_, th, _) in data), max(th for (_, th, _) in data))
    rows = []
    for frac in E_FRACS:
        e = frac * b
        band = [(t, th, thr) for (t, th, thr) in data if e <= th <= b - e]
        if len(band) < 20:
            continue
        tmax = max(band, key=lambda row: row[0])
        tmin = min(band, key=lambda row: row[2])
        sup_tau, inf_third = tmax[0], tmin[2]
        rows.append((e, sup_tau, tmax[1], inf_third, tmin[1],
                     inf_third / sup_tau,
                     min(thr / t for (t, _, thr) in band), len(band)))
    return rows, span


if __name__ == "__main__":
    print("FIXED = inf third / sup tau    (>1 iff ONE separating radius serves [e, b-e])")
    print("RATIO = min over theta of third/tau  (what thm:FT-geometry gives; always >1)")
    print("b = pi/r, and e is taken as a FRACTION of b so the arcs are comparable.")
    print()
    covered, skipped, ROWS = [], [], []
    for name, a, r in PENCILS:
        assert max(len(a), r) >= 3, f"{name}: deg D = {max(len(a), r)}, no third modulus exists"
        rows, span = report(a, r)
        if not rows:
            print(f"{name:24s}  NO BRANCH SAMPLES")
            skipped.append(name)
            continue
        b = pi / r
        print(f"{name:24s}  b = pi/{r} = {mp.nstr(b, 6)}   "
              f"theta swept over [{mp.nstr(span[0], 4)}, {mp.nstr(span[1], 4)}]")
        for e, sup_tau, th_tau, inf_third, th_third, fixed, ratio, cnt in rows:
            flag = "" if fixed > 1 else "   <-- NO FIXED RADIUS"
            print(f"    e = {mp.nstr(e, 4):>9s}"
                  f"  sup tau = {mp.nstr(sup_tau, 7):>11s} at th={mp.nstr(th_tau, 4):>8s}"
                  f"  inf third = {mp.nstr(inf_third, 7):>11s} at th={mp.nstr(th_third, 4):>8s}"
                  f"  FIXED = {mp.nstr(fixed, 6):>9s}"
                  f"  RATIO = {mp.nstr(ratio, 6):>9s}  ({cnt}){flag}")
            assert ratio > 1, f"pointwise ratio failed on {name} at e={e}: {ratio}"
            covered.append((name, e, r))
            ROWS.append((r, name, e, fixed, ratio, th_tau, th_third, b))
        print()

    assert covered, "no pencil produced a measurable band"
    assert not skipped, (
        "these pencils produced no rows and would have been silently dropped from "
        f"the scope of 'every pencil': {skipped}")
    npencils = len({nm for nm, _, _ in covered})
    rvals = sorted({rr for _, _, rr in covered})
    print(f"Measured {npencils} pencils and {len(covered)} rows, at r = {rvals}.")
    print("Every row satisfies the POINTWISE ratio of thm:FT-geometry.")
    print()

    # The split, asserted rather than described.  `n_1 = r - 2` counts the NON-PRINCIPAL
    # members of the collapsing upper cluster.  At `r = 2` it is zero: the principal pair is
    # the whole collapsing set, nothing non-principal runs into the origin with `tau`, and
    # the third modulus stays O(1) -- so `sup tau` and `inf third` are attained at the SAME
    # angle and the fixed form reduces to the pointwise ratio.  From `r = 3` a non-principal
    # member collapses, `inf third -> 0` at the upper end while `sup tau` sits at the lower
    # one, and no single radius can separate them.
    two = [row for row in ROWS if row[0] == 2]
    three = [row for row in ROWS if row[0] >= 3]
    assert two and three, "the split needs rows on both sides of r = 3"
    for r, name, e, fixed, ratio, th_tau, th_third, b in two:
        assert fixed > 1, f"r = 2 should admit a fixed radius: {name}, e={e}, FIXED={fixed}"
    for r, name, e, fixed, ratio, th_tau, th_third, b in three:
        assert fixed < 1, f"r >= 3 should not: {name}, e={e}, FIXED={fixed}"
    print("SPLIT, at every pencil and every interior parameter measured:")
    print(f"  r = 2   ({len(two):2d} rows):  FIXED in "
          f"[{mp.nstr(min(x[3] for x in two), 6)}, {mp.nstr(max(x[3] for x in two), 6)}]"
          "   -- one separating radius EXISTS")
    print(f"  r >= 3  ({len(three):2d} rows):  FIXED in "
          f"[{mp.nstr(min(x[3] for x in three), 6)}, {mp.nstr(max(x[3] for x in three), 6)}]"
          "   -- it does NOT")
    print()
    # the mechanism, as the location of the two extrema rather than as prose
    gap2 = max(fabs(x[5] - x[6]) for x in two)
    farm = min((x[6] - x[2]) / (x[7] - 2 * x[2]) for x in three)
    print(f"At r = 2 the two extrema are CO-LOCATED: max |theta(sup tau) - theta(inf third)|"
          f" = {mp.nstr(gap2, 4)}, so FIXED and RATIO coincide and the fixed form asks")
    print("  nothing beyond thm:FT-geometry's pointwise statement.")
    print(f"At r >= 3 they sit at OPPOSITE ends: theta(inf third) is at least "
          f"{mp.nstr(farm * 100, 3)}% of the way")
    print("  across [e, b-e] while theta(sup tau) is at its lower endpoint.")
    print()
    print("So the fixed-circle interior block is satisfiable at r = 2 and FALSE from r = 3,")
    print("and the boundary is n_1 = r - 2, the theorem's own count of retained upper")
    print("cluster members -- not a matter of a pencil being well conditioned.  A finite")
    print("cover does not repair r >= 3: it yields one radius PER PIECE, while the block")
    print("quantifies ONE radius outside the interval.")

    print("\nALL PASS")
