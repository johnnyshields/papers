r"""Paper section `sec:dominance` (`thm:weighted-dominance`), and `thm:FT-geometry`.

`DominanceFT.interior_data_of_geometry` asks for ONE separating radius across the whole
compact interior:

    hpair :  for every theta in [e, b-e], every zero of D with |t| <= R0 is one of the
             principal pair,        together with        hTR : tau(theta) < R0.

That is a FIXED-CIRCLE contour hypothesis, and it is **strictly stronger** than what
`thm:FT-geometry` states.  The theorem gives a uniform modulus **ratio** on a compact
subinterval -- every non-principal zero has `|w| >= (1+c) tau(theta)`, pointwise in theta.
A ratio does not produce a fixed radius: what `hpair` needs is

    sup_{[e,b-e]} tau   <   inf_{[e,b-e]} (min non-principal modulus),

and the pointwise ratio only gives `third(theta) > tau(theta)` at each theta separately.
Since `tau` is strictly decreasing along the Forgacs--Tran branch, `sup tau = tau(e)` sits at
the LOWER end of the interval while `inf third` can sit anywhere, so the two quantities are
compared across different angles and nothing pointwise settles it.

This script measures the comparison.  For each pencil it sweeps the real spectral parameter,
reads the roots of `D(t,z) = Q(t) + z t^r` directly (never solving for the branch -- the
conditioning trap recorded in `check_ft_geometry_general_r.py`), identifies the
minimum-modulus conjugate pair as `tau e^{+-i theta}`, and records the next modulus up.  It
then reports, per interior parameter `e`,

    FIXED     = inf third / sup tau        (must exceed 1 for a single R0 to exist)
    RATIO     = min over theta of third/tau  (what `thm:FT-geometry` gives)

so the two are visible side by side and the gap between them is the thing at issue.

mpmath `polyroots` at 60 digits throughout, with the pair identified by conjugacy rather than
by argument: `numpy.roots` has misreported this tree's root sets before, and a repeated
smallest zero conditions the cluster like `eps^{1/rho}`.
"""

from mpmath import mp, mpf, mpc, polyroots, fabs, arg, pi, conj

mp.dps = 60

# `Q = c * prod (a_k - t)` with the zeros positive, and r >= 1.
PENCILS = [
    ("simple spread 1,2,4",      [1, 2, 4],        1),
    ("simple spread 1,2,20",     [1, 2, 20],       1),
    ("simple spread 1,1.05,3",   [1, "1.05", 3],   1),
    ("double smallest 1,1,3",    [1, 1, 3],        1),
    ("triple smallest 1,1,1",    [1, 1, 1],        1),
    ("triple + far 1,1,1,7",     [1, 1, 1, 7],     1),
    ("wide 1,10,100",            [1, 10, 100],     1),
    ("four simple 1,2,3,4",      [1, 2, 3, 4],     1),
]

E_GRID = [mpf(1) / 2, mpf(1) / 4, mpf(1) / 10, mpf(1) / 20]


def den_coeffs(a, r, z):
    """Coefficients of D(t,z) = prod_k (a_k - t) + z t^r, highest degree first."""
    poly = [mpf(1)]                       # prod (a_k - t), built as coefficients of t
    for ak in a:
        # multiply by (ak - t)
        new = [mpf(0)] * (len(poly) + 1)
        for i, c in enumerate(poly):
            new[i] += mpf(ak) * c
            new[i + 1] -= c
        poly = new
    poly = poly[:]                        # poly[i] is the coefficient of t^i
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
        return None                        # minimal root is real: off the branch
    if fabs(w1 - conj(w0)) > mpf(10) ** -20 * max(mpf(1), fabs(w0)):
        return None                        # the two smallest are not a conjugate pair
    tau = fabs(w0)
    theta = fabs(arg(w0))
    return tau, theta, fabs(roots[2])


def sweep(a, r, n):
    """A logarithmic sweep of the spectral parameter.

    The branch occupies a bounded window of `z` whose location moves by decades between
    pencils -- `1,2,4` lives near `z ~ 1`, `1,10,100` near `z ~ 100`.  A linear grid wide
    enough for the second is far too coarse for the first, which is how an earlier version
    of this script reported "no branch samples" on a pencil whose branch it had simply
    stepped over.
    """
    out = []
    for i in range(n + 1):
        u = mpf(-8) + mpf(16) * mpf(i) / n
        z = mpf(10) ** u
        got = pair_and_third(a, r, z)
        if got is not None:
            out.append(got)
    return out


def report(name, a, r):
    # sweep z over a range wide enough to cover the arc; the branch's theta is monotone in z
    data = sweep(a, r, 3000)
    if not data:
        return None
    rows = []
    for e in E_GRID:
        band = [(t, th, thr) for (t, th, thr) in data if e <= th <= pi - e]
        if len(band) < 20:
            continue
        tmax = max(band, key=lambda row: row[0])
        tmin = min(band, key=lambda row: row[2])
        sup_tau, inf_third = tmax[0], tmin[2]
        fixed = inf_third / sup_tau
        ratio = min(thr / t for (t, _, thr) in band)
        rows.append((e, sup_tau, tmax[1], inf_third, tmin[1], fixed, ratio, len(band)))
    return rows


if __name__ == "__main__":
    print("FIXED = inf third / sup tau   (>1 iff one separating radius exists on [e, b-e])")
    print("RATIO = min theta of third/tau (what thm:FT-geometry gives, always >1)")
    print()
    failures = []
    for name, a, r in PENCILS:
        rows = report(name, a, r)
        if not rows:
            print(f"{name:26s}  no branch samples")
            continue
        print(f"{name:26s}  r = {r}")
        for e, sup_tau, th_tau, inf_third, th_third, fixed, ratio, cnt in rows:
            flag = "" if fixed > 1 else "   <-- NO FIXED RADIUS"
            print(f"    e = {mp.nstr(e, 4):>7s}"
                  f"  sup tau = {mp.nstr(sup_tau, 7):>11s} at th={mp.nstr(th_tau, 4):>7s}"
                  f"  inf third = {mp.nstr(inf_third, 7):>11s} at th={mp.nstr(th_third, 4):>7s}"
                  f"  FIXED = {mp.nstr(fixed, 6):>9s}"
                  f"  RATIO = {mp.nstr(ratio, 6):>9s}  ({cnt}){flag}")
            assert ratio > 1, f"pointwise ratio failed on {name} at e={e}: {ratio}"
            if fixed <= 1:
                failures.append((name, e, fixed, ratio))
        print()

    print("Every pencil satisfies the POINTWISE ratio of thm:FT-geometry.")
    if failures:
        print()
        print("The FIXED-radius form fails on:")
        for name, e, fixed, ratio in failures:
            print(f"  {name}, e = {mp.nstr(e, 4)}: FIXED = {mp.nstr(fixed, 6)} "
                  f"<= 1 while RATIO = {mp.nstr(ratio, 6)} > 1")
        print()
        print("So `interior_data_of_geometry`'s `hpair` is not implied by thm:FT-geometry,")
        print("and on these configurations it is not merely unproved -- it is FALSE.")
    else:
        print("The FIXED-radius form also holds on every pencil and every e swept.")

    print("\nALL PASS")
