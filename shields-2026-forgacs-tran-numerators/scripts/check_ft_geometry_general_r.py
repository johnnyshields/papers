r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude).

Targets `thm:FT-geometry`, `eq:principal-pair` and `eq:ab-def` at general `r`, where the
formalization currently closes unconditionally only at `r = 1`.

The instrument here is deliberately different from every other branch script in this
directory, and the difference is the point.  Those solve for `\tau(\theta)` on a ray and are
therefore exposed to the conditioning of that solve -- `\Im g` vanishes identically on the ray
at `\theta = 0`, and a repeated smallest zero of `Q` makes the solve root-of-multiplicity
conditioned near the endpoint.  This script **never solves for the branch**.  It sweeps the
real spectral parameter `z` and reads the roots of the polynomial `D(t,z) = Q(t) + zt^r`
directly, then asks whether they have the structure `thm:FT-geometry` asserts:

  (G1) the minimum modulus is attained by a conjugate pair `\tau e^{\pm i\theta}` and by
       nothing else -- `eq:principal-pair`, and the minimum-modulus clause together;
  (G2) that pair is SIMPLE, which is `eq:principal-simple` (see
       `check_critical_points_real.py` for the proof that it cannot fail off the real axis);
  (G3) `\theta` lies in `(0, \pi/r)` and increases strictly with `z`, so `z \mapsto \theta` is
       a bijection onto the viewing arc -- the image statement of `eq:ab-def`;
  (G4) for `r > 1` the interval is a RAY, `I_{Q,r} = (a,\infty)`, so `\theta \to \pi/r` as
       `z \to \infty`, which is the endpoint behavior that separates `r > 1` from `r = 1`.

Because the roots come from `polyroots` rather than a rootfinder on a transcendental equation,
the only conditioning risk is a multiple root, and (G2) is checked at every sample rather than
assumed -- so a run where it degraded would fail loudly instead of drifting.
"""

from mpmath import mp, mpf, mpc, fabs, im, re, pi, polyroots, arg, sqrt

mp.dps = 60

TOL = mpf(10) ** (-30)


def q_coeffs_desc(xs):
    r"""`\prod_j (1 - t/x_j)` as a highest-degree-first coefficient list."""
    asc = [mpf(1)]
    for x in xs:
        nxt = [mpf(0)] * (len(asc) + 1)
        for i, c in enumerate(asc):
            nxt[i] += c
            nxt[i + 1] += -c / x
        asc = nxt
    return list(reversed(asc))


def den_coeffs(xs, r, z):
    r"""`D(t,z) = Q(t) + z t^r`, highest-degree-first."""
    q = q_coeffs_desc(xs)          # degree n
    n = len(q) - 1
    d = max(n, r)
    out = [mpf(0)] * (d + 1)
    for i, c in enumerate(q):      # q[i] is the coefficient of t^(n-i)
        out[d - (n - i)] += c
    out[d - r] += z
    return out


# (n, r, zeros) -- spanning r < n, r = n, r > n, repeated zeros, and wide spreads
PENCILS = [
    (2, [mpf(1), mpf(2)]),
    (2, [mpf(1), mpf(1), mpf(1)]),
    (2, [mpf(1), mpf(1), mpf(4)]),
    (3, [mpf(1), mpf(2), mpf(3)]),
    (3, [mpf(1), mpf(1), mpf(1), mpf(1)]),
    (4, [mpf(1), mpf(2)]),
    (4, [mpf(1), mpf(2), mpf(3), mpf(4), mpf(5)]),
    (5, [mpf('0.25'), mpf(1), mpf(9)]),
    (2, [mpf('0.01'), mpf(1), mpf(100)]),
    (6, [mpf(2), mpf(2), mpf(2), mpf(5)]),
]

total_samples = 0
worst_pair_gap = mpf('inf')
worst_simple = mpf('inf')

for r, xs in PENCILS:
    n = len(xs)
    thetas = []
    zs = []
    # sweep z over several decades on the positive ray; the viewing arc is where the
    # minimum-modulus root is a nonreal conjugate pair
    # The sweep must run far up the ray: `theta -> pi/r` only as `z -> infinity`, and the
    # approach is slow, so a grid stopping at `10^4` leaves a gap of 0.024 at `r = 3` that
    # reads as a failure of the ray form when it is a failure of the grid.
    grid = [mpf(10) ** (mpf(k) / mpf(12)) for k in range(-36, 121)]
    for z in grid:
        coeffs = den_coeffs(xs, r, z)
        rts = polyroots(coeffs, maxsteps=300, extraprec=600)
        mods = sorted(rts, key=fabs)
        tmin = mods[0]
        if fabs(im(tmin)) < mpf(10) ** (-20):
            continue                      # minimum-modulus root is real: off the arc
        # (G1) the minimum modulus is attained by a conjugate PAIR and nothing else
        m0 = fabs(mods[0])
        same = [t for t in mods if fabs(fabs(t) - m0) < mpf(10) ** (-25)]
        assert len(same) == 2, \
            f"minimum modulus attained {len(same)} times at r={r}, xs={xs}, z={z}"
        a, b = same
        assert fabs(a - mpc(re(b), -im(b))) < mpf(10) ** (-25), \
            f"the two minimal roots are not conjugate at r={r}, xs={xs}, z={z}"
        # separation from the next root up -- the gap `thm:FT-geometry` asserts
        rest = [fabs(t) for t in mods if fabs(t) - m0 > mpf(10) ** (-25)]
        if rest:
            worst_pair_gap = min(worst_pair_gap, rest[0] / m0 - 1)
        # (G2) simplicity: D'(t) != 0 at the pair
        dcoef = [c * (len(coeffs) - 1 - i) for i, c in enumerate(coeffs[:-1])]
        dv = mpc(0)
        for c in dcoef:
            dv = dv * a + c
        worst_simple = min(worst_simple, fabs(dv))
        assert fabs(dv) > TOL, \
            f"the principal pair is NOT simple at r={r}, xs={xs}, z={z}: D'={dv}"
        th = arg(a) if im(a) > 0 else arg(b)
        # (G3) theta lies in the open viewing arc
        assert 0 < th < pi / r, \
            f"theta={th} outside (0, pi/{r}) at xs={xs}, z={z}"
        thetas.append(th)
        zs.append(z)
        total_samples += 1

    assert len(thetas) >= 12, f"too few arc samples at r={r}, xs={xs}: {len(thetas)}"
    # (G3) strict monotonicity of z |-> theta
    for i in range(1, len(thetas)):
        assert thetas[i] > thetas[i - 1] - mpf(10) ** (-25), \
            f"theta is not increasing in z at r={r}, xs={xs}: " \
            f"{thetas[i-1]} then {thetas[i]}"

    # (G4) for r > 1 the arc runs to pi/r as z grows: the interval is a ray
    if r > 1:
        # The claim is CONVERGENCE, so it is checked as convergence: the gap to `pi/r` must
        # shrink as `z` grows, and be small at the top of the sweep.  A bare threshold would
        # be a statement about the grid.
        gap_top = pi / r - thetas[-1]
        gap_mid = pi / r - thetas[len(thetas) // 2]
        assert gap_top < gap_mid / 4, \
            f"at r={r}, xs={xs} the gap to pi/r is not closing: {mp.nstr(gap_mid,6)} at the " \
            f"middle of the sweep against {mp.nstr(gap_top,6)} at the top"
        assert gap_top < mpf('0.02'), \
            f"at r={r}, xs={xs} the arc stops {mp.nstr(gap_top,6)} short of pi/r even at " \
            f"z = 1e10; `eq:ab-def`'s ray form would fail"
    print(f"      r = {r}, n = {n}, zeros {[mp.nstr(x,4) for x in xs]}: "
          f"{len(thetas)} arc samples, theta from {mp.nstr(thetas[0],6)} "
          f"to {mp.nstr(thetas[-1],6)} (pi/r = {mp.nstr(pi/r,6)}, "
          f"gap {mp.nstr(pi/r - thetas[-1],4)})")

print(f"\nPASS  thm:FT-geometry holds at every one of {total_samples} samples across "
      f"{len(PENCILS)} pencils with r = 2..6")
print(f"PASS  the principal pair is simple throughout: min |D'(t_+)| = "
      f"{mp.nstr(worst_simple, 8)}")
print(f"PASS  the pair is strictly separated from the rest of the spectrum: "
      f"smallest relative gap to the next root = {mp.nstr(worst_pair_gap, 8)}")


# --------------------------------------------------------------------------
# The r = 1 contrast, so the ray form of `eq:ab-def` is shown to be about r > 1
# and not an artifact of the sweep.  At r = 1 the interval is BOUNDED.
# --------------------------------------------------------------------------

bounded_seen = False
for xs in ([mpf(1), mpf(2)], [mpf(1), mpf(1), mpf(1)]):
    top = mpf(0)
    for k in range(-36, 61):
        z = mpf(10) ** (mpf(k) / mpf(12))
        rts = polyroots(den_coeffs(xs, 1, z), maxsteps=300, extraprec=600)
        mods = sorted(rts, key=fabs)
        if fabs(im(mods[0])) < mpf(10) ** (-20):
            continue
        top = max(top, z)
    # a bounded interval: the sweep runs to 10^5 and the arc ends well below it
    if top < mpf(10) ** 4:
        bounded_seen = True
        print(f"      r = 1, zeros {[mp.nstr(x,4) for x in xs]}: the arc ends at "
              f"z = {mp.nstr(top,8)}, so I_(Q,1) is BOUNDED")

assert bounded_seen, \
    "no bounded interval found at r = 1, so the ray form asserted for r > 1 above is not " \
    "shown to be a property of r rather than of the sweep"
print("\nPASS  the ray form is a property of r > 1: at r = 1 the same sweep finds a "
      "bounded interval, which is the `eq:ab-def` dichotomy")
print("ALL PASS  check_ft_geometry_general_r.py")
