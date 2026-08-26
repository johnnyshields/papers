#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`;
`eq:contour-remainder-bound`, `eq:ab-def`.

`hCbd_1`'s CONCLUSION at `r = 1`, not its premise.

`check_upper_endpoint_regimes.py` settles the premise: at `r = 1` the spectral
parameter tends to a FINITE limit, so `EndpointSeparation`'s upper circle -- which
is conditioned on `ftUpperWindow <= |z|` -- is cleared by no constant whatever and
the `r >= 2` route to `hCbd_1` is unavailable rather than merely inconvenient.
That is not repeated here.

What is measured here is the replacement.  A bounded parameter is the HYPOTHESIS
of the `r = 1` route: `D(.,z(pi-delta))` differs from the limiting pencil
`D_b = Q + bX` by `(z - b)t^r`, which is uniformly small on a fixed circle, so any
circle carrying no zero of `D_b` carries a bound on `B/D`.

  (C1) The limit point is algebraic, not fitted: `L` solves `sum_k L/(a_k+L) = 1`
       -- which is `E(-L) = 0` at `r = 1` -- and `b = -Q(-L)/(-L)` is the branch's
       own parameter there.  The branch's `tau(pi-delta)` and `z(pi-delta)` are
       checked to run into that `L` and that `b`, so the pencil the bound is proved
       against is the pencil the branch actually approaches.
  (C2) `-L` is a DOUBLE root of `D_b` and not a triple one: `D_b(-L) = D_b'(-L) = 0`
       with `D_b''(-L) != 0`.  This is the same fact `hamp_1` runs on, in the
       opposite direction -- it is why the amplitude diverges and why the circle
       has to be placed past the collision rather than around it.
  (C3) On a circle past every zero of `D_b`, `|D(.,z(pi-delta))|` stays bounded
       BELOW across four decades of `delta`, and `sup |B/D|` over that circle stays
       bounded ABOVE and CONVERGES rather than drifting.  Both bounds are computed
       from the roots -- `|D(t)| >= |lead| prod_j (R - |rho_j|)` for `|t| = R` past
       every `|rho_j|` -- so neither rests on a grid.
  (C4) Negative control: the radius is load-bearing.  On a circle placed exactly at
       a zero of `D_b`, the same supremum DIVERGES as `delta -> 0`.  Without this,
       (C3) would be consistent with the bound holding for reasons unrelated to
       where the circle sits.

mpmath only, 50 digits.  The branch comes from the MONOTONE angle-sum of
`Forgacs2017RationalDenominator` Lemma 2(ii) plus the minimum-modulus test, never
from bisecting `Im(Q(w)/w^r)`.
"""
from mpmath import (mp, mpf, mpc, exp, pi, arg, findroot, polyroots, im, re,
                    fabs, log)

mp.dps = 50


def qcoeffs(c, a):
    poly = [mpf(c)]
    for ak in a:
        nxt = [mpf(0)] * (len(poly) + 1)
        for i, co in enumerate(poly):
            nxt[i] += co * mpf(ak)
            nxt[i + 1] -= co
        poly = nxt
    return poly[::-1]


def peval(C, t):
    v = mpc(0)
    for co in C:
        v = v * t + co
    return v


def dcoeffs(Q, z, r):
    D = [mpf(0)] * max(0, r + 1 - len(Q)) + list(Q)
    D[len(D) - 1 - r] += z
    while len(D) > 1 and D[0] == 0:
        D = D[1:]
    return D


def deriv(C):
    d = len(C) - 1
    return [C[i] * (d - i) for i in range(d)] if d > 0 else [mpf(0)]


def angle_sum(a, r, theta, tau):
    w = mpc(tau) * exp(mpc(0, 1) * theta)
    return sum(arg(mpc(ak) - w) for ak in a) - r * theta


def branch(c, a, r, theta):
    """Branch radius: monotone angle-sum, then the minimum-modulus test."""
    Q = qcoeffs(c, a)
    lo, hi = mpf(10)**-14, mpf(max(a)) * 4
    Slo, Shi = angle_sum(a, r, theta, lo), angle_sum(a, r, theta, hi)
    cands = []
    for l in range(int(mp.floor(-Slo / pi)) - 1, int(mp.ceil(-Shi / pi)) + 2):
        target = -mpf(l) * pi
        if not (Shi < target < Slo):
            continue
        cands.append(mpf(re(findroot(
            lambda t: angle_sum(a, r, theta, t) - target, (lo, hi),
            solver='bisect', tol=mpf(10)**-40))))
    for tau in sorted(cands):
        w = mpc(tau) * exp(mpc(0, 1) * theta)
        zc = -peval(Q, w) / w**r
        if fabs(im(zc)) > mpf(10)**-25:
            continue
        z = mpf(re(zc))
        rts = polyroots(dcoeffs(Q, z, r), maxsteps=400, extraprec=800)
        if min(fabs(t - w) for t in rts) > mpf(10)**-22:
            continue
        if fabs(fabs(w) - min(fabs(t) for t in rts)) < mpf(10)**-22:
            return tau, z, Q
    raise AssertionError(f"no minimum-modulus branch at theta={theta}, r={r}")


def endpoint_L(a):
    """The `L > 0` of `sum_k L/(a_k+L) = 1`, which is `E(-L) = 0` at `r = 1`."""
    f = lambda L: sum(L / (mpf(ak) + L) for ak in a) - 1
    lo, hi = mpf(10)**-10, mpf(max(a)) * mpf(len(a)) * 8
    assert f(lo) < 0 < f(hi), "the deficit equation does not bracket a root"
    return mpf(re(findroot(f, (lo, hi), solver='bisect', tol=mpf(10)**-45)))


def bound_from_roots(Bc, Dc, R):
    """(lower bound on |D| over |t| = R, upper bound on sup |B/D| there).

    For `|t| = R` past every root, `|t - rho| >= R - |rho|`, so
    `|D(t)| >= |lead| prod (R - |rho|)`; and `|B(t)| <= sum |b_i| R^i`.  No grid.
    """
    rts = polyroots(Dc, maxsteps=400, extraprec=800)
    assert all(fabs(t) < R for t in rts), "the circle is not past every root"
    lo = fabs(Dc[0])
    for t in rts:
        lo *= (R - fabs(t))
    hi = sum(fabs(co) * R**(len(Bc) - 1 - i) for i, co in enumerate(Bc))
    return lo, hi / lo


def sup_ratio_grid(Bc, Dc, R, m=1440):
    """Sampled sup of |B/D| on |t| = R -- reported, never asserted on."""
    best = mpf(0)
    for k in range(m):
        t = R * exp(mpc(0, 1) * (2 * pi * k / m))
        d = fabs(peval(Dc, t))
        if d == 0:
            return mp.inf
        best = max(best, fabs(peval(Bc, t)) / d)
    return best


def ratio_on_ray(Bc, Dc, R, rho):
    """|B/D| at the point of `|t| = R` on the ray through the root nearest `rho`.

    A LOWER bound on the supremum, evaluated exactly.  A grid cannot serve here:
    a root approaching the circle tangentially sits closer to it than any fixed
    angular step, so a sampled supremum saturates at the step size and reports a
    bounded quantity that is not bounded.
    """
    rts = polyroots(Dc, maxsteps=400, extraprec=800)
    near = min(rts, key=lambda t: fabs(t - rho))
    t = R * near / fabs(near)
    return fabs(peval(Bc, t)) / fabs(peval(Dc, t))


# B = X + 3, a numerator that is neither constant nor vanishing on the negative
# axis inside the circles used below.
BC = [mpf(1), mpf(3)]

PENCILS = [([1.0, 1.0, 2.0], 1.0, "a=(1,1,2) c=1"),
           ([1.0, 1.0, 1.0, 2.0], 1.0, "a=(1,1,1,2) c=1"),
           ([0.4, 0.4, 1.7], 2.5, "a=(0.4,0.4,1.7) c=2.5")]
DELTAS = [mpf(10)**-2, mpf(10)**-3, mpf(10)**-4, mpf(10)**-5]

print("hCbd_1 at r = 1: the contour bound from a convergent spectral parameter")
print()

collisions = []
uniform = []
control = []

for a, c, lab in PENCILS:
    Q = qcoeffs(c, a)
    L = endpoint_L(a)
    b = mpf(re(-peval(Q, mpf(-L)) / mpf(-L)))
    Db = dcoeffs(Q, b, 1)

    # (C1) the branch runs into that L and that b
    tau_e, z_e, _ = branch(c, a, 1, pi - DELTAS[-1])
    dL, db = fabs(tau_e - L), fabs(z_e - b)

    # (C2) the collision is a double root, not a triple one
    v0 = fabs(peval(Db, mpc(-L)))
    v1 = fabs(peval(deriv(Db), mpc(-L)))
    v2 = fabs(peval(deriv(deriv(Db)), mpc(-L)))
    collisions.append((lab, L, b, dL, db, v0, v1, v2))
    print(f"  {lab}: L {mp.nstr(L,10)}  b {mp.nstr(b,10)}   "
          f"|tau(pi-1e-5)-L| {mp.nstr(dL,4)}  |z(pi-1e-5)-b| {mp.nstr(db,4)}")
    print(f"      at -L:  |D_b| {mp.nstr(v0,4)}   |D_b'| {mp.nstr(v1,4)}   "
          f"|D_b''| {mp.nstr(v2,6)}")

    # (C3) a circle past every zero of D_b
    rts_b = polyroots(Db, maxsteps=400, extraprec=800)
    R = max(fabs(t) for t in rts_b) * mpf(3) / 2
    lows, sups, grids = [], [], []
    for d in DELTAS:
        _, z, _ = branch(c, a, 1, pi - d)
        Dz = dcoeffs(Q, z, 1)
        lo, hi = bound_from_roots(BC, Dz, R)
        lows.append(lo)
        sups.append(hi)
        grids.append(sup_ratio_grid(BC, Dz, R))
    spread = (max(sups) - min(sups)) / min(sups)
    uniform.append((lab, R, min(lows), max(sups), spread))
    print(f"      R {mp.nstr(R,8)} (past every zero of D_b): "
          f"min |D| {'  '.join(mp.nstr(v,5) for v in lows)}")
    print(f"      certified sup |B/D| {'  '.join(mp.nstr(v,6) for v in sups)}   "
          f"(sampled {'  '.join(mp.nstr(v,6) for v in grids)})")

    # (C4) the same supremum, on a circle placed AT a zero of D_b
    rho_star = max(rts_b, key=fabs)
    Rbad = fabs(rho_star)
    bad = []
    for d in DELTAS:
        _, z, _ = branch(c, a, 1, pi - d)
        bad.append(ratio_on_ray(BC, dcoeffs(Q, z, 1), Rbad, rho_star))
    control.append((lab, Rbad, bad))
    print(f"      control, R at a zero of D_b ({mp.nstr(Rbad,8)}): "
          f"sup |B/D| {'  '.join(mp.nstr(v,6) for v in bad)}")
    print()

# (C1)
for lab, L, b, dL, db, *_ in collisions:
    assert L > 0, f"{lab}: the deficit equation gave L = {mp.nstr(L,8)}, not positive"
    assert dL < mpf(10)**-3, (
        f"{lab}: tau(pi-1e-5) misses the algebraic L by {mp.nstr(dL,6)} -- the "
        f"pencil the bound is proved against is not the one the branch approaches")
    assert db < mpf(10)**-3, (
        f"{lab}: z(pi-1e-5) misses b = -Q(-L)/(-L) by {mp.nstr(db,6)}")
print(f"PASS  (C1) at all {len(collisions)} pencils the branch runs into the "
      f"ALGEBRAIC endpoint: L solves sum_k L/(a_k+L) = 1, and z -> -Q(-L)/(-L)")

# (C2)
for lab, L, _, _, _, v0, v1, v2 in collisions:
    assert v0 < mpf(10)**-20, f"{lab}: -L is not a root of D_b, |D_b(-L)| = {mp.nstr(v0,6)}"
    assert v1 < mpf(10)**-20, f"{lab}: |D_b'(-L)| = {mp.nstr(v1,6)} does not vanish"
    assert v2 > mpf(1) / 100, (
        f"{lab}: |D_b''(-L)| = {mp.nstr(v2,6)} -- the collision would be at least "
        f"triple, and Q'' is a sum of positive terms on the negative axis")
print(f"PASS  (C2) the collision at -L is EXACTLY double at all "
      f"{len(collisions)} pencils: D_b(-L) = D_b'(-L) = 0 with D_b''(-L) != 0")

# (C3)
for lab, R, lo, hi, spread in uniform:
    assert lo > mpf(1) / 1000, (
        f"{lab}: |D| falls to {mp.nstr(lo,6)} on the circle R = {mp.nstr(R,6)} -- "
        f"the bound would then hold by Lean's division convention rather than by "
        f"the geometry")
    assert hi < mpf(10)**4, f"{lab}: sup |B/D| reaches {mp.nstr(hi,6)}"
    assert spread < mpf(1) / 10, (
        f"{lab}: the certified sup drifts by {mp.nstr(spread*100,4)}% across four "
        f"decades of delta -- a bound that drifts is a bound on this grid, not a "
        f"constant C_1")
print(f"PASS  (C3) on a circle past every zero of D_b the pencil is bounded away "
      f"from zero and sup |B/D| CONVERGES across four decades of delta, at all "
      f"{len(uniform)} pencils -- one C_1 serves the whole punctured window")

# (C4)
for lab, Rbad, bad in control:
    growth = bad[-1] / bad[0]
    assert growth > 10, (
        f"{lab}: on a circle AT a zero of D_b the supremum grew only by "
        f"{mp.nstr(growth,6)} -- if it stays bounded there too, the radius "
        f"hypothesis R_0 <= R_1 is decoration")
print(f"PASS  (C4) the radius is load-bearing: on a circle placed AT a zero of "
      f"D_b the same supremum DIVERGES as delta -> 0, at all {len(control)} "
      f"pencils")

print("INFO  the PREMISE -- that |z| is bounded at r = 1 and unbounded at r >= 2, "
      "so the z t^r route to hCbd_1 dies here -- is check_upper_endpoint_regimes.py "
      "and is not repeated")
print()
print("ALL PASS")
