#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; the `_0` retained group
at `rho = 1`, `eq:principal-pair`, `eq:ab-def`.

Whether the product clearance can supply the LOWER endpoint's retained radius.

The retained group needs `R_0` with the principal pair inside and every other root
of the limiting pencil outside, so what it consumes is a bound on the SMALLEST
non-collision root modulus.  What `EndpointCollision.clearance_ge_relative_gap_of_r`
bounds is `prod_k a_k / t^n - 1`, a bound on the PRODUCT of all roots.

At `n = 3` those coincide: the collision accounts for `t^2` and exactly one root is
left, so the product IS that root.  From `n = 4` the product runs over `n - 2`
roots and a product bound does not bound the smallest of them.  This is the same
obstruction `check_upper_endpoint_general_n.py` records as (G4) at the other
endpoint, and the question here is whether it bites at this one too.

  (L1) The pair really is the only thing near the origin: `min |w| / t_a` over the
       non-collision roots exceeds 1 at every pencil, so a retained radius exists.
  (L2) The SPREAD `max/min` over those roots, which is what decides whether a
       product bound can be inverted into a bound on the smallest.  At `n = 3` it
       is exactly 1 by construction -- one root.
  (L3) The product-derived lower bound on the smallest, `(prod/t^2)^(1/(n-2))`
       divided by the true smallest.  Above 1 means the product route would CLAIM
       more clearance than the smallest root has, i.e. it is unsound as a bound on
       the smallest; that ratio is the size of the error.

Pencils carry a simple smallest zero -- `rho = 1` -- and include both comfortable
and lopsided tails, since a comfortable tail is exactly what hides a spread.
"""

from mpmath import mp, mpf, mpc, fabs, findroot, polyroots

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


def deriv(C):
    d = len(C) - 1
    return [C[i] * (d - i) for i in range(d)] if d > 0 else [mpf(0)]


def dcoeffs(Q, z, r):
    D = [mpf(0)] * max(0, r + 1 - len(Q)) + list(Q)
    D[len(D) - 1 - r] += z
    while len(D) > 1 and D[0] == 0:
        D = D[1:]
    return D


def Ecoeffs(c, a, r):
    Q = qcoeffs(c, a)
    dQ = deriv(Q)
    E = [mpf(0)] * (len(Q))
    for i, co in enumerate(dQ):
        E[i] += co
    for i, co in enumerate(Q):
        E[i] -= mpf(r) * co
    while len(E) > 1 and E[0] == 0:
        E = E[1:]
    return E


PENCILS = [([1.0, 2.0, 3.0], "n=3 a=(1,2,3)"),
           ([1.0, 2.0, 3.0, 4.0], "n=4 a=(1,2,3,4) comfortable"),
           ([1.0, 1.1, 8.0, 9.0], "n=4 a=(1,1.1,8,9) lopsided tail"),
           ([1.0, 2.0, 3.0, 4.0, 5.0], "n=5 a=(1,..,5) comfortable"),
           ([1.0, 1.05, 6.0, 30.0, 60.0], "n=5 a=(1,1.05,6,30,60) spread tail"),
           ([1.0, 1.05, 3.0, 4.0, 20.0, 90.0], "n=6 spread tail"),
           # the confluent direction, where the clearance infimum is 1 and
           # unattained -- omitting it would let (L1) report a margin belonging to
           # the sampler rather than to the geometry
           ([1.0, 1.01, 1.02], "n=3 a=(1,1.01,1.02) near-uniform"),
           ([1.0, 1.001, 1.002], "n=3 a=(1,1.001,1.002) near-uniform"),
           ([1.0, 1.001, 1.002, 1.003], "n=4 near-uniform")]
RS = [1, 2]

print("the rho = 1 lower retained radius: can a PRODUCT clearance supply it?")
print()

rows = []
for a, lab in PENCILS:
    n = len(a)
    for r in RS:
        c = mpf(1)
        E = Ecoeffs(c, a, r)
        ta = mpf(findroot(lambda t: peval(E, t).real,
                          (mpf(a[0]) * (1 + mpf(10)**-9), mpf(a[1]) * (1 - mpf(10)**-9)),
                          solver='bisect', tol=mpf(10)**-40).real)
        b = -peval(qcoeffs(c, a), ta) / ta**r
        rts = polyroots(dcoeffs(qcoeffs(c, a), mpf(b.real), r),
                        maxsteps=600, extraprec=1200)
        # drop the double collision at t_a
        others = sorted(rts, key=lambda w: fabs(w - ta))[2:]
        assert len(others) == n - 2, f"{lab} r={r}: {len(others)} non-collision roots"
        mods = sorted(fabs(w) / ta for w in others)
        kmin, kmax = mods[0], mods[-1]
        prod = mpf(1)
        for w in others:
            prod *= fabs(w) / ta
        geo = prod ** (mpf(1) / (n - 2))
        rows.append((lab, r, n, ta, kmin, kmax, geo))
        print(f"  {lab}  r={r}")
        print(f"      t_a {mp.nstr(ta,10)}   min|w|/t_a {mp.nstr(kmin,7)}   "
              f"max|w|/t_a {mp.nstr(kmax,7)}   spread {mp.nstr(kmax/kmin,7)}")
        print(f"      geometric mean of the n-2 ratios {mp.nstr(geo,7)}   "
              f"geo/min {mp.nstr(geo/kmin,7)}")
print()

# (L1)
for lab, r, n, ta, kmin, kmax, geo in rows:
    assert kmin > 1, f"{lab} r={r}: min ratio {mp.nstr(kmin,6)} is not above 1"
tight = min(k for _, _, _, _, k, _, _ in rows)
print(f"PASS  (L1) at all {len(rows)} pencil/r pairs every non-collision root sits "
      f"strictly outside the collision radius, so a retained radius exists at each "
      f"one.  The tightest is {mp.nstr(tight,6)} t_a, and that number is NOT a "
      f"constant to build on: it comes from the near-uniform pencils, where the "
      f"ratio approaches 1 as the zeros confluence.  A family of comfortable "
      f"pencils would have reported a margin belonging to the family")
assert tight < mpf(11) / 10, (
    "the near-uniform pencils did not drive the clearance toward 1 -- either they "
    "are not near-uniform enough or the infimum is not 1, and (L1)'s margin claim "
    "must be re-read before it is trusted")

# (L2)/(L3) -- the finding, not a pass/fail on the tree
n3 = [x for x in rows if x[2] == 3]
big = [x for x in rows if x[2] >= 4]
for lab, r, n, ta, kmin, kmax, geo in n3:
    assert fabs(kmax / kmin - 1) < mpf(10)**-20, f"{lab}: n=3 should have one root"
    assert fabs(geo / kmin - 1) < mpf(10)**-20, f"{lab}: n=3 geo should BE the root"
print(f"PASS  (L2) at n = 3 the spread is exactly 1 and the geometric mean IS the "
      f"single remaining root, so the product clearance and the smallest-root "
      f"clearance are the same number -- which is why the Fin 3 statement can be "
      f"read as either")

worst = max(x[6] / x[4] for x in big)
spread = max(x[5] / x[4] for x in big)
assert worst > 2, (
    "the product route's overclaim never exceeded 2x on these pencils -- if that "
    "holds up the product bound may be usable after all, and this row should be "
    "re-read rather than trusted")
print(f"PASS  (L3) from n = 4 they come apart.  The spread max/min over the "
      f"non-collision roots reaches {mp.nstr(spread,6)}, and the geometric mean "
      f"overstates the SMALLEST root's clearance by up to {mp.nstr(worst,6)}x.  So "
      f"a bound on prod_k a_k / t^n does NOT yield a bound on the smallest "
      f"non-collision root, and the lower retained radius cannot be derived from "
      f"the clearance alone at n >= 4 -- the same obstruction "
      f"check_upper_endpoint_general_n.py records as (G4) at the upper endpoint, "
      f"where it was answered by a PER-ROOT bound "
      f"(two_mul_lt_norm_of_root_endpoint_pi) rather than a product one")

print()
print("ALL PASS")
