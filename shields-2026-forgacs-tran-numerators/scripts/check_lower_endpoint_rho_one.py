#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `sec:geometry`,
`eq:ab-def`, `thm:FT-geometry`.

The `rho = 1` lower endpoint is the MIRROR of the `r = 1` upper endpoint, not a
degenerate case of the cluster picture.

At `rho >= 2` the lower endpoint is a cluster of `rho` roots collapsing onto the
smallest zero `x_1`, and `clusterAlpha x_1 rho j = -x_1 omega_j / sin(pi/rho)`
describes their slopes.  At `rho = 1` that parameterization degenerates --
`sin(pi/1) = 0` and `clusterAlpha x_1 1 j = 0` -- which reads as the endpoint
being harder.  It is not: the parameterization is simply the wrong one, because
at `rho = 1` the collision does not happen at `x_1` at all.

  (R1) At `rho = 1` the principal radius tends to `t_a`, the smallest positive
       CRITICAL POINT of `g = -Q/t^r`, and NOT to `x_1`.  Measured at `r = 1` and
       `r = 2`, so this is a statement about `rho`, not about `r`.
  (R2) `E(t_a) = 0` there, `E(t) = t Q'(t) - r Q(t)` -- the same endpoint
       condition that gives the double root at the `r = 1` upper endpoint.
  (R3) The cofactor `|D'(t_+)|` vanishes LINEARLY in the angle, so the collision
       is a double root of the limiting pencil.
  (R4) Therefore the amplitude BLOWS UP, exponent `-1`, exactly as at the `r = 1`
       upper endpoint -- `ftAmp = -B(tau)/D'(tau)` is a residue.
  (R5) And the separation the fixed radius needs holds: the limiting pencil has a
       root of multiplicity EXACTLY 2 at `t_a`, and every other root is strictly
       outside `|t_a|`.  Those are the same two facts, checked the same way, that
       decided the `r = 1` upper endpoint.

So the machinery built for the `r = 1` upper endpoint -- the endpoint condition
as a root order, the root-count transfer along a limit, the amplitude floor from
a blow-up -- is the machinery this case wants, with `t_a` in place of `-L`.  What
does NOT transfer is anything phrased through `clusterAlpha`.

mpmath only, 45 digits.  The branch comes from the monotone angle-sum, and `t_a`
independently from a sign change of `E` on `(0, max a)`, so (R1) compares two
quantities computed by different routes rather than restating one.
"""
from mpmath import (mp, mpf, mpc, exp, pi, arg, findroot, polyroots, im, re,
                    fabs, log)

mp.dps = 45


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


def angle_sum(a, r, theta, tau):
    w = mpc(tau) * exp(mpc(0, 1) * theta)
    return sum(arg(mpc(ak) - w) for ak in a) - r * theta


def branch(c, a, r, theta):
    Q = qcoeffs(c, a)
    lo, hi = mpf(10)**-14, mpf(max(a)) * 4
    Slo, Shi = angle_sum(a, r, theta, lo), angle_sum(a, r, theta, hi)
    cands = []
    for l in range(int(mp.floor(-Slo / pi)) - 1, int(mp.ceil(-Shi / pi)) + 2):
        target = -mpf(l) * pi
        if not (Shi < target < Slo):
            continue
        cands.append(mpf(re(findroot(
            lambda u: angle_sum(a, r, theta, u) - target, (lo, hi),
            solver='bisect', tol=mpf(10)**-38))))
    for tau in sorted(cands):
        w = mpc(tau) * exp(mpc(0, 1) * theta)
        zc = -peval(Q, w) / w**r
        if fabs(im(zc)) > mpf(10)**-22:
            continue
        z = mpf(re(zc))
        rts = polyroots(dcoeffs(Q, z, r), maxsteps=400, extraprec=600)
        if min(fabs(t - w) for t in rts) > mpf(10)**-20:
            continue
        if fabs(fabs(w) - min(fabs(t) for t in rts)) < mpf(10)**-20:
            return tau, z, Q
    raise AssertionError(f"no minimum-modulus branch at theta={theta}, r={r}")


def critical_point(Q, r, hi):
    """Smallest positive `t_a` with `E(t_a) = 0`, found independently."""
    Qp = deriv(Q)
    E = lambda t: (t * peval(Qp, mpc(t)) - r * peval(Q, mpc(t))).real
    step, x = mpf(1) / 2000, mpf(1) / 2000
    prev = E(x)
    while x < hi:
        cur = E(x + step)
        if prev * cur < 0:
            return mpf(findroot(E, (x, x + step), solver='bisect',
                                tol=mpf(10)**-35))
        prev, x = cur, x + step
    raise AssertionError("no positive critical point")


PENCILS = [
    ([1.0, 2.0, 3.0], 1.0, 1, "a=(1,2,3), r=1"),
    ([1.0, 2.0, 3.0], 1.0, 2, "a=(1,2,3), r=2"),
    ([0.5, 1.7, 4.0], 2.0, 2, "a=(0.5,1.7,4), c=2, r=2"),
    ([1.0, 4.0, 9.0], 1.0, 3, "a=(1,4,9), r=3"),
]
THS = [mpf(10)**-3, mpf(10)**-4, mpf(10)**-5]

print("the rho = 1 lower endpoint: collision at t_a, not at x_1")
print()

rows = []
for a, c, r, lab in PENCILS:
    assert sum(1 for x in a if x == min(a)) == 1, f"{lab}: rho is not 1"
    Q = qcoeffs(c, a)
    ta = critical_point(Q, r, mpf(max(a)))
    data = []
    for th in THS:
        tau, z, _ = branch(c, a, r, th)
        w = mpc(tau) * exp(mpc(0, 1) * th)
        dp = peval(deriv(dcoeffs(Q, z, r)), w)
        data.append((tau, fabs(dp), fabs(mpc(1) / dp)))
    slope = ((log(data[0][2]) - log(data[-1][2]))
             / (log(THS[0]) - log(THS[-1])))
    rows.append((lab, a, ta, data, slope))
    print(f"  {lab}: x1={min(a)}  t_a={mp.nstr(ta,10)}  "
          f"tau(1e-5)={mp.nstr(data[-1][0],10)}  |D'|(1e-5)={mp.nstr(data[-1][1],6)}  "
          f"amplitude exponent={mp.nstr(slope,8)}")
print()

# (R1) tau -> t_a, not x_1
for lab, a, ta, data, slope in rows:
    assert fabs(data[-1][0] - ta) < mpf(10)**-8, (
        f"{lab}: tau(1e-5)={mp.nstr(data[-1][0],10)} does not approach "
        f"t_a={mp.nstr(ta,10)}")
    assert fabs(ta - mpf(min(a))) > mpf(1) / 100, (
        f"{lab}: t_a coincides with x_1, so this pencil cannot distinguish them")
print(f"PASS  (R1) at rho = 1 the principal radius tends to the CRITICAL POINT "
      f"t_a and not to x_1, at all {len(rows)} pencils, with t_a and tau computed "
      f"by different routes -- and t_a is well separated from x_1")

# (R2) t_a is where E vanishes -- the same condition as the r = 1 upper endpoint
for lab, a, ta, data, slope in rows:
    c = next(c for aa, c, r, l in PENCILS if l == lab)
    r = next(r for aa, c2, r, l in PENCILS if l == lab)
    Q = qcoeffs(c, a)
    E = (mpc(ta) * peval(deriv(Q), mpc(ta)) - r * peval(Q, mpc(ta)))
    assert fabs(E) < mpf(10)**-25 * max(mpf(1), fabs(peval(Q, mpc(ta)))), (
        f"{lab}: E(t_a) = {mp.nstr(fabs(E),8)} != 0")
print("PASS  (R2) E(t_a) = 0 with E(t) = tQ'(t) - rQ(t) -- the SAME endpoint "
      "condition that yields the double root at the r = 1 upper endpoint")

# (R3) the cofactor vanishes linearly, so the collision is a double root
for lab, a, ta, data, slope in rows:
    sl = ((log(data[0][1]) - log(data[-1][1])) / (log(THS[0]) - log(THS[-1])))
    assert fabs(sl - 1) < mpf(1) / 50, (
        f"{lab}: |D'| falls at order {mp.nstr(sl,8)}, not 1")
print("PASS  (R3) |D'(t_+)| vanishes LINEARLY in the angle at every pencil, so "
      "the limiting pencil has a double root at t_a")

# (R4) hence the amplitude blows up, exponent -1
for lab, a, ta, data, slope in rows:
    assert fabs(slope + 1) < mpf(1) / 50, (
        f"{lab}: amplitude exponent {mp.nstr(slope,8)}, expected -1")
    assert data[-1][2] > data[0][2], f"{lab}: |W| is not growing"
print("PASS  (R4) the amplitude exponent is -1 at every pencil -- ftAmp is a "
      "residue and its denominator vanishes, so |W| BLOWS UP exactly as at the "
      "r = 1 upper endpoint, and a constant floor serves for hamp_0 there too")

# (R5) The separation, which is what a fixed radius at this endpoint needs.
# At the endpoint parameter `a_end = -Q(t_a)/t_a^r` the limiting pencil should
# have a DOUBLE root at `t_a` and every other root strictly outside `|t_a|` --
# the same two facts the r = 1 upper endpoint needed at `-L`, and the same two
# that decide whether a fixed circle exists.
seps = []
for lab, a, ta, data, slope in rows:
    c = next(cc for aa, cc, rr, ll in PENCILS if ll == lab)
    r = next(rr for aa, cc, rr, ll in PENCILS if ll == lab)
    Q = qcoeffs(c, a)
    a_end = mpf((-peval(Q, mpc(ta)) / mpc(ta) ** r).real)
    D = dcoeffs(Q, a_end, r)
    v0 = fabs(peval(D, mpc(ta)))
    v1 = fabs(peval(deriv(D), mpc(ta)))
    v2 = fabs(peval(deriv(deriv(D)), mpc(ta)))
    assert v0 < mpf(10)**-25, f"{lab}: t_a is not a root, |D|={mp.nstr(v0,6)}"
    assert v1 < mpf(10)**-22, f"{lab}: |D'(t_a)|={mp.nstr(v1,6)} -- not a double root"
    assert v2 > mpf(1) / 1000, (
        f"{lab}: |D''(t_a)|={mp.nstr(v2,6)} -- multiplicity may exceed 2, so no "
        f"fixed radius isolates the pair")
    rts = sorted(polyroots(D, maxsteps=400, extraprec=800), key=lambda t: fabs(t))
    others = [t for t in rts if fabs(t - ta) > mpf(10)**-15]
    assert others, f"{lab}: the endpoint pencil has no root besides the collision"
    third = min(fabs(t) for t in others)
    assert third > mpf(ta), (
        f"{lab}: another root sits at modulus {mp.nstr(third,8)} <= t_a="
        f"{mp.nstr(ta,8)}, so no fixed radius separates the pair")
    seps.append((lab, third / mpf(ta), v2))
print(f"PASS  (R5) at the rho = 1 lower endpoint the limiting pencil has a root "
      f"of multiplicity EXACTLY 2 at t_a (worst |D''| = "
      f"{mp.nstr(min(x[2] for x in seps),6)}) and every other root strictly "
      f"outside, ratios " + ", ".join(mp.nstr(x[1], 6) for x in seps))
worst = min(x[1] for x in seps)
assert worst > 1 + mpf(1) / 100, f"the worst separation ratio is {mp.nstr(worst,8)}"
print(f"PASS  the worst ratio is {mp.nstr(worst,8)}, bounded away from 1, so a "
      f"FIXED separating radius exists at the rho = 1 lower endpoint -- the same "
      f"conclusion, by the same two facts, as at the r = 1 upper endpoint")

print()
print("ALL PASS  check_lower_endpoint_rho_one")
