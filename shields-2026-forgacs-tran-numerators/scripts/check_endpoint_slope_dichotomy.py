#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; the lower endpoint of
`eq:ab-def`, `eq:principal-pair`.

The radial slope `(tau(theta) - t_a)/theta` at the LOWER endpoint, measured across
the multiplicity, against the criterion the Lean proof uses.

`PencilArcSymmetry.tendsto_slope_of_ftPencilIm_eq_zero` concludes the slope
vanishes from ONE hypothesis about the pencil: `E'(t_a) != 0`, where
`E(t) = t Q'(t) - r Q(t)`.  It says nothing about `rho`.  That is a strong claim,
because the `rho >= 2` slope is already known by a different route --
`EndpointPackage.tendsto_ftTau_blowup` gives it as `-x_1 cot(pi/rho)` -- so the two
must agree wherever both apply, and disagreeing would mean one of them is wrong.

They do agree, and the agreement is not a coincidence of one pencil:

  E'(x_1) = x_1 Q''(x_1) at a zero of multiplicity rho >= 2, so among rho >= 2 the
  derivative is nonzero exactly at rho = 2.  And cot(pi/rho) vanishes exactly at
  rho = 2.  So both routes call the slope zero on exactly the same set.

  (S1) rho = 1: `E'(t_a) != 0` and the approach is quadratic.  This is the case the
       Lean theorem is FOR.
  (S2) rho = 2: `E'(t_a) != 0` and the approach is again quadratic -- the criterion
       predicts a vanishing slope at a multiplicity where the cluster route
       independently gives `-x_1 cot(pi/2) = 0`.
  (S3) rho = 3: `E'(t_a) = 0`, the criterion does not apply, and the approach is
       LINEAR with slope `-x_1/sqrt(3)`.  This is the negative control: without it
       (S1) and (S2) would be consistent with a theorem that is simply always true.

Measured at `r = 1` and `r = 2`, since the criterion names `r` only through `E`.
"""

from mpmath import (mp, mpf, mpc, exp, arg, re, im, fabs, pi, log, cot, findroot,
                    polyroots)

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
            return tau
    raise AssertionError(f"no minimum-modulus branch at theta={theta}, r={r}")


def Ecoeffs(c, a, r):
    """E = X Q' - r Q, as a coefficient list."""
    Q = qcoeffs(c, a)
    dQ = deriv(Q)
    n = len(Q) - 1
    E = [mpf(0)] * (n + 1)
    for i, co in enumerate(dQ):                 # X * Q' raises degree by one
        E[i] += co
    for i, co in enumerate(Q):
        E[i] -= mpf(r) * co
    while len(E) > 1 and E[0] == 0:
        E = E[1:]
    return E


PENCILS = [([1.0, 2.0, 3.0], 1.0, 1, 1, "(S1) rho=1 r=1  a=(1,2,3)"),
           ([1.0, 2.0, 3.0], 1.0, 2, 1, "(S1) rho=1 r=2  a=(1,2,3)"),
           ([1.0, 1.0, 2.0], 1.0, 1, 2, "(S2) rho=2 r=1  a=(1,1,2)"),
           ([1.0, 1.0, 2.0], 1.0, 2, 2, "(S2) rho=2 r=2  a=(1,1,2)"),
           ([1.0, 1.0, 1.0], 1.0, 1, 3, "(S3) rho=3 r=1  a=(1,1,1)"),
           ([1.0, 1.0, 1.0], 1.0, 2, 3, "(S3) rho=3 r=2  a=(1,1,1)")]
THETAS = [mpf(10)**-2, mpf(10)**-3, mpf(10)**-4, mpf(10)**-5]

print("the lower endpoint's radial slope, against the criterion E'(t_a) != 0")
print()

rows = []
for a, c, r, rho, lab in PENCILS:
    E = Ecoeffs(c, a, r)
    dE = deriv(E)
    taus = [branch(c, a, r, th) for th in THETAS]
    ta = mpf(re(findroot(lambda t: peval(E, t), taus[-1], tol=mpf(10)**-40)))
    dEta = fabs(peval(dE, ta))
    devs = [fabs(t - ta) for t in taus]
    slope = (log(devs[0]) - log(devs[-1])) / (log(THETAS[0]) - log(THETAS[-1]))
    rows.append((lab, rho, ta, dEta, devs, slope, taus[-1]))
    print(f"  {lab}")
    print(f"      t_a {mp.nstr(ta,12)}   |E'(t_a)| {mp.nstr(dEta,8)}")
    print(f"      |tau - t_a| {'  '.join(mp.nstr(v,6) for v in devs)}")
    print(f"      log-log exponent in theta {mp.nstr(slope,8)}   "
          f"slope at 1e-5 {mp.nstr(devs[-1]/THETAS[-1],6)}")
    print()

# (S1)/(S2) -- the criterion holds, and the approach is quadratic
for lab, rho, ta, dEta, devs, slope, _ in rows:
    if rho >= 3:
        continue
    assert dEta > mpf(10)**-8, f"{lab}: E'(t_a) = {mp.nstr(dEta,6)} is not nonzero"
    assert fabs(slope - 2) < mpf(1) / 20, (
        f"{lab}: exponent {mp.nstr(slope,8)}, expected 2")
    assert devs[-1] / THETAS[-1] < mpf(10)**-3, (
        f"{lab}: slope {mp.nstr(devs[-1]/THETAS[-1],6)} at 1e-5 is not collapsing")
print("PASS  (S1)+(S2) wherever E'(t_a) != 0 the approach is QUADRATIC, exponent 2 "
      "to within 5e-2, and the radial slope is below 1e-3 at theta = 1e-5.  At "
      "rho = 2 that agrees with -x_1 cot(pi/2) = 0 from the cluster route, which "
      "is an independent derivation -- so the Lean criterion gets the right answer "
      "at a multiplicity it was not designed for")

# (S3) -- the negative control
for lab, rho, ta, dEta, devs, slope, _ in rows:
    if rho < 3:
        continue
    assert dEta < mpf(10)**-8, (
        f"{lab}: E'(t_a) = {mp.nstr(dEta,6)}, expected 0 at rho >= 3")
    assert fabs(slope - 1) < mpf(1) / 20, (
        f"{lab}: exponent {mp.nstr(slope,8)}, expected 1")
    lin = devs[-1] / THETAS[-1]
    assert lin > mpf(1) / 10, (
        f"{lab}: slope {mp.nstr(lin,6)} is not bounded away from 0")
    # and it is not merely nonzero: it is the cluster route's own constant
    predicted = ta * cot(pi / rho)
    assert fabs(lin - predicted) < mpf(10)**-4, (
        f"{lab}: slope {mp.nstr(lin,8)} against x_1 cot(pi/rho) "
        f"{mp.nstr(predicted,8)}")
print("PASS  (S3) at rho = 3 the criterion FAILS -- E'(t_a) = 0 -- and the approach "
      "is LINEAR, exponent 1, and the slope is x_1 cot(pi/rho) to within 1e-4 -- "
      "the cluster route's own constant, arrived at from the pencil rather than "
      "from the cluster.  So the theorem is not vacuously true: its hypothesis is "
      "what separates the two behaviors, and it separates them at r = 1 and r = 2")

print()
print("ALL PASS")
