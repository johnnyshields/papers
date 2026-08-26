#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`;
`eq:endpoint-linear-gap`, `eq:lower-cluster-expansion`.

The LOWER endpoint gap coefficient, at four pencils rather than one.

`check_lower_cluster_expansion.py` already pins this coefficient end to end, but
at a single pencil -- `Q = (1-t)^3`, `r = 1`, `rho = 3` -- and one pencil cannot
see two of the things the claim rests on.  At `rho = 3` there is exactly ONE
retained member (`rho - 2 = 1`), so the MINIMUM over retained indices that
`exists_lower_cluster_gap_coeff` produces is a minimum over a singleton and its
content is untested; and a coefficient measured at one cofactor cannot show that
the cofactor drops out.  Both are checked here, and the second is checked the
only way it can be: at a different cofactor, not at more digits of the first.

The claim, `hgapin_0`'s input:

    zeta_j(theta) = |g_j| / tau = 1 + c_j theta + O(theta^2),
    c_j = (cos(pi/rho) - cos(clusterAngle rho j)) / sin(pi/rho),
    clusterAngle rho j = (2j - 1) pi / rho.

Two indices must come out at coefficient EXACTLY zero -- the principal pair
`j = 0, 1`, since `clusterAngle rho 1 = pi/rho` and `clusterAngle rho 0` is its
negative -- and the remaining `rho - 2` must be strictly positive, since `c_0` is
their minimum and `hgapin_0` is vacuous at `c_0 <= 0`.

The linear order in `theta` is MEASURED here rather than assumed: the cluster
displacement from `x_1` and the modulus ratio need not scale alike, so the
exponent is fitted on a ladder before any coefficient is read off it.

mpmath only, 60 digits.  The branch radius is solved from the reality of `z`
and then VALIDATED as the minimum modulus -- the defining property of the branch
and the one a scan for the first sign change gets wrong.  Measured while writing
this: an unanchored scan at `rho = 5` returned `tau = 1.7957` for a branch at
`tau -> 1`, and every coefficient read off it would have been wrong while the
script reported a clean number.
"""
from mpmath import (mp, mpf, mpc, exp, pi, cos, sin, arg, findroot, polyroots,
                    im, re, fabs, log)

mp.dps = 60


def qcoeffs(c, a):
    """Coefficients of Q(t) = c * prod_k (a_k - t), highest degree first."""
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


def angle_sum(a, r, theta, tau):
    """`S(tau) = sum_k arg(a_k - tau e^{i theta}) - r theta`, the angle-sum of
    `Forgacs2017RationalDenominator` Lemma 2(ii).

    Each `a_k - tau e^{i theta}` has negative imaginary part for `tau, theta > 0`,
    so every term sits in `(-pi, 0)` with no branch jump, and each decreases in
    `tau` -- so `S` is strictly decreasing and the branch equation
    `S(tau) = -l pi` has at most one root per index.
    """
    w = mpc(tau) * exp(mpc(0, 1) * theta)
    return sum(arg(mpc(ak) - w) for ak in a) - r * theta


def branch(c, a, r, theta, x1):
    """Branch radius at `theta`, from the MONOTONE angle-sum, then selected by
    the property that defines the branch.

    Bisecting `Im(Q(w)/w^r)` directly does not work and the failure is silent.
    With `Q` carrying a root of multiplicity `rho` at `x_1`, that quantity is
    `O(theta^rho)` near the branch and its two crossings can sit closer together
    than any practical grid step: measured at `Q = (1-t)^3`, `theta = 1e-4`, the
    crossings are `1 +- 5.8e-5` while the sampled values at `1 +- 1e-4` are both
    negative and the value between them is `+1e-12`.  A scan sees no sign change
    at all, and a coarser scan that happens to bracket one root succeeds by grid
    luck rather than by method.

    The angle-sum is the same equation with the cancellation removed: every term
    is `O(1)` and the sum is strictly decreasing, so each admissible index gives
    one root by monotone bisection with no scan.  Candidates are then filtered by
    the branch's defining property -- the principal point must be the
    MINIMUM-modulus root of the pencil that candidate induces, which differs from
    candidate to candidate since each induces its own `z`.
    """
    Q = qcoeffs(c, a)
    lo, hi = mpf(x1) / 1000, mpf(max(a)) * 4
    Slo, Shi = angle_sum(a, r, theta, lo), angle_sum(a, r, theta, hi)
    assert Shi < Slo, "the angle-sum is not decreasing; the branch index is unsafe"
    cands = []
    lmin = int(mp.floor(-Slo / pi)) - 1
    lmax = int(mp.ceil(-Shi / pi)) + 1
    for l in range(lmin, lmax + 1):
        target = -mpf(l) * pi
        if not (Shi < target < Slo):
            continue
        tau = findroot(lambda t: angle_sum(a, r, theta, t) - target, (lo, hi),
                       solver='bisect', tol=mpf(10)**-40)
        cands.append(mpf(re(tau)))
    assert cands, f"no branch index admissible at theta={theta}"
    for tau in sorted(cands):
        w = mpc(tau) * exp(mpc(0, 1) * theta)
        zc = -peval(Q, w) / w**r
        if fabs(im(zc)) > mpf(10)**-25:
            continue
        z = mpf(re(zc))
        rts = polyroots(dcoeffs(Q, z, r), maxsteps=400, extraprec=800)
        if min(fabs(t - w) for t in rts) > mpf(10)**-25:
            continue
        if fabs(fabs(w) - min(fabs(t) for t in rts)) < mpf(10)**-25:
            return tau, z, Q
    raise AssertionError(
        f"no admissible index is the minimum-modulus branch at theta={theta}; "
        f"candidates {[mp.nstr(t, 8) for t in sorted(cands)]}")


def zetas(c, a, r, theta, x1, rho):
    """Sorted `|g_j|/tau - 1` over the rho cluster members nearest `x_1`."""
    tau, z, Q = branch(c, a, r, theta, x1)
    rts = polyroots(dcoeffs(Q, z, r), maxsteps=400, extraprec=800)
    cl = sorted(rts, key=lambda t: fabs(t - x1))[:rho]
    tm = min(fabs(t) for t in cl)
    return sorted(fabs(t) / tm - 1 for t in cl)


def predicted(rho):
    """The closed form at every index, sorted."""
    return sorted((cos(pi / rho) - cos((2 * mpf(j) - 1) * pi / rho)) / sin(pi / rho)
                  for j in range(rho))


PENCILS = [
    # rho, x1, cofactor roots, r, label
    (3, 1.0, [], 1, "Q=(1-t)^3, r=1  (the single pencil already covered)"),
    (3, 1.0, [2.0], 1, "rho=3, cofactor a=2"),
    (4, 1.0, [2.0], 1, "rho=4, cofactor a=2"),
    (5, 1.0, [2.0, 3.0], 1, "rho=5, cofactor a=2,3"),
]

print("lower endpoint gap coefficient, theta -> 0+")
print()

# (1) the order in theta is measured, not assumed
LADDER = [mpf(10)**-3, mpf(10)**-4, mpf(10)**-5]
for rho, x1, cof, r, label in PENCILS:
    a = [x1] * rho + cof
    top = [zetas(1.0, a, r, th, mpf(x1), rho)[-1] for th in LADDER]
    slope = (log(top[0]) - log(top[-1])) / (log(LADDER[0]) - log(LADDER[-1]))
    assert fabs(slope - 1) < mpf(1) / 100, (
        f"{label}: zeta-1 scales as theta^{mp.nstr(slope,6)}, not theta")
    print(f"  {label}: exponent {mp.nstr(slope, 8)}")
print("PASS  |g_j|/tau - 1 is linear in theta at every pencil, fitted over three "
      "decades -- so the paper's theta is the arc parameter itself")
print()

# (2) the coefficients are the closed form, at every pencil
TH = mpf(10)**-6
for rho, x1, cof, r, label in PENCILS:
    a = [x1] * rho + cof
    meas = [v / TH for v in zetas(1.0, a, r, TH, mpf(x1), rho)]
    pred = predicted(rho)
    for m, p in zip(meas, pred):
        assert fabs(m - p) < mpf(1) / 1000, (
            f"{label}: measured {mp.nstr(m,10)} against closed form {mp.nstr(p,10)}")
    print(f"  rho={rho}: " + "  ".join(mp.nstr(v, 8) for v in meas))
print("PASS  every coefficient matches (cos(pi/rho) - cos(clusterAngle rho j))/"
      "sin(pi/rho), across four pencils with three different cofactors")
print()

# (3) exactly two zeros -- the principal pair -- and rho-2 strictly positive
for rho, x1, cof, r, label in PENCILS:
    a = [x1] * rho + cof
    meas = [v / TH for v in zetas(1.0, a, r, TH, mpf(x1), rho)]
    zeros = [m for m in meas if fabs(m) < mpf(1) / 1000]
    pos = [m for m in meas if m > mpf(1) / 1000]
    assert len(zeros) == 2, f"{label}: {len(zeros)} zero coefficients, expected 2"
    assert len(pos) == rho - 2, f"{label}: {len(pos)} positive, expected rho-2"
print("PASS  exactly two coefficients vanish at every pencil -- the principal "
      "pair j = 0, 1 -- and the remaining rho-2 are strictly positive, which is "
      "what makes c_0 > 0 and hgapin_0 non-vacuous")
print()

# (4) the minimum over retained indices is a REAL minimum, which rho=3 cannot show
rho5 = [v / TH for v in zetas(1.0, [1.0] * 5 + [2.0, 3.0], 1, TH, mpf(1.0), 5)]
ret5 = sorted(m for m in rho5 if m > mpf(1) / 1000)
assert len(ret5) == 3, f"rho=5 should retain 3, got {len(ret5)}"
assert ret5[-1] - ret5[0] > mpf(1), (
    "rho=5's retained coefficients are too close together to test a minimum")
rho3 = [v / TH for v in zetas(1.0, [1.0] * 3 + [2.0], 1, TH, mpf(1.0), 3)]
assert len([m for m in rho3 if m > mpf(1) / 1000]) == 1, "rho=3 should retain 1"
print(f"PASS  at rho=5 the retained coefficients are "
      f"{', '.join(mp.nstr(v,7) for v in ret5)} -- spread {mp.nstr(ret5[-1]-ret5[0],6)}, "
      f"so c_0 is a minimum over a genuine SET.  At rho=3 the retained set is a "
      f"singleton, so no single-pencil check can test that minimum")
print()

# (5) teeth: the index convention is pinned.  The upper side's convention
# clusterAngle = 2j pi/rho would put its zeros elsewhere and is distinguishable.
for rho in (3, 4, 5):
    wrong = sorted((cos(pi / rho) - cos(2 * mpf(j) * pi / rho)) / sin(pi / rho)
                   for j in range(rho))
    right = predicted(rho)
    assert max(fabs(w - r_) for w, r_ in zip(wrong, right)) > mpf(1) / 100, (
        f"rho={rho}: the two index conventions are indistinguishable, so this "
        f"check cannot pin the convention")
    nz = len([w for w in wrong if fabs(w) < mpf(1) / 1000])
    assert nz != 2, (
        f"rho={rho}: the wrong convention also gives two zeros, so the zero "
        f"count does not pin the convention")
print("PASS  the upper side's convention clusterAngle = 2j*pi/rho is measurably "
      "different at rho = 3, 4, 5 and does NOT give two vanishing coefficients, "
      "so the measured pair of zeros pins (2j-1)pi/rho rather than merely "
      "agreeing with it")

print()
print("ALL PASS  check_lower_linear_gap")
