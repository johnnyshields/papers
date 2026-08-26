#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `lem:amplitude-divisor`,
`eq:ab-def`.

`hamp_1`'s exponent at the upper endpoint, at `r = 1`.

`check_upper_amplitude_floor.py` measures that exponent at `r = 2, 3, 4` and
finds `p_1 = 1`: there `tau -> 0`, the cofactor `D'(t_+)` blows up, and the
principal amplitude vanishes linearly, so the floor is `A_1 * eta`.  It does not
cover `r = 1`, and `r = 1` is a DIFFERENT REGIME rather than the same one at a
smaller index.

At `r = 1` the arc ends at `theta = pi` with `tau -> L > 0`: the principal root
and its conjugate both run to the same point `-L` on the negative real axis, so
`-L` is a DOUBLE root of `D` in the limit and `D'(-L) = 0`.  Since
`ftAmp = -B(tau)/D'(tau)` is a residue, the amplitude does not vanish there --
it BLOWS UP.  So the exponent is negative, and a floor at exponent `1` would be
the wrong statement rather than a weaker one.

  (P1) At `r = 1` the measured exponent of `|W(pi - eta)|` is `-1`, fitted on a
       log-log ladder, at every pencil.
  (P2) The `r >= 2` side is not re-measured: `check_upper_amplitude_floor.py`
       already reports `p1 = 1` there, and duplicating a green measurement is how
       two scripts drift into disagreeing about one fact.
  (P3) The mechanism: `|D'(t_+)| -> 0` at `r = 1`.  `ftAmp` is a residue, so a
       vanishing denominator is what sends the amplitude UP rather than down.
  (P4) A floor is therefore EASIER at `r = 1`, not harder: `|W|` is eventually
       bounded below by any constant.  Asserted, so that a later pass does not
       import the `r >= 2` shape by symmetry.

mpmath only, 50 digits.  The branch comes from the MONOTONE angle-sum of
`Forgacs2017RationalDenominator` Lemma 2(ii), never from bisecting
`Im(Q(w)/w^r)`, whose crossings can sit closer together than any practical grid
near a multiple zero.
"""
from mpmath import mp, mpf, mpc, exp, pi, arg, findroot, polyroots, im, re, fabs, log

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
    # the floor must sit BELOW tau, and at r >= 2 the upper-endpoint tau
    # collapses -- 5.7e-5 at eta = 1e-3 on these pencils -- so a floor scaled
    # to min(a) misses the branch entirely and the search reports none.
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


def amp_and_cofactor(c, a, r, theta):
    """(|W|, |D'(t_+)|) at the branch point of angle `theta`, with B = 1."""
    tau, z, Q = branch(c, a, r, theta)
    w = mpc(tau) * exp(mpc(0, 1) * theta)
    D = dcoeffs(Q, z, r)
    dp = peval(deriv(D), w)
    return fabs(mpc(1) / dp), fabs(dp)


def exponent(c, a, r, etas):
    """Log-log slope of |W| against eta, where theta = pi/r - eta."""
    vals = [amp_and_cofactor(c, a, r, pi / r - e)[0] for e in etas]
    return (log(vals[0]) - log(vals[-1])) / (log(etas[0]) - log(etas[-1])), vals


ETAS = [mpf(10)**-3, mpf(10)**-4, mpf(10)**-5]
ONE = [([1.0, 1.0, 2.0], 1.0, "a=(1,1,2) rho=2"),
       ([1.0, 1.0, 1.0, 2.0], 1.0, "a=(1,1,1,2) rho=3"),
       ([0.4, 0.4, 1.7], 2.5, "a=(0.4,0.4,1.7) rho=2, c=2.5")]


print("upper endpoint amplitude exponent, r = 1 against r >= 2")
print()

p_one = []
for a, c, lab in ONE:
    p, vals = exponent(c, a, 1, ETAS)
    _, dp = amp_and_cofactor(c, a, 1, pi - ETAS[-1])
    p_one.append((lab, p, dp))
    print(f"  r=1  {lab}: exponent {mp.nstr(p,8)}   |W| "
          f"{'  '.join(mp.nstr(v,6) for v in vals)}   |D'| at eta=1e-5 {mp.nstr(dp,6)}")
print()

# (P1) r = 1 gives -1
for lab, p, _ in p_one:
    assert fabs(p + 1) < mpf(1) / 50, (
        f"{lab}: r = 1 exponent {mp.nstr(p,8)}, expected -1 -- the principal root "
        f"collides with its conjugate at -L, so the residue blows up")
print(f"PASS  at r = 1 the amplitude exponent is -1 at all {len(p_one)} pencils: "
      f"|W| BLOWS UP at the upper endpoint")

# (P2) the r >= 2 side is NOT re-measured here: `check_upper_amplitude_floor.py`
# already reports `p1=1` at r = 2, 3, 4 on four pencils, and duplicating a green
# measurement is how two scripts drift into disagreeing about one fact.
print("INFO  the r >= 2 exponent is +1, measured by check_upper_amplitude_floor.py "
      "and not repeated here")

# (P3) the mechanism is the cofactor vanishing
for lab, _, dp in p_one:
    assert dp < mpf(1) / 100, f"{lab}: |D'| = {mp.nstr(dp,6)} is not vanishing at r = 1"
print("PASS  the mechanism is the cofactor: |D'(t_+)| vanishes at r = 1 -- the "
      "principal root and its conjugate collide at -L, so -L is a double root of "
      "D in the limit -- and ftAmp is a residue, so a vanishing denominator is "
      "what sends the amplitude UP rather than down")

# (P4) a floor is easier at r = 1
for lab, _, _ in p_one:
    a, c = next((a, c) for a, c, l in ONE if l == lab)
    vals = [amp_and_cofactor(c, a, 1, pi - e)[0] for e in ETAS]
    assert vals[-1] > vals[0] > 1, f"{lab}: |W| is not growing past 1"
print("PASS  so hamp_1 is EASIER at r = 1, not harder -- |W| is eventually above "
      "any constant, and a floor at exponent 1 would be the wrong statement "
      "rather than a weaker one")

print()
print("ALL PASS  check_upper_amplitude_r_one")
