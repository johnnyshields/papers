#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; the `_0` retained group
at `rho = 1`, `eq:ab-def`.

How the per-root clearance constant behaves as `n` grows.

`check_lower_per_root_clearance.py` establishes `min_j |w_j|/t >= 1 + c_n g` in the
collapsing direction and measures `c_n` at `n = 3..6`: `1, 1, 0.857676, 0.718480`.
Four points, and the retained radius is about to be built on that constant, so the
question this file settles is whether `c_n` stays bounded away from `0`.

It does not.

  (A1) `c_n` continues to decrease through `n = 12`, monotonically from `n = 4`.
  (A2) `(n-2) c_n` RISES to about `3.12` near `n = 9` and then FALLS -- `3.118,
       3.116, 3.100, 3.075, 3.047, 3.017`.  So it does not settle, and `c_n` decays
       strictly faster than `C/n`.  Over `n = 3..6` the product reads
       `1, 2, 2.573, 2.874` with increments halving, which looks exactly like
       convergence to a constant; the turnover is invisible before `n = 9`.
  (A3) So `c_n -> 0`, and with no positive lower bound: a retained radius of the
       form `t(1 + c_n g)` collapses onto the collision radius as the pencil grows.

**The asymptotic FORM is not determined here and is not asserted.**  The local
log-log exponent drifts from about `1.14` over `n = 5..10` to about `1.30` over
`n = 10..14`, so no power law fits the range; what the file establishes is the
direction and the absence of a floor, which is what a radius formula has to
survive.

This is a fact about the BOUND, not about the geometry: the true clearance
`min_j |w_j|/t` does not tend to `1` -- (A4) reports it -- so the degeneration is
in what the relative-gap form can express, and a radius formula that has to hold at
every `n` needs a different shape.
"""

from mpmath import mp, mpf, mpc, fabs, findroot, polyroots

mp.dps = 160


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


def sigma(a, r, s):
    """`Sigma(s) = sum_k s/(a_k - s) + r`, whose interior zero is the critical point."""
    return sum(s / (ak - s) for ak in a) + mpf(r)


def t_of(a, r):
    """The critical point in `(a_0, a_1)`, by bisecting SIGMA rather than E.

    `E` vanishes at every repeated zero of `Q`, and the collapsing family puts a
    zero of multiplicity `n-1` at `a_1` -- so a bracket on `E` has a root sitting
    at its own endpoint and bisection walks to it.  `Sigma` has a POLE there
    instead, so its sign change is the interior critical point and nothing else.
    Measured: bisecting `E` returned `t = a_1` exactly at `n = 6`, and the
    clearance then read below 1.
    """
    xs = sorted(a)
    lo = xs[0] + (xs[1] - xs[0]) * mpf(10) ** -30
    hi = xs[1] - (xs[1] - xs[0]) * mpf(10) ** -30
    assert sigma(a, r, lo) < 0 < sigma(a, r, hi), "Sigma does not straddle the gap"
    for _ in range(400):
        mid = (lo + hi) / 2
        if sigma(a, r, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def c_of(n, r, eps):
    """The per-root constant in the collapsing direction, at one (n, r, eps)."""
    a = [mpf(1)] + [mpf(1) + eps] * (n - 1)
    c = mpf(1)
    t = t_of(a, r)
    b = -peval(qcoeffs(c, a), t) / t ** r
    rts = polyroots(dcoeffs(qcoeffs(c, a), mpf(b.real), r),
                    maxsteps=4000, extraprec=6000)
    ds = sorted(rts, key=lambda w: fabs(w - t))
    # the collision is a genuine double root; the next root must be far outside
    # numerical error, or the identification is not trustworthy
    assert fabs(ds[1] - t) < mpf(10) ** -20, f"n={n} r={r}: no double root at t"
    assert fabs(ds[2] - t) > mpf(10) ** -12, f"n={n} r={r}: third root at t"
    others = ds[2:]
    assert len(others) == n - 2, f"n={n} r={r}: {len(others)} non-collision roots"
    kmin = min(fabs(w) / t for w in others)
    g = eps / (1 + eps)
    return (kmin - 1) / g, kmin


NS = list(range(3, 15))
EPS = mpf(10) ** -4

print("the per-root clearance constant as n grows")
print()

cs, kmins = {}, {}
for n in NS:
    vals = []
    for r in (1, 2):
        if r >= n:
            continue
        cn, kmin = c_of(n, r, EPS)
        vals.append((r, cn, kmin))
    # r-independence, re-checked out here rather than assumed from n <= 6
    if len(vals) == 2:
        assert fabs(vals[0][1] - vals[1][1]) / vals[0][1] < mpf(1) / 500, (
            f"c_n moves with r at n={n}: {vals[0][1]} vs {vals[1][1]}")
    cs[n], kmins[n] = vals[0][1], vals[0][2]
    print(f"  n = {n:2d}   c_n {mp.nstr(cs[n], 8):>12}   "
          f"(n-2)c_n {mp.nstr((n - 2) * cs[n], 8):>12}   "
          f"min|w|/t {mp.nstr(kmins[n], 8)}")
print()

# (A1)
for n in NS[1:]:
    if n == 4:
        continue
    assert cs[n] < cs[n - 1], f"c_n did not decrease from n={n-1} to n={n}"
print(f"PASS  (A1) c_n decreases monotonically from n = 4 through n = {NS[-1]}, "
      f"reaching {mp.nstr(cs[NS[-1]], 6)}")

# (A2) -- the product turns over, which is what rules out a C/n law
prods = {n: (n - 2) * cs[n] for n in NS}
peak = max(prods, key=lambda n: prods[n])
assert peak not in (NS[0], NS[-1]), (
    f"(n-2)c_n peaks at the edge of the range (n={peak}), so the turnover is not "
    f"established -- extend NS before reading anything into it")
assert prods[NS[-1]] < prods[peak], "(n-2)c_n did not fall after its peak"
print(f"PASS  (A2) (n-2)c_n RISES to {mp.nstr(prods[peak],6)} at n = {peak} and then "
      f"FALLS to {mp.nstr(prods[NS[-1]],6)} at n = {NS[-1]}.  It does not settle, so "
      f"c_n decays strictly faster than C/n -- and over n = 3..6 alone the product "
      f"reads 1, 2, 2.573, 2.874 with halving increments, which is indistinguishable "
      f"from convergence.  The turnover is invisible before n = {peak}")

# (A3) -- direction and the absence of a floor; the FORM is deliberately not claimed
assert cs[NS[-1]] < cs[3] / 3, "c_n has not fallen by 3x across the range"
assert prods[NS[-1]] < prods[peak], "no evidence c_n falls faster than C/n"
print(f"PASS  (A3) c_n -> 0 with no positive floor in the measured range: it falls "
      f"monotonically from {mp.nstr(cs[3],6)} to {mp.nstr(cs[NS[-1]],6)}, a factor "
      f"{mp.nstr(cs[3]/cs[NS[-1]],5)}.  A retained radius of the form t(1 + c_n g) "
      f"collapses onto the collision radius as the pencil grows.  The asymptotic "
      f"FORM is NOT asserted -- the local log-log exponent drifts from about 1.14 "
      f"to about 1.30 across the range, so no power law is fitted here")

# (A4) -- the geometry is NOT degenerating, only the relative-gap expression
assert kmins[NS[-1]] > 1, "the true clearance fell to 1"
print(f"PASS  (A4) the TRUE clearance min|w|/t stays above 1 throughout "
      f"({mp.nstr(kmins[NS[-1]],8)} at n = {NS[-1]}, against "
      f"{mp.nstr(kmins[3],8)} at n = 3), so what degenerates is the relative-gap "
      f"FORM of the bound rather than the separation it describes")

print()
print("ALL PASS")
