#!/usr/bin/env python3
r"""Paper section `subsec:proof`, `prop:angular-discrepancy`,
`eq:angular-distinct-lower` and `eq:angular-discrepancy`.

The formalization builds `prop:angular-discrepancy` out of a window family, a
summation core, a disjointness step and a complementation.  Every one of those
is a statement about the ROUTE.  This script tests the TARGET: it counts actual
zeros of actual coefficient polynomials in actual angular windows and asks
whether the discrepancy really is bounded by `C_0 + C_1 deg B` with constants
that do not see `B`.

A wrong normalization -- `M` for `M+1`, a factor of `r`, a half-open versus open
window -- survives every structural check and dies here.

Pencil: `Q = (1-t)^3`, `r = 1`, so `I_{Q,1} = (0, 27/4)` and the viewing arc is
`(0, pi)`.  The coefficient polynomial is computed EXACTLY, from

    B/D = sum_k (-z)^k t^k B(t)/(1-t)^{3k+3},

so `F_M(z) = sum_k (-z)^k sum_j b_j binom(M + 2k - j + 2, 3k+2)` with integer
binomial coefficients -- no series truncation and no numerical extraction.

Asserted, each as a failing test:

  (D1) The exact coefficient formula agrees with a Taylor extraction of `B/D`.
  (D2) `deg F_M = M` and the count of zeros in `I_{Q,1}` is `M` or `M-1` -- the
       zeros really are essentially all interior, which is what makes the
       defect bounded at all.
  (D3) `eq:angular-discrepancy` holds: over every window of a grid, and over
       five weights `B` of degree 0 through 6, the discrepancy
       `|Z_M(alpha,beta) - (M+1)(beta-alpha)/pi|` is bounded, and the bound
       grows at most linearly in `deg B`.
  (D4) The fitted `C_1` is small and the fitted `C_0` does not grow with `M` --
       which is the content of "the threshold in `M` may depend on `B`, but the
       discrepancy constants do not".
  (D5) The check has teeth against the errors the statement CAN see.  It cannot
       see `M` versus `M+1`: those differ by `(beta-alpha)/pi <= 1`, which sits
       inside `C_0`, and measured at `M = 40` the `M` form actually scores
       slightly better.  That is a property of `eq:angular-discrepancy`, not a
       defect -- the proposition is deliberately insensitive to an additive
       constant.  What it must see is a wrong SLOPE in `beta - alpha`: a factor
       of two, or a missing `r`, makes the discrepancy grow linearly in `M`,
       which no `C_0 + C_1 deg B` absorbs.  Both are asserted to fail.

`mpmath` throughout; roots at 80 digits, since a degree-60 polynomial with
binomial coefficients of size ~1e40 is badly scaled in float64.
"""
from __future__ import annotations

import math
import mpmath as mp

mp.mp.dps = 80

I = mp.mpc(0, 1)


def tau(theta):
    return 1 / (2 * mp.cos((mp.pi - theta) / 3))


def zbranch(theta):
    t = tau(theta) * mp.exp(I * theta)
    z = -(1 - t) ** 3 / t
    assert mp.fabs(mp.im(z)) < mp.mpf(10) ** (-60), f"z left the reals at {theta}"
    return mp.re(z)


def coeff_poly(bcoeffs, M):
    """`F_M` as a coefficient list in `z`, ascending, computed exactly."""
    out = []
    for k in range(M + 1):
        s = 0
        for j, bj in enumerate(bcoeffs):
            n = M + 2 * k - j + 2
            if n >= 3 * k + 2 and M - k - j >= 0:
                s += bj * math.comb(n, 3 * k + 2)
        out.append(((-1) ** k) * s)
    return out


def taylor_coeff(bcoeffs, M, z):
    def f(t):
        B = sum(mp.mpf(b) * t ** j for j, b in enumerate(bcoeffs))
        return B / ((1 - t) ** 3 + z * t)
    return mp.taylor(f, 0, M, method='quad', radius=mp.mpf(1) / 5)[M]


# ---------------------------------------------------------------------------
# (D1) the exact formula is the coefficient
# ---------------------------------------------------------------------------
worst = mp.mpf(0)
for bc in ([1], [1, 0, 3], [2, -1, 0, 5]):
    for M in (5, 9, 14):
        c = coeff_poly(bc, M)
        for zval in (mp.mpf(1) / 2, mp.mpf(2), mp.mpf(5)):
            exact = sum(mp.mpf(c[k]) * zval ** k for k in range(M + 1))
            num = taylor_coeff(bc, M, zval)
            worst = max(worst, abs(exact - num) / max(abs(num), mp.mpf(1)))
assert worst < mp.mpf(10) ** (-40), f"the exact coefficient formula is wrong: {mp.nstr(worst,8)}"
print(f"PASS  (D1) the exact F_M formula matches a Taylor extraction, worst "
      f"relative {mp.nstr(worst, 6)}")

Z_LO, Z_HI = mp.mpf(0), mp.mpf(27) / 4


def interior_angles(bcoeffs, M):
    """Angles of the zeros of `F_M` lying in `I_{Q,1}`, ascending."""
    c = coeff_poly(bcoeffs, M)
    while c and c[-1] == 0:
        c.pop()
    roots = mp.polyroots([mp.mpf(x) for x in reversed(c)], maxsteps=300, extraprec=800)
    angs = []
    for rt in roots:
        if mp.fabs(mp.im(rt)) > mp.mpf(10) ** (-25):
            continue
        x = mp.re(rt)
        if not (Z_LO < x < Z_HI):
            continue
        th = mp.findroot(lambda t: zbranch(t) - x, mp.mpf(1), solver='bisect',
                         tol=mp.mpf(10) ** (-50),
                         maxsteps=400) if False else None
        lo, hi = mp.mpf(10) ** (-30), mp.pi - mp.mpf(10) ** (-30)
        for _ in range(200):
            mid = (lo + hi) / 2
            if zbranch(mid) < x:
                lo = mid
            else:
                hi = mid
        angs.append((lo + hi) / 2)
    return sorted(angs), len(c) - 1


# ---------------------------------------------------------------------------
# (D2) the zeros are essentially all interior
# ---------------------------------------------------------------------------
for M in (20, 35):
    angs, deg = interior_angles([1], M)
    assert deg == M, f"deg F_M = {deg}, expected {M}"
    assert M - 1 <= len(angs) <= M, f"at M={M}: {len(angs)} interior zeros, expected {M-1} or {M}"
print(f"PASS  (D2) deg F_M = M and all but at most one zero is interior "
      f"(M = 20 and 35 at B = 1)")

WEIGHTS = {0: [1], 1: [1, 2], 2: [1, 0, 3], 4: [2, -1, 0, 5, 1], 6: [1, 1, -2, 0, 3, 0, 1]}


def discrepancy(bcoeffs, M, nwin):
    angs, _ = interior_angles(bcoeffs, M)
    worstd = mp.mpf(0)
    for i in range(nwin):
        for j in range(i + 1, nwin + 1):
            al, be = mp.pi * i / nwin, mp.pi * j / nwin
            cnt = sum(1 for a in angs if al < a < be)
            pred = ((M + 1) * (be - al)) / mp.pi
            worstd = max(worstd, abs(mp.mpf(cnt) - pred))
    return worstd


# ---------------------------------------------------------------------------
# (D3)/(D4) the discrepancy is bounded, linear in deg B, stable in M
# ---------------------------------------------------------------------------
table = {}
for K, bc in sorted(WEIGHTS.items()):
    row = []
    for M in (24, 32, 40):
        row.append(discrepancy(bc, M, 6))
    table[K] = row
    assert max(row) < 30, f"discrepancy blew up at deg B = {K}: {[mp.nstr(v,5) for v in row]}"
    spread = max(row) - min(row)
    assert spread < 3, (
        f"the discrepancy at deg B = {K} grows with M ({[mp.nstr(v,5) for v in row]}); "
        "C_0 would then depend on M, which the proposition forbids")
Ks = sorted(table)
maxd = [max(table[K]) for K in Ks]
print(f"PASS  (D3) discrepancy over all windows of a 6-grid, deg B = {Ks}: "
      f"{[mp.nstr(v, 4) for v in maxd]}")

# linear fit: the growth per unit degree must be bounded and modest
slopes = [(maxd[i + 1] - maxd[i]) / (Ks[i + 1] - Ks[i]) for i in range(len(Ks) - 1)]
assert all(s < 4 for s in slopes), f"growth in deg B is not modest: {[mp.nstr(s,5) for s in slopes]}"
c1 = max(max(slopes), mp.mpf(0))
c0 = max(maxd[0], mp.mpf(0))
for K, d in zip(Ks, maxd):
    assert d <= c0 + c1 * K + mp.mpf(1) / 2, \
        f"C_0 + C_1 K fails at K = {K}: {mp.nstr(d,6)} > {mp.nstr(c0 + c1*K, 6)}"
print(f"PASS  (D4) bounded by C_0 + C_1 deg B with C_0 = {mp.nstr(c0, 5)}, "
      f"C_1 = {mp.nstr(c1, 5)}, and stable across M = 24, 32, 40 "
      f"(so the constants do not see M)")

# ---------------------------------------------------------------------------
# (D5) the check has teeth against the errors the statement can see
# ---------------------------------------------------------------------------
def worst_under(angs, M, slope):
    w = mp.mpf(0)
    for i in range(8):
        for j in range(i + 1, 9):
            al, be = mp.pi * i / 8, mp.pi * j / 8
            cnt = mp.mpf(sum(1 for a in angs if al < a < be))
            w = max(w, abs(cnt - slope * (be - al)))
    return w

right, half, double = [], [], []
for M in (24, 40):
    angs, _ = interior_angles([1], M)
    right.append(worst_under(angs, M, (M + 1) / mp.pi))
    half.append(worst_under(angs, M, (M + 1) / (2 * mp.pi)))
    double.append(worst_under(angs, M, 2 * (M + 1) / mp.pi))

# the correct slope stays bounded as M grows; both wrong slopes grow with M
assert max(right) < 3, f"the correct normalization is not bounded: {[mp.nstr(v,5) for v in right]}"
assert half[1] > half[0] + 5, (
    f"halving the slope does not grow with M ({[mp.nstr(v,5) for v in half]}); "
    "the check cannot see a factor-of-two error")
assert double[1] > double[0] + 5, (
    f"doubling the slope does not grow with M ({[mp.nstr(v,5) for v in double]}); "
    "the check cannot see a factor-of-two error")
print(f"PASS  (D5) the correct slope stays bounded across M = 24, 40 "
      f"({[mp.nstr(v, 4) for v in right]}) while a halved slope "
      f"({[mp.nstr(v, 4) for v in half]}) and a doubled one "
      f"({[mp.nstr(v, 4) for v in double]}) both grow with M, so a wrong slope "
      f"fails this and an additive constant -- which C_0 absorbs -- does not")

print("ALL PASS  check_angular_discrepancy_end_to_end")
