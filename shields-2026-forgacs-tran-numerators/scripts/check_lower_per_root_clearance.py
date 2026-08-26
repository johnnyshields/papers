r"""Paper section `sec:dominance` (The weighted dominance bound).

Whether the lower endpoint admits a PER-ROOT clearance bound, which is what
the retained-set group needs and what the product bound cannot supply.

`EndpointCollision.clearance_ge_relative_gap_of_r` bounds
`\prod_k a_k / t^n - 1`, the product of all non-collision roots' clearances.
The retained group consumes a bound on the SMALLEST of them.  At `n = 3` the
two coincide -- the collision eats `t^2` and exactly one root is left -- which
is why the three-term statement reads as either.  From `n = 4` they come
apart, so widening the product bound does not feed the radius.

What the radius needs is the lower-endpoint analogue of
`two_mul_lt_norm_of_root_endpoint_pi`, and the first question is whether one
exists at all: at the upper endpoint the answer is a fixed factor `2`, while
here the clearance infimum is `1`, unattained.  So a fixed factor is
unavailable and the only candidate shape is relative-gap: with
`g = (a_1 - a_0)/a_1`,

    min_j |w_j| / t  \ge  1 + c_n g .

Two things are measured:

  (i)   `c_n` exists and is positive, is independent of `r`, and DECREASES
        with `n` -- `c_3 = c_4 = 1`, `c_5 \approx 0.8577`, `c_6 \approx 0.7185`;
  (ii)  the infimum sits in the COLLAPSING direction, the whole tail closing
        onto the smallest zero together, and every other direction sampled
        stays above `1.5`.

(ii) is the part that makes (i) worth anything.  Three separate margins
reported tonight belonged to the family that produced them rather than to the
mathematics, each time because the tight direction was absent; the collapsing
direction is where this one lives, and it is asserted rather than sampled.

The non-collision roots are obtained from `g(w) = g(t)` cleared of
denominators -- `-Q(w)t^r + Q(t)w^r = 0` -- and the double root at `t` is
removed by ordering on distance and dropping two, never by dividing.

mpmath only.
"""

from mpmath import mp, mpf, mpc, fabs, polyroots

mp.dps = 50
ZERO = mpf(10) ** -35


def sigma(a, r, s):
    return sum(s / (ak - s) for ak in a) + r


def t_of(a, r):
    xs = sorted(set(a))
    if len(xs) < 2:
        return None
    lo = xs[0] + (xs[1] - xs[0]) * mpf(10) ** -30
    hi = xs[1] - (xs[1] - xs[0]) * mpf(10) ** -30
    if not (sigma(a, r, lo) < 0 < sigma(a, r, hi)):
        return None
    for _ in range(400):
        mid = (lo + hi) / 2
        if sigma(a, r, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def q_coeffs(a):
    p = [mpf(1)]
    for ak in a:
        q = [mpf(0)] * (len(p) + 1)
        for i, c in enumerate(p):
            q[i] += ak * c
            q[i + 1] += -c
        p = q
    return p


def other_roots(a, r, t):
    """Roots of g(w) = g(t) with the double root at t dropped."""
    p = [-c * t ** r for c in q_coeffs(a)]
    qt = mpf(1)
    for ak in a:
        qt *= (ak - t)
    while len(p) <= r + len(a):
        p.append(mpf(0))
    p[r] += qt
    while len(p) > 1 and fabs(p[-1]) < ZERO:
        p.pop()
    rts = sorted(polyroots(list(reversed(p)), maxsteps=400, extraprec=400),
                 key=lambda z: fabs(mpc(z) - t))
    return rts[2:]


def min_clearance(a, r):
    t = t_of(a, r)
    if t is None:
        return None, None
    rs = other_roots(a, r, t)
    if not rs:
        return None, None
    xs = sorted(a)
    return min(fabs(mpc(z)) / t for z in rs), (xs[1] - xs[0]) / xs[1]


EXPECTED = {3: mpf(1), 4: mpf(1), 5: mpf("0.857676"), 6: mpf("0.71848")}

print("PASS  (i) the per-root constant in the collapsing direction:")
for n in (3, 4, 5, 6):
    vals = []
    for r in (1, 2):
        if r >= n:
            continue
        eps = mpf(10) ** -5
        a = [mpf(1)] + [mpf(1) + eps] * (n - 1)
        m, g = min_clearance(a, r)
        assert m is not None, f"no roots at n={n}, r={r}"
        c = (m - 1) / g
        assert c > 0, f"the per-root constant is {c} <= 0 at n={n}, r={r}"
        rel = fabs(c - EXPECTED[n]) / EXPECTED[n]
        assert rel < mpf(1) / 500, (
            f"c_{n} at r={r} is {c}, expected {EXPECTED[n]}")
        vals.append(c)
    assert len(vals) >= 1
    if len(vals) == 2:
        assert fabs(vals[0] - vals[1]) / vals[0] < mpf(1) / 500, (
            f"the constant moves with r at n={n}: {vals}")
    print(f"        n = {n}:  c_n = {mp.nstr(vals[0], 8)}"
          f"{'  (same at r = 1 and 2)' if len(vals) == 2 else ''}")

assert EXPECTED[3] == EXPECTED[4] and EXPECTED[5] < EXPECTED[4] and EXPECTED[6] < EXPECTED[5]
print("PASS  (i) c_n is positive and independent of r, so a per-root "
      "relative-gap bound EXISTS -- but it DECREASES with n (1, 1, 0.858, "
      "0.718), so a radius built from it weakens as the pencil grows, unlike "
      "the fixed factor 2 the upper endpoint gets")

print("PASS  (ii) the infimum is in the collapsing direction, not elsewhere:")
best = mpf("inf")
at = None
count = 0
for n in (3, 4, 5, 6):
    for r in (1, 2):
        if r >= n:
            continue
        pts = []
        for k in range(1, 7):
            e = mpf(10) ** (-mpf(k) / 2)
            pts.append([mpf(1), mpf(1) + e] + [mpf(2) + mpf(j) for j in range(n - 2)])
            pts.append([mpf(1)] + [mpf(1) + e * mpf(j + 1) for j in range(n - 1)])
            pts.append([e] + [mpf(1) + mpf(j) for j in range(n - 1)])
        for s in range(1, 12):
            pts.append(sorted(mpf(1) + mpf((s * 7 * (j + 3)) % 13) / 10
                              for j in range(n)))
        for a in pts:
            if len(set(a)) < 2:
                continue
            m, g = min_clearance(a, r)
            if m is None or g < mpf(10) ** -8:
                continue
            count += 1
            c = (m - 1) / g
            if c < best:
                best, at = c, (n, r, [mp.nstr(x, 4) for x in a])
assert best > mpf(3) / 2, (
    f"a non-collapsing direction reaches {best} at {at} -- below the "
    f"collapsing constants, so the infimum is not where this claims")
print(f"        {count} configurations off the collapsing direction; lowest "
      f"{mp.nstr(best, 6)} at {at}")
print(f"PASS  (ii) every other direction stays above 1.5, well clear of the "
      f"collapsing constants -- so c_n is the infimum and not an artifact of "
      f"which family was sampled")
# --- (iii) c_n has NO positive floor, and n = 3..6 cannot see that ---------
# The window above stops at n = 6, where c_n reads 1, 1, 0.858, 0.719 and
# (n-2)c_n reads 1, 2, 2.573, 2.874 with increments halving -- indistinguishable
# from convergence to a constant, which is what a first pass over that window
# concluded.  Continuing to n = 15 shows the product PEAKS and turns:
#
#   n         3      4      5      6      7      8      9     10     12     15
#   (n-2)c_n  1.000  2.000  2.573  2.874  3.025  3.094  3.118  3.116  3.075  2.987
#
# So c_n decays strictly faster than C/n and has no positive floor, and a
# radius t(1 + c_n g) collapses onto the collision radius as the pencil grows.
# No form is asserted: the local log-log exponent drifts, so no power law fits.
# What is asserted is the direction, the turnover, and the absence of a floor.
mp.dps = 160
prod = {}
clear = {}
for n in range(3, 16):
    eps = mpf(10) ** -4
    a = [mpf(1)] + [mpf(1) + eps] * (n - 1)
    t = t_of(a, 1)
    assert t is not None, f"no bracket at n={n}"
    # the bracket must be on Sigma, never on E: in this family the tail sits at
    # a_1 with multiplicity n-1, so E VANISHES at a_1 and a bisection on E walks
    # to its own endpoint and returns t = a_1 exactly.  Sigma has a pole there.
    assert t < a[1], f"t reached the endpoint at n={n} -- bisected the wrong function"
    rs = other_roots(a, 1, t)
    assert rs, f"no non-collision roots at n={n}"
    mn = min(fabs(mpc(z)) / t for z in rs)
    assert mn > 1, f"the true clearance dropped to {mn} at n={n}"
    g = eps / (1 + eps)
    clear[n] = mn
    prod[n] = (n - 2) * (mn - 1) / g

peak = max(prod, key=lambda k: prod[k])
assert peak == 9, f"(n-2)c_n peaks at n={peak}, expected 9"
assert prod[15] < prod[9], "the product does not turn over"
assert prod[15] < prod[8], "the fall does not reach below the pre-peak values"
print(f"PASS  (iii) (n-2)c_n rises to {mp.nstr(prod[9], 7)} at n = 9 and then "
      f"FALLS -- {mp.nstr(prod[12], 7)} at n = 12, {mp.nstr(prod[15], 7)} at "
      f"n = 15.  So c_n decays strictly faster than C/n and has no positive "
      f"floor")
print(f"PASS  (iii) but the true clearance min_j|w_j|/t stays above 1 "
      f"throughout ({mp.nstr(clear[15], 10)} at n = 15), so what degenerates "
      f"is the RELATIVE-GAP FORM and not the separation it describes -- a "
      f"retained radius must be n-dependent by construction, or expressed in "
      f"something other than g")
print("PASS  (iii) and n = 3..6 cannot see this: over that window the product "
      "reads 1, 2, 2.573, 2.874 with increments halving, which is exactly what "
      "convergence to a constant looks like")

print("ALL PASS")
