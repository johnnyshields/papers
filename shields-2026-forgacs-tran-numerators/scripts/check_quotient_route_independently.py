#!/usr/bin/env python3
r"""Paper section `sec:dominance` (Proof of the main theorem), the lower-endpoint
separation step of `thm:weighted-dominance` at `rho = 1`.

An independent check of the **quotient route**, by a different mechanism from
the one the route itself uses.  The route counts roots with a circular argument
principle; this script counts them by locating them, so a defect in either the
integral or the root-finder cannot hide behind the other.  A check and its
verification must not share a mechanism.

The route, restated so what is being tested is explicit.  With
`F(sigma) = prod_k (1 - v_k sigma) - (1+sigma)^r` and `sum_k v_k = -r`:

  * `sigma = 0` is a root of `F` of order EXACTLY two -- `c_0 = c_1 = 0` from the
    constraint, and `c_2 = (r - p_2)/2 < 0` because `p_2 >= v_0^2 > r^2 >= r`;
  * it is the ONLY root on the circle `|1 + sigma| = 1`;
  * so `Q := F / sigma^2` is zero-free on that circle and the ordinary circular
    argument principle applies with no indentation at all.  The obstruction the
    contour route existed to dodge was the double root sitting ON the contour,
    and dividing by `sigma^2` removes it rather than routing around it.

The count is then pinned by deforming the CONFIGURATION rather than the contour.
`{tail >= 0, sum_k v_k = -r}` is convex, so `v` travels in a straight line to a
reference `v* = (-(r+w), w, 0, ..., 0)`.

  (Q1) The order at the origin is exactly two, over the sweep -- asserted as an
       exact coefficient identity plus `c_2 != 0`, since an order of three would
       leave a root on the circle after dividing by `sigma^2`.

  (Q2) `Q` is zero-free on `|1 + sigma| = 1` at the endpoints AND at every rung
       of the segment.  This is the hypothesis the whole deformation rests on:
       if `Q` acquires a circle zero part-way, the count may jump there and the
       conclusion at the reference says nothing about `v`.

  (Q3) The count at the reference is zero, over `r` up to 12 and `w` across four
       decades -- checked by LOCATING the roots rather than by integrating.

  (Q4) The count is constant along the segment, and equal at both ends.  A
       constant count is what the argument claims; asserting only the endpoints
       would pass on a path that jumped twice.

  (Q5) The conclusion, restated in the paper's own terms and checked directly:
       every root of `F` other than the origin has `|1 + sigma| > 1`.

  (Q6) **The tail must be allowed to vanish, and that relaxation is load-bearing
       rather than convenient.** The reference concentrates the whole tail on one
       index, so every other coordinate is exactly `0`; on a strictly positive
       tail the segment cannot reach it.  Asserted by checking the reference is
       admissible with zeros present and that `v_0 < -r` stays DERIVED there.

mpmath only.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 40


def coeffs(v, r):
    """Ascending coefficients of F(sigma) = prod_k (1 - v_k sigma) - (1+sigma)^r."""
    prod = [mp.mpf(1)]
    for vk in v:
        nxt = [mp.mpf(0)] * (len(prod) + 1)
        for i, c in enumerate(prod):
            nxt[i] += c
            nxt[i + 1] += -vk * c
        prod = nxt
    bi = [mp.binomial(r, i) for i in range(r + 1)]
    deg = max(len(prod), len(bi))
    asc = [mp.mpf(0)] * deg
    for i, c in enumerate(prod):
        asc[i] += c
    for i, c in enumerate(bi):
        asc[i] -= c
    return asc


def quotient(v, r):
    """Ascending coefficients of Q = F / sigma^2, after asserting order exactly 2."""
    asc = coeffs(v, r)
    assert abs(asc[0]) < mp.mpf('1e-30'), asc[0]
    assert abs(asc[1]) < mp.mpf('1e-30'), asc[1]
    assert abs(asc[2]) > mp.mpf('1e-20'), ('order 3 at the origin', asc[2])
    q = asc[2:]
    while len(q) > 1 and abs(q[-1]) < mp.mpf('1e-35'):
        q.pop()
    return q


def q_at(q, s):
    out = mp.mpc(0)
    for c in reversed(q):
        out = out * s + c
    return out


def min_on_circle(q, n=2048):
    """min |Q| over |1 + sigma| = 1, i.e. sigma = e^{i t} - 1."""
    return min(abs(q_at(q, mp.expj(2 * mp.pi * k / n) - 1)) for k in range(n))


def count_in_disc(q):
    """Roots of Q strictly inside |1 + sigma| < 1, located rather than integrated."""
    if len(q) < 2:
        return 0
    rts = mp.polyroots(list(reversed(q)), maxsteps=800, extraprec=400)
    inside = [s for s in rts if abs(1 + s) < 1 - mp.mpf('1e-18')]
    on = [s for s in rts if abs(abs(1 + s) - 1) <= mp.mpf('1e-18')]
    assert not on, ('a root of Q sits on the circle', [mp.nstr(s, 12) for s in on])
    return len(inside)


def ref(r, w, n):
    """v* = (-(r+w), w, 0, ..., 0), with n - 2 vanishing tail coordinates."""
    return [-(mp.mpf(r) + w), w] + [mp.mpf(0)] * (n - 2)


# --- (Q6) the reference is admissible, with a vanishing tail ------------------
for r in (1, 2, 5, 12):
    for w in (mp.mpf('1e-3'), mp.mpf(1), mp.mpf('1e3')):
        v = ref(r, w, 6)
        assert abs(sum(v) + r) < mp.mpf('1e-30')
        assert all(x >= 0 for x in v[1:])
        assert v[0] < -mp.mpf(r)                     # derived, not imposed
        assert sum(1 for x in v[1:] if x == 0) == 4  # the tail really does vanish
print("PASS  (Q6) the reference is admissible with four vanishing tail coordinates, "
      "and v_0 < -r there is still derived from the constraint -- so the relaxation "
      "to a NONNEGATIVE tail is what lets the segment reach it, not a convenience")


# --- (Q1)/(Q3) order two, and count zero at the reference ---------------------
checked = 0
for r in (1, 2, 3, 5, 8, 12):
    for e in (-3, -1, 0, 1, 3):
        w = mp.mpf(10) ** e
        for n in (2, 3, 6):
            v = ref(r, w, n)
            q = quotient(v, r)                       # (Q1) inside
            m = min_on_circle(q)
            assert m > mp.mpf('1e-12'), (r, e, n, mp.nstr(m, 10))
            assert count_in_disc(q) == 0, (r, e, n, count_in_disc(q))
            checked += 1
print(f"PASS  (Q1)(Q3) at all {checked} reference configurations the origin is a root "
      f"of order exactly two, Q is zero-free on the circle, and Q has ZERO roots "
      f"inside it -- counted by locating them, not by integrating")


# --- (Q2)/(Q4) zero-freeness and constancy ALONG the segment ------------------
x = mp.mpf('0.4142135623730950488016887242096980785696')
segments = 0
for trial in range(120):
    x = mp.frac(x * 6364136223846793005 + mp.pi)
    r = 1 + trial % 6
    n = 2 + trial % 5
    tail = []
    for _ in range(n - 1):
        x = mp.frac(x * 6364136223846793005 + mp.pi)
        tail.append(mp.mpf(10) ** (5 * x - 2))
    v = [-mp.mpf(r) - sum(tail)] + tail
    x = mp.frac(x * 6364136223846793005 + mp.pi)
    w = mp.mpf(10) ** (4 * x - 2)
    vs = ref(r, w, n)
    counts, mins = [], []
    for j in range(21):
        t = mp.mpf(j) / 20
        vt = [(1 - t) * a + t * b for a, b in zip(v, vs)]
        assert abs(sum(vt) + r) < mp.mpf('1e-28'), (trial, j)
        assert all(y >= -mp.mpf('1e-30') for y in vt[1:]), (trial, j)
        q = quotient(vt, r)
        mins.append(min_on_circle(q, n=512))
        counts.append(count_in_disc(q))
    assert min(mins) > mp.mpf('1e-14'), (trial, mp.nstr(min(mins), 8))
    assert len(set(counts)) == 1, (trial, counts)
    assert counts[0] == 0, (trial, counts)
    segments += 1
print(f"PASS  (Q2)(Q4) over {segments} straight segments from a random admissible v to "
      f"its reference, Q stays zero-free on the circle at every rung and the interior "
      f"count is CONSTANT at 0 -- asserted rung by rung, since checking only the two "
      f"ends would pass on a path that jumped twice")


# --- (Q5) the conclusion, in the paper's own terms ----------------------------
x = mp.mpf('0.4142135623730950488016887242096980785696')
concl = 0
for trial in range(150):
    x = mp.frac(x * 6364136223846793005 + mp.pi)
    r = 1 + trial % 6
    n = 2 + trial % 5
    tail = []
    for _ in range(n - 1):
        x = mp.frac(x * 6364136223846793005 + mp.pi)
        tail.append(mp.mpf(10) ** (5 * x - 2))
    v = [-mp.mpf(r) - sum(tail)] + tail
    q = quotient(v, r)
    rts = mp.polyroots(list(reversed(q)), maxsteps=800, extraprec=400) if len(q) > 1 else []
    for s in rts:
        assert abs(1 + s) > 1, (trial, mp.nstr(abs(1 + s), 16))
    concl += 1
print(f"PASS  (Q5) on {concl} admissible configurations every root of F other than the "
      f"double root at the origin satisfies |1 + sigma| > 1, which is the separation "
      f"the corner consumes")

print("ALL PASS  check_quotient_route_independently")
