#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `eq:W-endpoint-form`; `subsec:strong-clock`,
`prop:local-strong-clock`.

Extending the phase-derivative bound to the CLOSED arc turns on one question:
does the endpoint limit of `Im(W'/W)` need second-order regularity of the
branch, or is first-order enough?  The answer decides whether the endpoint
package must reach `gamma' in C^{0,1}` or merely produce a bound, and it is a
question about the objects rather than about any Lean statement -- so it is
settled here rather than argued.

Write `gamma(theta) - t_a = theta * u(theta)`, so `W = theta^{-m} V` with `V`
regular.  Then `Im(W'/W)` splits as a first-order part plus `-m * Im(u'/u)`,
and `u'` is second order in `gamma` -- `u' = (gamma' theta - (gamma - t_a))/theta^2`
needs `gamma' theta - (gamma - t_a) = O(theta^2)`.

At `Q = (1-t)^3`, `r = 1`, where `t_a = x_1 = 1` and `m = 2`:

  (P1) `Im(u'/u) -> 1/3`, flat across five decades rather than drifting.
  (P2) `m * Im(u'/u) = 2/3`, which is exactly the gap between the measured
       limit `7/6` and the value `11/6` a first-order-only computation gives.
       So the LIMIT is not determined by `gamma'(0)` and the pencil.
  (P3) But a BOUND is: `(gamma' theta - (gamma - t_a))/theta^2` stays bounded
       on `(0, b]`, which is what `gamma'` Lipschitz would give and is all the
       `_of_bound` form of the phase-derivative lemma asks for.
  (P4) Teeth: the two quantities are genuinely different -- the limit is
       approached while the bound is attained -- so a check that conflated them
       would not distinguish first- from second-order data.

`mpmath` throughout: `u'` is a difference of two `O(theta)` quantities divided
by `theta^2`, so at `theta = 1e-6` it is a cancellation of twelve digits.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 60
I = mp.mpc(0, 1)
TA = mp.mpf(1)
M_ORDER = 2


def tau(t):
    return 1 / (2 * mp.cos((mp.pi - t) / 3))


def gam(t):
    return tau(t) * mp.exp(I * t)


def u(t):
    return (gam(t) - TA) / t


def du(t):
    return mp.diff(u, t)


# ---------------------------------------------------------------------------
# (P1) Im(u'/u) -> 1/3, flat
# ---------------------------------------------------------------------------
vals = [mp.im(du(mp.mpf(10) ** (-k)) / u(mp.mpf(10) ** (-k))) for k in (2, 3, 4, 5, 6)]
spread = max(vals) - min(vals)
assert spread < mp.mpf(10) ** (-8), f"Im(u'/u) drifts: {[mp.nstr(v,8) for v in vals]}"
assert abs(vals[-1] - mp.mpf(1) / 3) < mp.mpf(10) ** (-6), \
    f"Im(u'/u) is not 1/3: {mp.nstr(vals[-1], 12)}"
print(f"PASS  (P1) Im(u'/u) = {mp.nstr(vals[-1], 12)} = 1/3, flat over five decades "
      f"(spread {mp.nstr(spread, 4)})")

# ---------------------------------------------------------------------------
# (P2) the gap is exactly m * Im(u'/u)
# ---------------------------------------------------------------------------
gap = mp.mpf(11) / 6 - mp.mpf(7) / 6
assert abs(M_ORDER * vals[-1] - gap) < mp.mpf(10) ** (-6), \
    f"m*Im(u'/u) = {mp.nstr(M_ORDER*vals[-1],10)} does not match 11/6 - 7/6 = {mp.nstr(gap,10)}"
print(f"PASS  (P2) m*Im(u'/u) = {mp.nstr(M_ORDER * vals[-1], 10)} = 11/6 - 7/6, so the "
      f"endpoint LIMIT is not determined by gamma'(0) and the pencil")

# ---------------------------------------------------------------------------
# (P3) but the bound is first-order
# ---------------------------------------------------------------------------
def defect(t):
    return abs(mp.diff(gam, t) * t - (gam(t) - TA)) / t ** 2


ds = [defect(mp.mpf(10) ** (-k)) for k in (2, 3, 4, 5, 6)]
assert max(ds) < 10, f"(gamma' t - (gamma - t_a))/t^2 is unbounded: {[mp.nstr(v,6) for v in ds]}"
assert max(ds) - min(ds) < 1, f"it is not settling: {[mp.nstr(v,6) for v in ds]}"
print(f"PASS  (P3) |gamma' t - (gamma - t_a)|/t^2 stays at {mp.nstr(ds[-1], 8)} on (0,b], "
      f"which is what gamma' Lipschitz gives and all the `_of_bound` form needs")

# ---------------------------------------------------------------------------
# (P4) teeth -- limit and bound are different quantities
# ---------------------------------------------------------------------------
assert abs(vals[-1] - ds[-1]) > mp.mpf(1) / 10, (
    f"the limit {mp.nstr(vals[-1],8)} and the bound {mp.nstr(ds[-1],8)} are too close "
    "for this check to distinguish first- from second-order data")
print(f"PASS  (P4) the limit ({mp.nstr(vals[-1], 6)}) and the bound "
      f"({mp.nstr(ds[-1], 6)}) are distinct quantities, so the check separates "
      f"what needs second-order data from what does not")

print("ALL PASS  check_endpoint_phase_order")
