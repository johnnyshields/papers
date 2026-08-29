#!/usr/bin/env python3
r"""Paper section `cor:linear-phase-variation`, `eq:linear-phase-variation`,
`eq:viewing-angle-bound`.

The root-state group of the branch supply asks, for each zero `beta` of `B`, that the
tangency set `{x : arg(gamma') - arg(gamma - beta) in pi*Z}` be exhibited as a finite
set.  At the Favard pencil `Q = 1 - 4t + t^2`, `r = 1`, `B = t^2 + 1`, `tau = 1` the
branch is the unit semicircle `gamma = e^{i theta}` and the two roots of `B` are `+i`
and `-i`, both ON that circle.  This script pins the closed forms the Lean proof rests
on, BEFORE it asserts them.

Asserted, each as a failing test:

  (F1) Both roots lie on the unit circle; the arc `[0, pi]` meets `+i` exactly at
       `pi/2` and misses `-i` entirely.  That is the two-disjunct split the root state
       is written around, and it is what makes this pencil the favourable one.
  (F2) Both rates are CONSTANT: `Im(gamma''/gamma') = 1` and `Im(gamma'/(gamma -+ i))
       = 1/2`, the second being the inscribed-angle theorem -- a chord from a point of
       a circle turns at half the rate of the tangent.  Constant rates are why the
       tangency set is computable here rather than merely finite.
  (F3) The four branches equal their closed forms, against numerically integrated
       `polarAngle`:  `pi/2 + x` for the tangent, `pi/4 + x/2` and `-pi/4 + x/2` and
       `-3pi/4 + (x-pi)/2` for the three chords.
  (F4) The three differences run strictly between consecutive multiples of `pi`:
       `(0, pi)` at `-i`, `(3pi/4, pi)` below the collision, `(2pi, 9pi/4)` above it.
       So every tangency set is EMPTY.
  (F5) The bound is attained only in the limit at `pi/2`: the lower difference tends
       to `pi` and the upper one to `2pi` as `x -> pi/2`.  Without this the emptiness
       would look like slack, when in fact it is exactly the collision being excluded
       -- and a check asserting only "no multiple of pi is hit" would pass equally on
       a pencil where the sets were empty for a weaker reason.
  (F6) The amplitude vanishes at `pi/2` and nowhere else on the open arc, which is
       what forces each nondegenerate block onto one side of the collision.

`mpmath` at 40 digits; the `polarAngle` integrals in (F3) are compared to 1e-25.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 40

I = mp.mpc(0, 1)
PI = mp.pi

gam = lambda x: mp.e ** (I * x)
dgam = lambda x: mp.e ** (I * x) * I
d2gam = lambda x: mp.e ** (I * x) * I * I


def polarAngle(G, dG, beta, base, s):
    """`log(G(base) - beta) + int_base^s dG/(G - beta)`, imaginary part."""
    f = lambda u: (dG(u) / (G(u) - beta)).imag
    return mp.log(G(base) - beta).imag + mp.quad(f, [base, s])


def report(name, ok, detail):
    print(f"  {'PASS' if ok else 'FAIL'}  {name}: {detail}")
    assert ok, f"{name} failed: {detail}"


print("check_favard_root_states")
print()

# --------------------------------------------------------------- (F1) geometry
onI = abs(abs(I) - 1)
onnegI = abs(abs(-I) - 1)
meet = abs(gam(PI / 2) - I)
miss = min(abs(gam(x) - (-I)) for x in [mp.mpf(k) * PI / 200 for k in range(201)])
report("F1", onI < mp.mpf('1e-30') and onnegI < mp.mpf('1e-30')
       and meet < mp.mpf('1e-30') and miss > mp.mpf('0.9'),
       f"both roots on the circle; gamma(pi/2) = i to {mp.nstr(meet, 3)}, and "
       f"min|gamma - (-i)| = {mp.nstr(miss, 6)} over the arc")

# ------------------------------------------------------------------ (F2) rates
xs = [mp.mpf(k) * PI / 17 for k in range(1, 17)]
r_t = max(abs((d2gam(x) / dgam(x)).imag - 1) for x in xs)
r_m = max(abs((dgam(x) / (gam(x) + I)).imag - mp.mpf(1) / 2) for x in xs)
r_p = max(abs((dgam(x) / (gam(x) - I)).imag - mp.mpf(1) / 2)
          for x in xs if abs(x - PI / 2) > mp.mpf('1e-3'))
report("F2", r_t < mp.mpf('1e-30') and r_m < mp.mpf('1e-30') and r_p < mp.mpf('1e-30'),
       f"tangent rate 1 to {mp.nstr(r_t, 3)}, chord rates 1/2 to "
       f"{mp.nstr(max(r_m, r_p), 3)} -- the inscribed-angle theorem")

# ----------------------------------------------------------- (F3) closed forms
worst = mp.mpf(0)
for x in [mp.mpf('0.2'), PI / 3, PI / 2, 2 * PI / 3, PI - mp.mpf('0.2')]:
    worst = max(worst, abs(polarAngle(dgam, d2gam, 0, 0, x) - (PI / 2 + x)))
    worst = max(worst, abs(polarAngle(gam, dgam, -I, 0, x) - (PI / 4 + x / 2)))
for x in [mp.mpf('0.2'), PI / 4, PI / 2 - mp.mpf('0.05')]:
    worst = max(worst, abs(polarAngle(gam, dgam, I, 0, x) - (-PI / 4 + x / 2)))
for x in [PI / 2 + mp.mpf('0.05'), 3 * PI / 4, PI - mp.mpf('0.2')]:
    worst = max(worst, abs(polarAngle(gam, dgam, I, PI, x) - (-3 * PI / 4 + (x - PI) / 2)))
report("F3", worst < mp.mpf('1e-25'),
       f"all four branches match their closed forms to {mp.nstr(worst, 6)}")

# ------------------------------------------------------- (F4) the three ranges
d_miss = [(PI / 4 + x / 2) / PI for x in [mp.mpf('1e-6'), PI / 2, PI - mp.mpf('1e-6')]]
d_low = [(3 * PI / 4 + x / 2) / PI for x in [mp.mpf('1e-6'), PI / 4, PI / 2 - mp.mpf('1e-6')]]
d_up = [(7 * PI / 4 + x / 2) / PI
        for x in [PI / 2 + mp.mpf('1e-6'), 3 * PI / 4, PI - mp.mpf('1e-6')]]
report("F4", all(0 < v < 1 for v in d_miss) and all(0 < v < 1 for v in d_low)
       and all(2 < v < 3 for v in d_up),
       f"Delta/pi in ({mp.nstr(d_miss[0], 6)}, {mp.nstr(d_miss[-1], 6)}), "
       f"({mp.nstr(d_low[0], 6)}, {mp.nstr(d_low[-1], 6)}), "
       f"({mp.nstr(d_up[0], 6)}, {mp.nstr(d_up[-1], 6)}) -- every tangency set empty")

# ------------------------------------------ (F5) the bound is attained at pi/2
lim_low = [(3 * PI / 4 + (PI / 2 - mp.mpf(10) ** (-k)) / 2) / PI for k in range(2, 8)]
lim_up = [(7 * PI / 4 + (PI / 2 + mp.mpf(10) ** (-k)) / 2) / PI for k in range(2, 8)]
report("F5", abs(lim_low[-1] - 1) < mp.mpf('1e-7') and abs(lim_up[-1] - 2) < mp.mpf('1e-7')
       and all(v < 1 for v in lim_low) and all(v > 2 for v in lim_up),
       f"as x -> pi/2 the two differences reach {mp.nstr(lim_low[-1], 12)}*pi and "
       f"{mp.nstr(lim_up[-1], 12)}*pi without touching -- the collision is the only "
       f"tangency, and it is excluded")

# ------------------------------------------------- (F6) the amplitude's divisor
# W = -gamma B(gamma)/E(gamma) with Q = 1 - 4t + t^2, r = 1, E = tQ' - Q
Qp = lambda t: 1 - 4 * t + t ** 2
E = lambda t: t * (-4 + 2 * t) - Qp(t)
Bp = lambda t: t ** 2 + 1
W = lambda x: -gam(x) * Bp(gam(x)) / E(gam(x))
zero_at = abs(W(PI / 2))
away = min(abs(W(mp.mpf(k) * PI / 40)) for k in range(1, 40)
           if abs(mp.mpf(k) * PI / 40 - PI / 2) > mp.mpf('0.1'))
report("F6", zero_at < mp.mpf('1e-30') and away > mp.mpf('0.05'),
       f"|W(pi/2)| = {mp.nstr(zero_at, 3)} and |W| >= {mp.nstr(away, 6)} elsewhere on "
       f"the arc, so a block on which W does not vanish misses pi/2")

print()
print("ALL PASS  check_favard_root_states")
