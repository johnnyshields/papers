#!/usr/bin/env python3
r"""Paper section `thm:weighted-dominance`, `lem:amplitude-divisor`,
`eq:W-endpoint-form`, `eq:W-on-g`.

`lem:amplitude-divisor` gives `p = nu - (k-1)` at a finite endpoint, and says
`k = 2` at the finite upper endpoint of an `r = 1` arc -- so `p_1 = nu - 1` for
**every** `nu`, with no condition on the numerator.  The formalization carried
`ord_{-L}(B) <= 1` instead, which is `p_1 <= 0`, and this script is what pins the
general statement: the exponent at each `nu`, the two boundary values of the
truncated `nu - 1`, and the two ways a wrong exponent could pass unnoticed.

At `Q = (1-t)^3`, `r = 1`, whose branch is closed form
(`tau = 1/(2 cos((pi - theta)/3))`).  Through `Amplitude.ftAmp_eq_ftCritical`,
`W = -gamma B(gamma)/E(gamma)` with `E = t Q'(t) - r Q(t)`, so the amplitude is a
rational function of the branch alone and the pencil parameter never enters.

Asserted, each as a failing test:

  (M1) `k = 2` and `ord_{t_b}(E) = 1` at the collision `t_b = -L = -1/2`: the
       limiting pencil has `D(t_b) = D'(t_b) = 0` and `D''(t_b) != 0`, while `E`
       has a simple zero there.  That is the `-1` in `p = nu - (k-1)`.
  (M2) The separation is LINEAR, `|t_+ - t_b| / eta -> L`, and the elementary
       lower bound the Lean route uses -- `tau(pi-eta) sin(eta) <= |t_+ - t_b|`,
       from `t_b` being real -- is within a factor of one of it.  So one side of
       the splitting is all the floor needs, and the two-sided rate is not.
  (M3) `|W| / eta^(nu-1)` converges to a positive constant at `nu = 0,1,2,3`,
       with `nu - 1` TRUNCATED in the naturals.  `nu = 0` and `nu = 1` are the
       boundary values and both give exponent `0`: at `nu = 0` the amplitude
       diverges, at `nu = 1` it tends to a positive limit, and a constant floor
       is right in both.
  (M4) At `nu = 2` a CONSTANT floor is false -- `|W| -> 0` -- so the dropped
       hypothesis was excluding a real case rather than tidying one away.
  (M5) The exponent is pinned from the other side too: `|W| / eta^nu` DIVERGES at
       every `nu >= 1`, so `p_1 = nu` is refuted and not merely unused.  Without
       this a floor stated one exponent too large would pass (M3) on the
       surviving cases and be wrong.

`mpmath` at 50 digits: (M3) at `nu = 3` compares quantities near `1e-14`, where
float64 is reporting its own rounding.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50

I = mp.mpc(0, 1)
R = 1
L = mp.mpf(1) / 2
TB = -L                                  # the collision point, REAL


def tau(theta):
    return 1 / (2 * mp.cos((mp.pi - theta) / 3))


def gamma(theta):
    return tau(theta) * mp.exp(I * theta)


def Qp(t):
    return (1 - t) ** 3


def E(t):
    return t * mp.diff(Qp, t) - R * Qp(t)


def W(B, theta):
    t = gamma(theta)
    return -t * B(t) / E(t)


def report(name, ok, detail):
    print(f"  {'PASS' if ok else 'FAIL'}  {name}: {detail}")
    assert ok, f"{name} failed: {detail}"


print("check_upper_endpoint_multiplicity")
print()

# ------------------------------------------------------- (M1) k = 2, ord E = 1
zb = -Qp(TB) / TB ** R                   # the limiting pencil's parameter
def D(t):
    return Qp(t) + zb * t

d0 = D(TB)
d1 = mp.diff(D, TB)
d2 = mp.diff(D, TB, 2)
e0 = E(TB)
e1 = mp.diff(E, TB)
report("M1", abs(d0) < mp.mpf('1e-40') and abs(d1) < mp.mpf('1e-40')
       and abs(d2) > mp.mpf('1e-3') and abs(e0) < mp.mpf('1e-40')
       and abs(e1) > mp.mpf('1e-3'),
       f"D(t_b)={mp.nstr(d0,4)}, D'(t_b)={mp.nstr(d1,4)}, D''(t_b)={mp.nstr(d2,6)} "
       f"=> k=2;  E(t_b)={mp.nstr(e0,4)}, E'(t_b)={mp.nstr(e1,6)} => ord E = 1")

# ---------------------------------------------------- (M2) the separation rate
ratios, floors = [], []
for k in range(2, 8):
    eta = mp.mpf(10) ** (-k)
    d = abs(gamma(mp.pi - eta) - TB)
    ratios.append(d / eta)
    floors.append(tau(mp.pi - eta) * mp.sin(eta) / d)
report("M2", abs(ratios[-1] - L) < mp.mpf('1e-6') and all(f <= 1 for f in floors)
       and floors[-1] > mp.mpf('0.999'),
       f"|t_+ - t_b|/eta -> {mp.nstr(ratios[-1], 10)} (= L), and the "
       f"tau*sin(eta) bound is {mp.nstr(floors[-1], 10)} of it")

# ------------------------------------- (M3) the exponent, and (M4)/(M5) its edges
def numer(nu):
    return lambda t: (t - TB) ** nu


print()
for nu in (0, 1, 2, 3):
    p = max(nu - 1, 0)                   # `nu - 1` truncated in the naturals
    vals = []
    for k in range(2, 7):
        eta = mp.mpf(10) ** (-k)
        vals.append(abs(W(numer(nu), mp.pi - eta)) / eta ** p)
    if nu == 0:
        # the lower boundary value: the amplitude DIVERGES, so a constant floor
        # holds a fortiori and `nu - 1 = 0` is right for a reason of its own
        report("M3 nu=0", vals[-1] > vals[0] * 100 and vals[0] > mp.mpf('1e-4'),
               f"|W| diverges, {mp.nstr(vals[0], 6)} -> {mp.nstr(vals[-1], 6)}, so the "
               f"eta^0 floor holds with room")
    else:
        stable = abs(vals[-1] - vals[-2]) < mp.mpf('1e-6') * abs(vals[-1])
        report(f"M3 nu={nu}", stable and vals[-1] > mp.mpf('1e-4'),
               f"|W|/eta^{p} -> {mp.nstr(vals[-1], 10)} > 0")

print()
# (M4) at nu = 2 a constant floor is FALSE
tail = [abs(W(numer(2), mp.pi - mp.mpf(10) ** (-k))) for k in range(2, 7)]
report("M4", tail[-1] < mp.mpf('1e-6') and tail[-1] < tail[0] / 1000,
       f"at nu=2, |W| falls from {mp.nstr(tail[0], 6)} to {mp.nstr(tail[-1], 6)}, "
       f"so no constant floor holds and the dropped hypothesis excluded a real case")

# (M5) one exponent too large is refuted
for nu in (1, 2, 3):
    big = [abs(W(numer(nu), mp.pi - mp.mpf(10) ** (-k))) / mp.mpf(10) ** (-k * nu)
           for k in range(2, 7)]
    report(f"M5 nu={nu}", big[-1] > big[0] * 100,
           f"|W|/eta^{nu} grows from {mp.nstr(big[0], 6)} to {mp.nstr(big[-1], 6)}, "
           f"so p_1 = nu is refuted")

print()
print("ALL PASS  check_upper_endpoint_multiplicity")
