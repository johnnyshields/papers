#!/usr/bin/env python3
r"""Paper section `thm:FT-geometry`, `lem:principal-endpoint-regularity`,
`cor:linear-phase-variation`.

The root-state producer asks for the branch's first two derivatives on an OPEN set
containing the closed arc `[0, pi]`.  This script measures whether the cubic pencil's
branch has them there.  It does not: `cubicTau` has a corner at `theta = 0`, and the
reason is the geometry rather than the parameterization -- at `theta = 0` the branch
point is a DOUBLE root of `2 cos(theta) tau^3 - 3 tau^2 + 1`, so the implicit function
theorem does not apply and the branch leaves it with a square-root singularity in the
parameter.

Asserted, each as a failing test:

  (C1) `cubicTau` -- the unique root of the branch equation in `(0,1]` -- agrees with
       `1/(2 cos((pi-theta)/3))` on `[0, pi]` and BEYOND `pi`, but NOT for `theta < 0`.
       That is where the two definitions part, and it is exactly where the corner is.
  (C2) The one-sided slopes at `theta = 0` are `-sqrt(3)/3` and `+sqrt(3)/3`: exact
       negatives, both nonzero.  So no two-sided derivative exists there.
  (C3) `tau(theta) = 1 - |theta|/sqrt(3) + O(theta^2)`, the square-root singularity of
       the double root, against the model to `1e-4` at `|theta| = 1e-4`.
  (C4) At the OTHER endpoint `theta = pi` both one-sided slopes tend to `0`, so there is
       NO corner there.  The obstruction is at one endpoint, not at "the endpoints" --
       a check asserting the weaker reading would be wrong at half of them, and the
       formalization would then be blocked for a reason that is not the real one.
  (C5) The curvature `K = tau^2 + 2 tau'^2 - tau tau''` equals `(8/9) tau^2` and is
       positive on the CLOSED arc, endpoints included.  So `hcurv` is not what fails,
       and the obstruction cannot be read as a curvature problem.
  (C6) `wedge(gamma'', gamma') = K` at this branch, which is what carries (C5) into the
       producer's hypothesis.

`mpmath` at 40 digits; the branch is solved by bisection on `(0,1]` rather than from the
closed form, so (C1) is a genuine comparison and not a tautology.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 40

PI = mp.pi
I = mp.mpc(0, 1)


def cubicTau(th):
    """The unique root of `2 cos(th) t^3 - 3 t^2 + 1` in `(0, 1]`, by bisection."""
    f = lambda t: 2 * mp.cos(th) * t ** 3 - 3 * t ** 2 + 1
    lo, hi = mp.mpf('1e-35'), mp.mpf(1)
    if f(hi) > 0:
        return hi
    for _ in range(400):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


cf = lambda th: 1 / (2 * mp.cos((PI - th) / 3))
tauD = lambda th: -mp.sin((PI - th) / 3) / (6 * mp.cos((PI - th) / 3) ** 2)
tauD2 = lambda th: (mp.cos((PI - th) / 3) ** 2 + 2 * mp.sin((PI - th) / 3) ** 2) \
    / (18 * mp.cos((PI - th) / 3) ** 3)

# (C5) and (C6) read tau off the closed form, which (C1) has just shown is the same
# function on the arc; the bisection's own error is the double root's and would set the
# tolerance rather than the identity
gam = lambda th: cf(th) * mp.e ** (I * th)
dgam = lambda th: mp.e ** (I * th) * (tauD(th) + cf(th) * I)
d2gam = lambda th: mp.e ** (I * th) * (tauD2(th) + 2 * tauD(th) * I - cf(th))
wedge = lambda u, w: u.imag * w.real - u.real * w.imag


def report(name, ok, detail):
    print(f"  {'PASS' if ok else 'FAIL'}  {name}: {detail}")
    assert ok, f"{name} failed: {detail}"


print("check_cubic_branch_corner")
print()

# ------------------------------------------- (C1) where the two definitions part
inside = max(abs(cubicTau(th) - cf(th))
             for th in [mp.mpf(k) * PI / 12 for k in range(13)])
beyond = abs(cubicTau(PI + mp.mpf('0.35')) - cf(PI + mp.mpf('0.35')))
before = abs(cubicTau(-mp.mpf('0.3')) - cf(-mp.mpf('0.3')))
# the bisection converges only to about the square root of the working precision at
# theta = 0, where the branch equation has a DOUBLE root -- which is the phenomenon
# this whole script is about, so the tolerance is set by it rather than by the digits
report("C1", inside < mp.mpf('1e-18') and beyond < mp.mpf('1e-30') and before > mp.mpf('0.3'),
       f"agree on [0,pi] to {mp.nstr(inside, 3)} and past pi to {mp.nstr(beyond, 3)}, but "
       f"differ by {mp.nstr(before, 6)} at theta = -0.3")

# ------------------------------------------------ (C2) the corner at theta = 0
t0 = cubicTau(mp.mpf(0))
h = mp.mpf(10) ** (-8)
right = (cubicTau(h) - t0) / h
left = (cubicTau(-h) - t0) / (-h)
target = -mp.sqrt(3) / 3
report("C2", abs(right - target) < mp.mpf('1e-7') and abs(left + target) < mp.mpf('1e-7')
       and abs(right) > mp.mpf('0.5'),
       f"right slope {mp.nstr(right, 10)}, left slope {mp.nstr(left, 10)}, "
       f"-sqrt(3)/3 = {mp.nstr(target, 10)} -- exact negatives, both nonzero")

# ------------------------------------------------ (C3) the square-root singularity
worst = max(abs(cubicTau(s * mp.mpf(10) ** (-k)) - (1 - mp.mpf(10) ** (-k) / mp.sqrt(3)))
            / mp.mpf(10) ** (-k)
            for k in (3, 4, 5) for s in (1, -1))
report("C3", worst < mp.mpf('1e-2'),
       f"|tau - (1 - |theta|/sqrt 3)| / |theta| <= {mp.nstr(worst, 6)}, so the leading "
       f"behaviour is the double root's")

# ------------------------------------ (C4) the UPPER endpoint has no corner
tpi = cubicTau(PI)
hl = (cubicTau(PI - h) - tpi) / (-h)
hr = (cubicTau(PI + h) - tpi) / h
report("C4", abs(hl) < mp.mpf('1e-6') and abs(hr) < mp.mpf('1e-6'),
       f"at pi the one-sided slopes are {mp.nstr(hl, 6)} and {mp.nstr(hr, 6)}, both -> 0, "
       f"so the obstruction is at theta = 0 alone")

# ------------------------------------------- (C5) the curvature on the CLOSED arc
Ks = [(cf(th) ** 2 + 2 * tauD(th) ** 2 - cf(th) * tauD2(th),
       mp.mpf(8) / 9 * cf(th) ** 2)
      for th in [mp.mpf(k) * PI / 12 for k in range(13)]]
report("C5", all(abs(a - b) < mp.mpf('1e-30') for a, b in Ks) and all(a > 0 for a, _ in Ks),
       f"K = (8/9)tau^2 throughout, from {mp.nstr(Ks[0][0], 8)} at 0 to "
       f"{mp.nstr(Ks[-1][0], 8)} at pi -- positive at both endpoints, so hcurv is not "
       f"what fails")

# ------------------------------------------------------- (C6) the wedge identity
wworst = max(abs(wedge(d2gam(th), dgam(th))
                 - (cf(th) ** 2 + 2 * tauD(th) ** 2 - cf(th) * tauD2(th)))
             for th in [mp.mpf(k) * PI / 12 for k in range(13)])
report("C6", wworst < mp.mpf('1e-28'),
       f"wedge(gamma'', gamma') = K to {mp.nstr(wworst, 6)}")

print()
print("ALL PASS  check_cubic_branch_corner")
