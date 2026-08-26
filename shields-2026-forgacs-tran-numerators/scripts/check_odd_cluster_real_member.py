#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `eq:lower-cluster-expansion`;
`sec:dominance`, `thm:weighted-dominance`'s `hsimple_0`.

`PrincipalSimple` settles simplicity of a pencil zero OFF THE REAL AXIS
unconditionally, so it is tempting to read the endpoint block's `hsimple_0` as
a corollary of `eq:principal-simple` and the disk count as tidiness.  It is
not, and this measures why: **a cluster of odd multiplicity carries a member
ON the real axis**, which no off-axis argument reaches.

With `omega_j = e^{(2j-1) pi i / rho}` (`Cluster.clusterOmega`), a member is
real exactly when `(2j-1)/rho` is an odd integer, i.e. `2j - 1 = rho`.  That
has a solution `j = (rho+1)/2` in range precisely when `rho` is ODD, and then
`omega_j = e^{i pi} = -1` and

    alpha_j = -x_1 * (-1) / sin(pi/rho) = x_1 / sin(pi/rho) > 0,

so the member leaves `x_1` along the positive real direction.  For even `rho`
there is no such `j` and every member is off-axis.

Asserted, each as a failing test:

  (O1) The dichotomy is exact over `rho = 2..15`: an odd `rho` has exactly one
       real `alpha_j`, at `j = (rho+1)/2`; an even `rho` has none, with every
       member's imaginary part bounded away from zero.
  (O2) At `rho = 3` the real member's slope is `x_1/sin(pi/3) = 1.1547 x_1`,
       the constant the endpoint package carries.
  (O3) The real member is a genuine pencil zero, not an artifact of the model:
       at `a = (1,1,1)`, `r = 1` the third root of `Q + z t` really does sit on
       the real axis at `x_1 + 1.1547 x_1 delta + o(delta)`, verified against
       the exact cubic and against the predicted slope.
  (O4) Teeth: the off-axis members at the same `rho` have imaginary parts
       growing like `delta`, so the real one is distinguished rather than all
       three being near-real at small `delta`.

`mpmath` throughout: at `delta = 1e-6` the three cluster members agree to six
digits before they separate, and the quantity under test is the imaginary part
of one of them against zero.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50
I = mp.mpc(0, 1)


def omega(rho, j):
    return mp.exp((2 * mp.mpf(j) - 1) * mp.pi / rho * I)


def alpha(x1, rho, j):
    return -mp.mpf(x1) * omega(rho, j) / mp.sin(mp.pi / rho)


# ---------------------------------------------------------------------------
# (O1) the parity dichotomy
# ---------------------------------------------------------------------------
for rho in range(2, 16):
    reals = [j for j in range(rho)
             if abs(mp.im(alpha(1, rho, j))) < mp.mpf(10) ** (-40)]
    if rho % 2 == 1:
        assert reals == [(rho + 1) // 2], \
            f"odd rho={rho}: real members at {reals}, expected [{(rho+1)//2}]"
    else:
        assert reals == [], f"even rho={rho}: unexpected real member at {reals}"
        worst = min(abs(mp.im(alpha(1, rho, j))) for j in range(rho))
        assert worst > mp.mpf(1) / 100, f"even rho={rho} has a near-real member: {worst}"
print("PASS  (O1) odd rho has exactly one real member at j=(rho+1)/2, even rho has "
      "none, over rho = 2..15")

# ---------------------------------------------------------------------------
# (O2) the rho = 3 constant
# ---------------------------------------------------------------------------
a2 = alpha(1, 3, 2)
assert abs(mp.im(a2)) < mp.mpf(10) ** (-40), f"alpha_2 is not real: {a2}"
assert abs(mp.re(a2) - 1 / mp.sin(mp.pi / 3)) < mp.mpf(10) ** (-40)
assert abs(mp.re(a2) - mp.mpf('1.1547')) < mp.mpf(1) / 10000
print(f"PASS  (O2) at rho = 3 the real member's slope is "
      f"{mp.nstr(mp.re(a2), 10)} = x_1/sin(pi/3), positive and real")

# ---------------------------------------------------------------------------
# (O3) it is a genuine pencil zero
# ---------------------------------------------------------------------------
def tau(t):
    return 1 / (2 * mp.cos((mp.pi - t) / 3))


def roots_at(d):
    g = tau(d) * mp.exp(I * d)
    z = mp.re(-(1 - g) ** 3 / g)
    return z, mp.polyroots([mp.mpf(-1), mp.mpf(3), z - 3, mp.mpf(1)],
                           maxsteps=300, extraprec=600)


slopes = []
for k in (4, 5, 6):
    d = mp.mpf(10) ** (-k)
    z, rts = roots_at(d)
    real = [r for r in rts if abs(mp.im(r)) < mp.mpf(10) ** (-20)]
    assert len(real) == 1, f"delta=1e-{k}: {len(real)} real roots, expected 1"
    slopes.append((mp.re(real[0]) - 1) / d)
assert all(abs(s - mp.mpf('1.1547')) < mp.mpf(1) / 100 for s in slopes), \
    f"the real root's slope is not 1.1547: {[mp.nstr(s,8) for s in slopes]}"
print(f"PASS  (O3) the pencil really has one real root near x_1, at slope "
      f"{[mp.nstr(s, 8) for s in slopes]} against the predicted 1.1547")

# ---------------------------------------------------------------------------
# (O4) teeth -- the off-axis members are distinguished
# ---------------------------------------------------------------------------
ims = []
for k in (4, 5, 6):
    d = mp.mpf(10) ** (-k)
    z, rts = roots_at(d)
    off = [r for r in rts if abs(mp.im(r)) >= mp.mpf(10) ** (-20)]
    assert len(off) == 2, f"expected 2 off-axis roots, got {len(off)}"
    ims.append(min(abs(mp.im(r)) / d for r in off))
assert all(v > mp.mpf(1) / 2 for v in ims), \
    f"off-axis imaginary parts do not scale like delta: {[mp.nstr(v,6) for v in ims]}"
print(f"PASS  (O4) the two off-axis members have |Im|/delta = "
      f"{[mp.nstr(v, 6) for v in ims]}, bounded away from 0, so the real member is "
      f"genuinely distinguished and not one of three near-real roots")

print("ALL PASS  check_odd_cluster_real_member")
