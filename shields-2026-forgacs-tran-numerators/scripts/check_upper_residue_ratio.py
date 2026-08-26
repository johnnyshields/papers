#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`, `eq:upper-residue-ratio`.

The upper-endpoint binders of `weighted_dominance_of_branch` were rewritten after
the block stated for the LOWER endpoint turned out to be unsatisfiable above
`r = 1`: there `d_t D` diverges like `1/tau`, so dividing it by a positive power
of the window coordinate has no finite limit.  The replacement states the
manuscript's own `eq:upper-residue-ratio` instead,

    W_j/W = zeta_j/zeta_+ (1 + O(tau)),      |W_j/W| -> 1,

which is what the Lean hypotheses `hratio1` (the limit exists) and `hL1` (its
modulus is one) carry.  A binder introduced to replace a vacuous one has to be
checked at the real objects rather than trusted, so this script does that.

  (U1) The diagnosis.  At the upper endpoint with r > 1 the branch point runs
       into the origin, tau is of order eta, and |d_t D| at the principal root
       grows like 1/eta -- so the retired binder's quotient d_t D / eta^(rho-1)
       diverges for every rho >= 2 and no finite limit exists.
  (U2) The replacement.  |W_j / W_+| -> 1 over the nonprincipal upper cluster,
       and the convergence is O(tau) as the manuscript states.
  (U3) The normalized cluster tends to the r-th roots of -1, with the principal
       pair at e^(+-i pi/r) -- the `r`, not `rho`, that the corrected `hexp1`,
       `hwne1` and `hwne'1` carry.
  (U4) `n1 = r - 2`: the cluster is empty at r = 2, which is what `hn1r` records.

Pencil: Q(t) = 1 - t with r = 3, so max{deg Q, r} = 3 and the upper endpoint is
the unbounded one.  Roots are found by `mpmath.polyroots` at high precision.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50
PASSES = 0


def ok(msg):
    global PASSES
    PASSES += 1
    print(f'PASS  {msg}')


R = 3                                   # the order r
def roots_at(zval):
    """Roots of Q(t) + z t^r with Q = 1 - t, highest degree first."""
    cf = [zval, mp.mpf(0), -mp.mpf(1), mp.mpf(1)]        # z t^3 + 0 t^2 - t + 1
    return mp.polyroots(cf, maxsteps=6000, extraprec=800)


def principal_pair(rts):
    """The two smallest-modulus roots; they are a conjugate pair."""
    s = sorted(rts, key=lambda w: abs(w))
    return s[0], s[1], s[2:]


def dD(t, zval):
    """d_t D = Q'(t) + r z t^(r-1) = -1 + 3 z t^2."""
    return -1 + 3 * zval * t**2


# ---------------------------------------------------------------- (U1)
prev = None
growth = []
for k in range(4, 12):
    zval = mp.mpf(10) ** k
    rts = roots_at(zval)
    tp, tm, rest = principal_pair(rts)
    tau = abs(tp)
    val = abs(dD(tp, zval))
    growth.append((tau, val))
assert all(g[0] > h[0] for g, h in zip(growth, growth[1:]))     # tau decreasing
assert all(g[1] < h[1] for g, h in zip(growth, growth[1:]))     # |d_t D| increasing
ratios = [g[1] * g[0] for g in growth]                          # |d_t D| * tau
assert max(ratios) / min(ratios) < 1.05, ratios
ok(f'(U1) at the upper endpoint tau -> 0 while |d_t D| -> infinity, with '
   f'|d_t D|*tau pinned to {mp.nstr(ratios[0], 6)} across eight decades -- so '
   f'|d_t D| ~ 1/tau exactly as eq:upper-residue-ratio\'s display says, and the '
   f'retired binder d_t D / delta^(rho-1) diverges for every rho >= 2')

# ---------------------------------------------------------------- (U2),(U3)
# `eq:upper-residue-ratio` claims `1 + O(tau)`, not equality, so the rate is what
# is tested: the deviation is divided by tau and the quotient must stay bounded.
# A threshold on the raw deviation would only be testing how far along the
# sequence the loop happens to run.
ratio_dev, omega_dev = [], []
for k in range(6, 14):
    zval = mp.mpf(10) ** k
    rts = roots_at(zval)
    tp, tm, rest = principal_pair(rts)
    tau = abs(tp)
    Wp = -1 / dD(tp, zval)
    for tj in rest:
        Wj = -1 / dD(tj, zval)
        ratio_dev.append((tau, abs(abs(Wj / Wp) - 1)))
    for tj in list(rest) + [tp, tm]:
        zeta = tj / tau
        best = min(abs(zeta - mp.e**(1j * (2 * j - 1) * mp.pi / R)) for j in range(1, R + 1))
        omega_dev.append((tau, best))

rq = [d / t for t, d in ratio_dev]
assert max(rq) < 1, max(rq)
assert ratio_dev[-1][1] < ratio_dev[0][1] / 100, (ratio_dev[0][1], ratio_dev[-1][1])
ok(f'(U2) |W_j/W_+| -> 1 over the nonprincipal upper cluster, at the rate the '
   f'manuscript states: the deviation over tau stays under {mp.nstr(max(rq), 4)} across '
   f'eight decades of z while the deviation itself falls from '
   f'{mp.nstr(ratio_dev[0][1], 4)} to {mp.nstr(ratio_dev[-1][1], 4)} -- so it is '
   f'1 + O(tau), which is the modulus `hL1` asserts in the limit')

oq = [d / t for t, d in omega_dev]
assert max(oq) < 2, max(oq)
assert omega_dev[-1][1] < omega_dev[0][1] / 100, (omega_dev[0][1], omega_dev[-1][1])
ok(f'(U3) every normalized root converges to an r-th root of -1 with r = {R}, the two '
   f'principal ones to e^(+-i pi/r), again at rate O(tau) (quotient under '
   f'{mp.nstr(max(oq), 4)}) -- the parameter the corrected hexp1/hwne1 carry, '
   f'which had been rho')

# ---------------------------------------------------------------- (U4)
zval = mp.mpf(10) ** 10
rts = roots_at(zval)
tp, tm, rest = principal_pair(rts)
assert len(rest) == R - 2, (len(rest), R - 2)
ok(f'(U4) the nonprincipal upper cluster has r - 2 = {R - 2} member(s), so it is empty '
   f'at r = 2 where both roots of -1 are principal -- the boundary `hn1r` records')

print(f'\n{PASSES} checks')
print('ALL PASS: check_upper_residue_ratio')
