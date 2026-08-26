#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `lem:principal-endpoint-regularity`,
`eq:principal-finite-endpoint-regularity`.

`weighted_dominance_of_branch` carries

    hgd0 : HasDerivAt (fun delta => ftPrincipal tau delta) gamma_e 0

a TWO-SIDED derivative of the principal branch at the endpoint.  The manuscript's
own statement is one-sided: `lem:principal-endpoint-regularity` extends the branch
to a regular arc on the CLOSED interval `[0, pi/r]`, and `delta` is the angular
DISTANCE to the endpoint, so `delta >= 0` throughout.

This script measures the difference quotient from both sides at the witness
pencil `Q = (1-t)^3`, `r = 1`, where the branch is `2 tau^3 cos(theta) = 3 tau^2 - 1`.

  (D1) tau is EVEN in theta -- the branch condition depends on theta only through
       cos -- so the one-sided difference quotients at the endpoint are negatives
       of one another and the two-sided derivative cannot exist unless both are 0.
  (D2) They are not 0: both converge to +-1/sqrt(3), which is the rate the closed
       form `1 - cos(theta) = (tau-1)^2 (2 tau + 1)/(2 tau^3)` predicts by
       comparing theta^2/2 against 3(1-tau)^2/2.
  (D3) So `hgd0` as stated is unsatisfiable at this branch, exactly as the
       two-sided `hrootev0` was before it was weakened.  The satisfiable form is
       `HasDerivWithinAt ... (Set.Ici 0) 0`.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 40
PASSES = 0


def ok(msg):
    global PASSES
    PASSES += 1
    print(f'PASS  {msg}')


def tau(th):
    cf = [2 * mp.cos(th), -3, mp.mpf(0), mp.mpf(1)]
    return min(mp.re(r) for r in mp.polyroots(cf, maxsteps=5000, extraprec=600)
               if abs(mp.im(r)) < mp.mpf('1e-30') and 0 < mp.re(r) <= 1)


HS = [mp.mpf('0.1') / 2**k for k in range(2, 10)]

# ---------------------------------------------------------------- (D1)
worst = mp.mpf(0)
for h in HS:
    worst = max(worst, abs(tau(h) - tau(-h)))
assert worst < mp.mpf('1e-30'), worst
ok(f'(D1) tau is even in theta to {mp.nstr(worst, 4)} over eight halvings -- the branch '
   f'condition sees theta only through cos, so the two one-sided difference quotients at '
   f'the endpoint are exact negatives')

# ---------------------------------------------------------------- (D2)
qp = [(tau(h) - 1) / h for h in HS]
qm = [(tau(-h) - 1) / (-h) for h in HS]
target = 1 / mp.sqrt(3)
assert all(q < 0 for q in qp) and all(q > 0 for q in qm)
assert abs(qp[-1] + target) < mp.mpf('1e-3'), qp[-1]
assert abs(qm[-1] - target) < mp.mpf('1e-3'), qm[-1]
ok(f'(D2) the one-sided quotients converge to {mp.nstr(qp[-1], 8)} and '
   f'{mp.nstr(qm[-1], 8)}, against -+1/sqrt(3) = {mp.nstr(target, 8)} -- the rate the '
   f'closed-form endpoint identity predicts')

# ---------------------------------------------------------------- (D3)
gap = min(abs(a - b) for a, b in zip(qp, qm))
assert gap > 1, gap
ok(f'(D3) the two one-sided limits differ by at least {mp.nstr(gap, 6)}, so no two-sided '
   f'derivative exists at the endpoint: `hgd0` as stated is UNSATISFIABLE at the branch, '
   f'and the satisfiable form is HasDerivWithinAt on Ici 0')

print(f'\n{PASSES} checks')
print('ALL PASS: check_endpoint_derivative_onesided')
