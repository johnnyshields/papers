#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `thm:FT-geometry`,
`eq:endpoint-linear-gap`.

`weighted_dominance_of_branch`'s LOWER endpoint block has never been tested at
the real objects.  Its `hexp0` asserts a specific coefficient,

    zeta_j(theta) = 1 + [(cos(pi/rho) - omega_j)/sin(pi/rho)] theta + O(theta^2),
    omega_j = e^((2j-1) i pi / rho),

and `hBj0`/`hEj0` assert limits built from `clusterAlpha x1 rho j`.  Two defects
this session were coefficients that were the wrong SHAPE; this checks that the
lower coefficient is the right NUMBER, which is a different question and one no
gate in the tree asks.

Pencil: Q(t) = (1-t)^3, r = 1.  Then rQ - tQ' = (1-t)^2 (1+2t), so t_a = 1 with
the smallest zero of Q of multiplicity rho = 3 -- the smallest pencil whose
lower cluster has a nonprincipal member (rho - 2 = 1).  Branch found by solving
Im[(1 - tau e^(i th))^3 / (tau e^(i th))] = 0 for the smallest positive tau.

  (L1) The branch is real: z(theta) is real, t_+ = tau e^(i th) is a root, and
       tau is the MINIMUM modulus -- the property that defines the branch and
       the one a naive root-finder gets wrong.
  (L2) The cluster: all three roots tend to t_a = 1, and the normalized roots
       tend to the cube roots of -1, principal pair at e^(+-i pi/3).
  (L3) `hexp0`'s coefficient is the right number: the nonprincipal normalized
       root matches 1 + c theta to O(theta^2) with c = (cos(pi/3) - omega)/sin(pi/3)
       at omega = -1, and the residual over theta^2 stays bounded.
  (L4) `hexp0` is satisfiable jointly with the gap it feeds: the same constant
       gives 1 + c0 theta <= |zeta_j| for the whole nonprincipal cluster.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 40
PASSES = 0
RHO = 3


def ok(msg):
    global PASSES
    PASSES += 1
    print(f'PASS  {msg}')


def imag_cond(tau, th):
    """Im of -Q(t)/t at t = tau e^(i th); vanishes exactly when z is real."""
    t = tau * mp.e**(1j * th)
    return mp.im(-((1 - t) ** 3) / t)


def branch(th):
    """(tau, z) for the principal branch at angle th: the SMALLEST positive tau
    solving the reality condition.  Bracketing from just above 0 is what keeps
    the solver on the minimum-modulus branch."""
    lo, hi = mp.mpf('1e-12'), mp.mpf(1)
    f_lo = imag_cond(lo, th)
    step = mp.mpf('0.001')
    x = lo
    while x < 8:
        nx = x + step
        if imag_cond(x, th) * imag_cond(nx, th) < 0:
            tau = mp.findroot(lambda u: imag_cond(u, th), (x, nx), solver='bisect',
                              tol=mp.mpf('1e-35'))
            t = tau * mp.e**(1j * th)
            return tau, mp.re(-((1 - t) ** 3) / t)
        x = nx
    raise RuntimeError('no branch found')


def roots_at(zval):
    # (1-t)^3 + z t = -t^3 + 3t^2 + (z-3)t + 1
    return mp.polyroots([-1, 3, zval - 3, 1], maxsteps=6000, extraprec=800)


THETAS = [mp.mpf('0.2') / 2**k for k in range(9)]

# ---------------------------------------------------------------- (L1)
worst_res, worst_min = mp.mpf(0), mp.mpf(0)
data = []
for th in THETAS:
    tau, zval = branch(th)
    t = tau * mp.e**(1j * th)
    worst_res = max(worst_res, abs((1 - t) ** 3 + zval * t))
    rts = roots_at(zval)
    mods = sorted(abs(w) for w in rts)
    worst_min = max(worst_min, abs(mods[0] - tau), abs(mods[1] - tau))
    data.append((th, tau, zval, rts))
assert worst_res < mp.mpf('1e-25'), worst_res
assert worst_min < mp.mpf('1e-25'), worst_min
ok(f'(L1) the branch is real and minimum-modulus at all {len(THETAS)} angles: '
   f'|D(t_+, z)| <= {mp.nstr(worst_res, 4)} and the two smallest root moduli both equal '
   f'tau to {mp.nstr(worst_min, 4)} -- so the solver is on the branch tau is DEFINED '
   f'by, not a larger one')

# ---------------------------------------------------------------- (L2)
# At the LOWER endpoint every root of the cluster tends to x_1 and tau tends to
# x_1 with them, so the NORMALIZED roots tend to 1 -- the omega_j enter the
# coefficient, not the limit.  (At the upper endpoint they are the limit; the
# two endpoints differ here as well, which is the same asymmetry that made a
# shared binder block wrong.)
worst_ta, worst_zeta = mp.mpf(0), mp.mpf(0)
for th, tau, zval, rts in data:
    for w in rts:
        if th == THETAS[-1]:
            worst_ta = max(worst_ta, abs(w - 1))
        worst_zeta = max(worst_zeta, abs(w / tau - 1) / th)
assert worst_ta < mp.mpf('1e-2'), worst_ta
assert worst_zeta < 5, worst_zeta
ok(f'(L2) at the lower endpoint all three roots tend to t_a = x_1 = 1 (within '
   f'{mp.nstr(worst_ta, 3)} at the smallest angle) and every NORMALIZED root tends to 1 '
   f'at rate O(theta) (quotient under {mp.nstr(worst_zeta, 4)}) -- the omega_j sit in '
   f'the coefficient here, not in the limit, unlike the upper endpoint')

# ---------------------------------------------------------------- (L3)
c_paper = (mp.cos(mp.pi / RHO) - mp.mpf(-1)) / mp.sin(mp.pi / RHO)   # omega = -1
quot = []
for th, tau, zval, rts in data:
    s = sorted(rts, key=lambda w: abs(w))
    nonprincipal = s[2]
    zeta = nonprincipal / tau
    quot.append(abs(zeta - (1 + c_paper * th)) / th**2)
assert max(quot) / min(quot) < 6, quot
ok(f'(L3) `hexp0`\'s coefficient is the right number: with c = (cos(pi/3)+1)/sin(pi/3) '
   f'= {mp.nstr(c_paper, 8)} the residual |zeta - (1 + c theta)| / theta^2 stays in '
   f'[{mp.nstr(min(quot), 4)}, {mp.nstr(max(quot), 4)}] over nine halvings of theta -- '
   f'bounded, so the expansion is O(theta^2) with exactly that linear term')

# ---------------------------------------------------------------- (L4)
c0 = c_paper / 2
worst_gap = None
for th, tau, zval, rts in data:
    s = sorted(rts, key=lambda w: abs(w))
    zeta = s[2] / tau
    slack = abs(zeta) - (1 + c0 * th)
    worst_gap = slack if worst_gap is None else min(worst_gap, slack)
assert worst_gap > 0, worst_gap
ok(f'(L4) the same coefficient feeds the gap it is there for: '
   f'1 + (c/2) theta <= |zeta_j| holds for the whole nonprincipal cluster with slack '
   f'>= {mp.nstr(worst_gap, 4)} -- `hexp0` and eq:endpoint-linear-gap are satisfiable '
   f'together, not just separately')

print(f'\n{PASSES} checks')
print('ALL PASS: check_lower_cluster_expansion')
