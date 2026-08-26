#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `subsec:FT-geometry`, `thm:FT-geometry`;
`eq:ab-def`.

The upper end of the viewing arc is a DICHOTOMY in r, and this check pins the
side of it that is not the collapse.

For r >= 2 the branch radius collapses, tau(theta) -> 0 as theta -> (pi/r)^-,
and the endpoint of `eq:ab-def` is b = +infinity.  At r = 1 the arc ends at pi,
the collapse does not happen, and tau tends to a POSITIVE limit L: the arc point
tau e^{-i theta} runs to -L on the NEGATIVE real axis, where it is a critical
point of g(t) = -P(t)/t^r.  So `eq:ab-def`'s b is finite there.

  (V1) At r = 1 the radius converges, and the limit L solves sum_k L/(L+a_k) = 1
       -- the deficit equation the angle count collapses to at theta = pi.
  (V2) That L satisfies E(-L) = 0 for E(t) = t P'(t) - r P(t): the arc point is
       -L and it is a zero of the critical polynomial.  This is the statement
       `exists_tendsto_ftTau_nhdsLT_pi` carries.
  (V3) The uniform bound the Lean proof uses: tau(theta) <= 2 A with
       A = sum_k a_k, on the whole window theta in (pi - 1/2, pi).  The
       intermediate constant A/tau >= 65/96 is asserted with it, since that is
       the number the arctan/tan chain actually produces.
  (V4) The split is real: at r >= 2 the same pencils send tau -> 0, so a single
       theorem covering both endpoints would be false in one regime.  The r = 1
       positive-limit claim is asserted to FAIL at r = 2 and r = 3.
  (V5) The two instantiations the statement is checked at before it is proved:
       n = 3, r = 1, a = [1,2,3]  and  n = 2, r = 2.

Bisection, not a formula: tau(theta) is defined implicitly by the angle sum
sum_k theta_k(tau) = r theta + (n-1) pi, which is strictly decreasing in tau.
"""

import mpmath as mp

mp.mp.dps = 40


def arccot(x):
    """The inverse cotangent onto (0, pi)."""
    return mp.pi / 2 - mp.atan(x)


def angle_sum(a, tau, theta):
    """sum_k theta_k, the Forgacs-Tran angle count at radius tau."""
    return mp.fsum(arccot((mp.cos(theta) - ak / tau) / mp.sin(theta)) for ak in a)


def ft_tau(a, r, theta):
    """The branch radius at angle theta, by bisection on the angle sum."""
    n = len(a)
    target = r * theta + (n - 1) * mp.pi
    lo, hi = mp.mpf('1e-30'), mp.mpf(1)
    while angle_sum(a, hi, theta) > target:
        hi *= 2
        if hi > mp.mpf('1e30'):
            raise RuntimeError('no bracket above')
    while angle_sum(a, lo, theta) < target:
        lo /= 2
        if lo < mp.mpf('1e-60'):
            raise RuntimeError('no bracket below')
    for _ in range(400):
        mid = (lo + hi) / 2
        if angle_sum(a, mid, theta) > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def deficit_root(a):
    """The positive L with sum_k L/(L+a_k) = 1, by bisection.

    The left side rises strictly from 0 to n = len(a), so the root is unique
    and exists exactly when n >= 2.
    """
    f = lambda t: mp.fsum(t / (t + ak) for ak in a) - 1
    lo, hi = mp.mpf('1e-30'), mp.mpf(1)
    while f(hi) < 0:
        hi *= 2
    for _ in range(400):
        mid = (lo + hi) / 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def eval_critical(a, c, r, t):
    """E(t) = t P'(t) - r P(t) for P(t) = c prod_k (a_k - t)."""
    P = c * mp.fprod([ak - t for ak in a])
    dP = c * mp.fsum(
        -mp.fprod([a[j] - t for j in range(len(a)) if j != k]) for k in range(len(a))
    )
    return t * dP - r * P


PENCILS = [
    [mp.mpf(1), mp.mpf(2), mp.mpf(3)],
    [mp.mpf(1), mp.mpf(1)],
    [mp.mpf('0.5'), mp.mpf(4)],
    [mp.mpf(1), mp.mpf(2), mp.mpf(3), mp.mpf(7)],
    [mp.mpf('2.5'), mp.mpf('2.5'), mp.mpf('0.25')],
]

print('== V1/V2: r = 1, tau -> L > 0 with sum L/(L+a_k) = 1 and E(-L) = 0 ==')
for a in PENCILS:
    L = deficit_root(a)
    assert L > 0, f'deficit root not positive at {a}'
    assert abs(mp.fsum(L / (L + ak) for ak in a) - 1) < mp.mpf('1e-30')
    prev = None
    for s in [mp.mpf('1e-2'), mp.mpf('1e-3'), mp.mpf('1e-4'), mp.mpf('1e-5')]:
        tau = ft_tau(a, 1, mp.pi - s)
        err = abs(tau - L)
        # a symmetric pencil holds tau at L exactly, so the error can already be
        # at the bisection floor; require a decrease only above it
        assert prev is None or err < prev or err < mp.mpf('1e-25'), \
            f'not converging at {a}, s = {s}'
        prev = err
    assert prev < mp.mpf('1e-4'), f'V1 fails at {a}: |tau - L| = {prev}'
    for c in [mp.mpf(1), mp.mpf('0.75'), mp.mpf(3)]:
        assert abs(eval_critical(a, c, 1, -L)) < mp.mpf('1e-28'), f'V2 fails at {a}, c = {c}'
    print(f'  a = {[mp.nstr(x, 5) for x in a]}  L = {mp.nstr(L, 12)}  '
          f'|tau - L| at s = 1e-5: {mp.nstr(prev, 4)}  E(-L) = 0')

print('== V3: tau <= 2 A and A/tau >= 65/96 on (pi - 1/2, pi), r = 1 ==')
for a in PENCILS:
    A = mp.fsum(a)
    worst = mp.mpf('1e30')
    for j in range(1, 60):
        s = mp.mpf('0.5') * j / 60
        tau = ft_tau(a, 1, mp.pi - s)
        assert tau <= 2 * A, f'V3 bound fails at {a}, s = {s}: tau = {tau} > {2 * A}'
        worst = min(worst, A / tau)
    assert worst >= mp.mpf(65) / 96, f'V3 constant fails at {a}: A/tau = {worst}'
    print(f'  a = {[mp.nstr(x, 5) for x in a]}  min A/tau = {mp.nstr(worst, 8)} '
          f'>= 65/96 = {mp.nstr(mp.mpf(65) / 96, 8)}')

print('== V4: at r >= 2 the radius collapses instead, so the split is real ==')
for a in PENCILS:
    for r in [2, 3]:
        taus = [ft_tau(a, r, mp.pi / r - s) for s in
                [mp.mpf('1e-2'), mp.mpf('1e-3'), mp.mpf('1e-4')]]
        assert taus[0] > taus[1] > taus[2], f'not decreasing at {a}, r = {r}'
        assert taus[2] < mp.mpf('1e-3'), f'no collapse at {a}, r = {r}: {taus[2]}'
        # the r = 1 conclusion is FALSE here: no positive limit to converge to
        L = deficit_root(a)
        assert abs(taus[2] - L) > mp.mpf('1e-3'), f'r = 1 claim wrongly holds at r = {r}'
    print(f'  a = {[mp.nstr(x, 5) for x in a]}  tau -> 0 at r = 2, 3')

print('== V5: the two instantiations ==')
a = [mp.mpf(1), mp.mpf(2), mp.mpf(3)]
L = deficit_root(a)
tau = ft_tau(a, 1, mp.pi - mp.mpf('1e-6'))
assert abs(tau - L) < mp.mpf('1e-6')
assert abs(L - mp.mpf('0.8793852416')) < mp.mpf('1e-9'), f'n = 3, r = 1 witness: {L}'
assert abs(eval_critical(a, mp.mpf(1), 1, -L)) < mp.mpf('1e-28')
print(f'  n = 3, r = 1, a = [1,2,3]:  L = {mp.nstr(L, 12)}, E(-L) = 0, tau -> L')
a2 = [mp.mpf(1), mp.mpf(2)]
tau2 = ft_tau(a2, 2, mp.pi / 2 - mp.mpf('1e-5'))
assert tau2 < mp.mpf('1e-4'), f'n = 2, r = 2 collapse: {tau2}'
assert abs(tau2 / mp.mpf('1e-5') - mp.mpf(4) / 3) < mp.mpf('1e-3'), f'rate: {tau2 / mp.mpf("1e-5")}'
print(f'  n = 2, r = 2, a = [1,2]:  tau(pi/2 - 1e-5) = {mp.nstr(tau2, 8)}, '
      f'tau/delta = {mp.nstr(tau2 / mp.mpf("1e-5"), 8)} -> 4/3')

print('ALL PASS')
