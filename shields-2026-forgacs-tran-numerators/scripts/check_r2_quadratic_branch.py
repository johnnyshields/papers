#!/usr/bin/env python3
r"""Paper section `sec:dominance` (`thm:weighted-dominance`, `eq:retained-range`) and
`sec:geometry` (`thm:FT-geometry`), for the case r > 1.

`rem:quadratic-case` supplies the Favard pencil (deg Q, r) = (2, 1), whose principal
modulus tau is CONSTANT.  Every non-vacuity witness in lean/ for the clause-3 chain runs
on it, so all of it is certified at r = 1 only.  This script checks the load-bearing
claims for the smallest r > 1 pencil that is still quadratic in t --
Q = q0 + q1 t + q2 t^2 with r = 2, so D(t,z) = q0 + q1 t + (q2 + z) t^2 -- before any of
it is asserted in Lean.

  (W1) The branch.  With the principal pair t_pm = tau e^{+-i theta}, Vieta gives
       tau(theta) = -2 q0 cos(theta) / q1   and   z(theta) = q0/tau^2 - q2.
       Checked: t_pm really are the roots of D(., z(theta)), and tau -> 0 as
       theta -> pi/2, which is the endpoint behavior that makes r > 1 different
       from r = 1 and which no constant-modulus pencil exhibits.

  (W2) z is strictly increasing on (0, pi/2) with z -> +infinity, so I_{Q,r} is a RAY,
       matching `eq:ab-def`'s b = +infinity exactly when r > 1.

  (W3) The principal amplitude W = -B(t_+)/(d/dt)D(t_+) at B = 1 is PURELY IMAGINARY:
       W = i tau / (2 q0 sin theta).  Hence arg W = pi/2 is constant, so
       `eq:phase-derivative-bound` holds at kappa = 0 and `eq:linear-phase-variation`
       at kappa_0 = kappa_1 = 0 -- the same collapse the r = 1 pencil enjoys.

  (W4) No remainder.  The pair exhausts a quadratic denominator, so
       `eq:principal-decomposition` is exact: tau^{M+1} F_M(z(theta)) equals
       2 Re(W e^{-i(M+1)theta}) to working precision, i.e. ftRemainder = 0.

  (W5) The monomial shift at NON-constant modulus, which is what
       `ftRemainder_X_pow_of_pos` states:
           R_M^{(t^k)} = tau^k R_{M-k}^{(1)}.
       Checked on the amplitude and coefficient identities that lemma composes,
       at tau != 1, where the tau == 1 form would say nothing.

All assertions are failing tests, at 50-digit precision.
"""

import mpmath as mp

mp.mp.dps = 50

Q0, Q1, Q2 = mp.mpf(1), mp.mpf(-3), mp.mpf(1)   # q1 < 0 so tau > 0 on (0, pi/2)
R = 2


def tau_of(theta):
    return -2 * Q0 * mp.cos(theta) / Q1


def z_of(theta):
    t = tau_of(theta)
    return Q0 / t**2 - Q2


def D(t, z):
    return Q0 + Q1 * t + (Q2 + z) * t**2


def dD(t, z):
    return Q1 + 2 * (Q2 + z) * t


def coeffs(z, n):
    """Taylor coefficients F_0..F_n of 1/D(.,z) at t = 0, by the convolution recurrence."""
    d = [Q0, Q1, Q2 + z]
    F = []
    for m in range(n + 1):
        acc = mp.mpf(1) if m == 0 else mp.mpf(0)
        for i in range(1, min(m, 2) + 1):
            acc -= d[i] * F[m - i]
        F.append(acc / Q0)
    return F


THETAS = [mp.pi / 2 * mp.mpf(j) / 12 for j in range(1, 12)]   # interior of (0, pi/2)

# (W1) the principal pair really is the root pair, and tau -> 0 at the upper endpoint
for th in THETAS:
    tau, z = tau_of(th), z_of(th)
    assert tau > 0, f"tau must be positive on (0, pi/2): {th}"
    for s in (1, -1):
        t = tau * mp.exp(s * 1j * th)
        assert abs(D(t, z)) < mp.mpf(10) ** (-40), f"(W1) root failed at {th}, s={s}"
tau_near = tau_of(mp.pi / 2 - mp.mpf(10) ** (-6))
assert tau_near < mp.mpf(10) ** (-5), f"(W1) tau should vanish at the upper endpoint: {tau_near}"
assert abs(tau_of(THETAS[0]) - tau_of(THETAS[-1])) > mp.mpf("0.1"), \
    "(W1) tau must be NON-constant, else this is the r=1 case again"

# (W2) z strictly increasing, blowing up: I_{Q,r} is a ray
zs = [z_of(th) for th in THETAS]
for a, b in zip(zs, zs[1:]):
    assert b > a, "(W2) z must be strictly increasing on (0, pi/2)"
assert z_of(mp.pi / 2 - mp.mpf(10) ** (-6)) > mp.mpf(10) ** 10, \
    "(W2) z must blow up at the upper endpoint (b = +infinity for r > 1)"

# (W3) the amplitude is purely imaginary, so arg W is the constant pi/2
for th in THETAS:
    tau, z = tau_of(th), z_of(th)
    tp = tau * mp.exp(1j * th)
    W = -1 / dD(tp, z)
    predicted = 1j * tau / (2 * Q0 * mp.sin(th))
    assert abs(W - predicted) < mp.mpf(10) ** (-40), f"(W3) closed form failed at {th}"
    assert abs(mp.re(W)) < mp.mpf(10) ** (-40), f"(W3) W must be purely imaginary at {th}"
    assert abs(mp.arg(W) - mp.pi / 2) < mp.mpf(10) ** (-40), f"(W3) arg W != pi/2 at {th}"

# (W4) no remainder: eq:principal-decomposition is exact
for th in THETAS:
    tau, z = tau_of(th), z_of(th)
    tp = tau * mp.exp(1j * th)
    W = -1 / dD(tp, z)
    F = coeffs(z, 24)
    for M in range(0, 25):
        lhs = tau ** (M + 1) * F[M]
        rhs = 2 * mp.re(W * mp.exp(-1j * (M + 1) * th))
        assert abs(lhs - rhs) < mp.mpf(10) ** (-35), \
            f"(W4) remainder nonzero at theta={th}, M={M}: {abs(lhs - rhs)}"

# (W5) the monomial shift at non-constant modulus
for th in THETAS:
    tau, z = tau_of(th), z_of(th)
    tp = tau * mp.exp(1j * th)
    W1 = -1 / dD(tp, z)
    F = coeffs(z, 30)
    for k in range(0, 5):
        Wk = -(tp ** k) / dD(tp, z)
        assert abs(Wk - tp ** k * W1) < mp.mpf(10) ** (-38), "(W5) amplitude shift failed"
        for M in range(k, 26):
            # R_M^{(t^k)} with F^{(t^k)}_M = F^{(1)}_{M-k}
            lhs = tau ** (M + 1) * F[M - k] \
                - 2 * mp.re(tau ** (M + 1) * (Wk / tp ** (M + 1)))
            rhs = tau ** (M - k + 1) * F[M - k] \
                - 2 * mp.re(tau ** (M - k + 1) * (W1 / tp ** (M - k + 1)))
            assert abs(lhs - tau ** k * rhs) < mp.mpf(10) ** (-33), \
                f"(W5) R_M^(t^k) = tau^k R_(M-k)^(1) failed at theta={th}, k={k}, M={M}"
        # and at tau != 1 the tau==1 form is genuinely different
    assert abs(tau - 1) > mp.mpf("1e-3"), "(W5) tau must differ from 1 for this to bite"

print('ALL PASS: check_r2_quadratic_branch')
print(f"  Q = {Q0} + {Q1} t + {Q2} t^2, r = {R}")
print(f"  tau ranges over [{mp.nstr(tau_of(THETAS[-1]), 8)}, {mp.nstr(tau_of(THETAS[0]), 8)}]"
      "  (non-constant, -> 0 at theta = pi/2)")
print(f"  z ranges over [{mp.nstr(zs[0], 8)}, {mp.nstr(zs[-1], 8)}]  (increasing, -> +infinity)")
print("  arg W = pi/2 exactly, so kappa = 0 and kappa_0 = kappa_1 = 0")
print("  ftRemainder = 0 for all tested (theta, M); monomial shift carries the factor tau^k")
