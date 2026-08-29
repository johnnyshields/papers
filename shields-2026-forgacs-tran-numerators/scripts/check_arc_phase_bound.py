#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `eq:W-local-zero`, `eq:W-endpoint-form`,
`eq:phase-derivative-bound`.

`eq:phase-derivative-bound` is asserted on the whole arc, amplitude zeros
included, and the reason it survives them is a cancellation that is invisible in
the modulus: both factorizations write `W` as a power of a REAL quantity times a
cofactor, and the logarithmic derivative of that power is real, so it drops out
of `Im(W'/W)` entirely.  `W'/W` blows up at a zero; `Im(W'/W)` does not.

Checked here at `Q = (1-t)^3`, `r = 1`, whose branch is closed form
(`tau = 1/(2 cos((pi - theta)/3))`), with `B = (t - t_0)(t - conj t_0)` chosen so
that `B(gamma(theta_0)) = 0` at `theta_0 = 2` -- a numerator with REAL
coefficients that genuinely vanishes on the branch, which is what an interior
member of the amplitude divisor is.  `Amplitude.ftAmp_eq_ftCritical` gives
`W = -gamma B(gamma)/E(gamma)` with `E = t Q'(t) - r Q(t)`, so

    W'/W = gamma' (1/gamma + B'(gamma)/B(gamma) - E'(gamma)/E(gamma)).

Asserted, each as a failing test:

  (D1) `|W'/W|` diverges like `1/|theta - theta_0|` at the interior zero -- so
       there IS a pole to survive, and the check is not vacuous.
  (D2) `|Im(W'/W)|` stays bounded across the same punctured collar, and the
       bound does not grow as the collar shrinks.
  (D3) The interior split of `ArcPhaseBound.im_logDeriv_local_factorization`,
       term by term:  `Im(W'/W) = nu Im(h'/h) + Im(A'/A)` with
       `h(theta) = (gamma(theta) - gamma(theta_0))/(theta - theta_0)` the divided
       difference and `A = gamma Btilde(gamma)/E(gamma)`.
  (D4) At the LOWER endpoint `t_e = 1`, where `E` vanishes to order `k-1 = 2`
       and `B` does not, the exponent is the NEGATIVE integer `nu - (k-1) = -2`:
       `|W|` diverges like `theta^{-2}`.
  (D5) `|Im(W'/W)|` stays bounded there too, and
  (D6) the endpoint split of `ftAmp_eq_endpoint_factorization` holds term by
       term:  `Im(W'/W) = (nu - (k-1)) Im(u'/u) + Im(A'/A)` with
       `u(theta) = (gamma(theta) - t_e)/theta` and `A = gamma Btilde(gamma)/H(gamma)`,
       `H = E/(t - t_e)^{k-1}`.

`mpmath` throughout, at 60 digits: (D3) and (D6) are identities between two
expressions that each carry a `1/(theta - theta_0)` singularity, so the agreement
is a cancellation of large quantities and float64 would report its own rounding.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 60

I = mp.mpc(0, 1)
R = 1
THETA0 = mp.mpf(2)


def tau(theta):
    return 1 / (2 * mp.cos((mp.pi - theta) / 3))


def gamma(theta):
    return tau(theta) * mp.exp(I * theta)


def dgamma(theta):
    return mp.diff(gamma, theta)


def Qp(t):
    return (1 - t) ** 3


def dQ(t):
    return -3 * (1 - t) ** 2


def E(t):
    return t * dQ(t) - R * Qp(t)


def dE(t):
    return mp.diff(E, t)


T0 = gamma(THETA0)
TE = mp.mpf(1)          # the lower endpoint: gamma(0) = tau(0) = 1


def Bp(t):
    # real coefficients, simple zero at T0 and at its conjugate
    return (t - T0) * (t - mp.conj(T0))


def dB(t):
    return mp.diff(Bp, t)


def W(theta):
    g = gamma(theta)
    return -g * Bp(g) / E(g)


def logderiv_W(theta):
    g = gamma(theta)
    return dgamma(theta) * (1 / g + dB(g) / Bp(g) - dE(g) / E(g))


def report(name, ok, detail):
    print(f"  {'PASS' if ok else 'FAIL'}  {name}: {detail}")
    assert ok, f"{name} failed: {detail}"


print("check_arc_phase_bound")
print()

# ---------------------------------------------------------------- interior ---
print("interior amplitude zero at theta_0 = 2")

offsets = [mp.mpf(10) ** (-k) for k in range(2, 7)]
mods, ims = [], []
for h in offsets:
    for th in (THETA0 + h, THETA0 - h):
        L = logderiv_W(th)
        mods.append((h, abs(L)))
        ims.append((h, abs(mp.im(L))))

# (D1) the pole is there: |W'/W| * |theta - theta_0| tends to nu = 1
ratios = [m * h for h, m in mods]
report("D1", all(abs(r - 1) < mp.mpf('1e-3') for r in ratios[-4:])
       and mods[-1][1] > mp.mpf('1e5'),
       f"|W'/W|*|dtheta| -> {mp.nstr(ratios[-1], 8)}, |W'/W| up to "
       f"{mp.nstr(mods[-1][1], 6)}")

# (D2) the imaginary part is bounded, and does not grow as the collar shrinks
im_max = max(v for _, v in ims)
im_tail = max(v for h, v in ims if h <= mp.mpf('1e-4'))
report("D2", im_max < 2 and abs(im_tail - im_max) < 2,
       f"max |Im(W'/W)| = {mp.nstr(im_max, 8)} over the whole collar, "
       f"{mp.nstr(im_tail, 8)} on its inner part")


def divdiff(theta):
    return (gamma(theta) - T0) / (theta - THETA0)


def d_divdiff(theta):
    d = theta - THETA0
    return (dgamma(theta) * d - (gamma(theta) - T0)) / d ** 2


def Bt_interior(t):
    return t - mp.conj(T0)


def A_interior_logderiv(theta):
    g = gamma(theta)
    return dgamma(theta) * (1 / g + 1 / Bt_interior(g) - dE(g) / E(g))


# (D3) the split, term by term
worst = mp.mpf(0)
for h in offsets:
    for th in (THETA0 + h, THETA0 - h):
        lhs = mp.im(logderiv_W(th))
        rhs = 1 * mp.im(d_divdiff(th) / divdiff(th)) + mp.im(A_interior_logderiv(th))
        worst = max(worst, abs(lhs - rhs))
report("D3", worst < mp.mpf('1e-20'),
       f"max |Im(W'/W) - (nu Im(h'/h) + Im(A'/A))| = {mp.nstr(worst, 6)}")

print()

# ---------------------------------------------------------------- endpoint ---
print("lower endpoint t_e = 1, where E vanishes to order k-1 = 2")

# E(t) = (1-t)^2 (-2t - 1); H is the cofactor, H(t_e) = -3 != 0
def H(t):
    return -2 * t - 1


def dH(t):
    return mp.mpf(-2)


checkE = max(abs(E(t) - (1 - t) ** 2 * H(t))
             for t in [mp.mpf('0.3'), mp.mpf('1.7'), mp.mpc(1, 1)])
report("E-factor", checkE < mp.mpf('1e-40'),
       f"E = (t-1)^2 H with H(1) = {mp.nstr(H(TE), 6)}, residual {mp.nstr(checkE, 6)}")

# nu = order of B at t_e = 1 is 0, so the exponent is 0 - 2 = -2
P_EXP = -2
small = [mp.mpf(10) ** (-k) for k in range(2, 6)]

# (D4) |W| ~ theta^{-2}
scaled = [abs(W(th)) * th ** 2 for th in small]
report("D4", all(abs(s - scaled[-1]) < mp.mpf('1e-2') * abs(scaled[-1]) for s in scaled[-2:])
       and abs(W(small[-1])) > mp.mpf('1e8'),
       f"|W| theta^2 -> {mp.nstr(scaled[-1], 8)}, |W| up to "
       f"{mp.nstr(abs(W(small[-1])), 6)}")

# (D5) the imaginary part of the logarithmic derivative stays bounded
ends = [abs(mp.im(logderiv_W(th))) for th in small]
report("D5", max(ends) < 5,
       f"max |Im(W'/W)| = {mp.nstr(max(ends), 8)} while |W'/W| reaches "
       f"{mp.nstr(abs(logderiv_W(small[-1])), 6)}")


def endpoint_cofactor(theta):
    return (gamma(theta) - TE) / theta


def d_endpoint_cofactor(theta):
    return (dgamma(theta) * theta - (gamma(theta) - TE)) / theta ** 2


def A_endpoint_logderiv(theta):
    g = gamma(theta)
    # Btilde = B, since B does not vanish at t_e
    return dgamma(theta) * (1 / g + dB(g) / Bp(g) - dH(g) / H(g))


# (D6) the endpoint split, term by term
worst_e = mp.mpf(0)
for th in small:
    lhs = mp.im(logderiv_W(th))
    rhs = P_EXP * mp.im(d_endpoint_cofactor(th) / endpoint_cofactor(th)) \
        + mp.im(A_endpoint_logderiv(th))
    worst_e = max(worst_e, abs(lhs - rhs))
report("D6", worst_e < mp.mpf('1e-20'),
       f"max |Im(W'/W) - ((nu-(k-1)) Im(u'/u) + Im(A'/A))| = {mp.nstr(worst_e, 6)}")

print()
print("ALL PASS  check_arc_phase_bound")
