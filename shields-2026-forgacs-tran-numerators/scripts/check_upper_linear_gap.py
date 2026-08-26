"""`eq:endpoint-linear-gap` at the upper endpoint (paper Sec. 4, `thm:weighted-dominance`).

Checks the coefficient the Lean producer
`ForgacsTran.EndpointUpperGap.tendsto_upper_normalized_modulus` proves:

    (|g_j| / tau - 1) / delta  ->  (cos(pi/r) - Re omega_j) / sin(pi/r),
    omega_j = mu_j * exp(i pi / r),   mu_j = exp(2 pi i j / r).

Two things are at stake and neither is visible in a build.

*The sum 1/a_k must cancel.*  It enters once through beta = Q'(0)/Q(0) = -sum 1/a_k
and once through the collapse rate L = r / (sin(pi/r) sum 1/a_k).  A derivation that
lost one of the two would agree with this at sum 1/a_k = 1 and disagree elsewhere,
so the pencils below are chosen with sum 1/a_k away from 1.

*The two principal indices must come out at coefficient zero.*  j = 0 and j = r-1
are the pair `hgmem_1` erases; if the direction convention were off by a rotation the
zeros would land on the wrong indices and the retained coefficients would go negative.

Numerics are mpmath at 40 digits: the quantity measured is a first-order rate, so
float64 masks the O(delta) error of the difference quotient itself.
"""

from mpmath import mp, mpf, mpc, exp, cos, sin, pi, im, fabs, polyroots

mp.dps = 40

PENCILS = [
    # (a, c, r) -- sum 1/a_k printed, deliberately not 1
    ([mpf(1), mpf(2)], mpf(1), 3),
    ([mpf(1), mpf(3)], mpf(2), 3),
    ([mpf(2), mpf(5)], mpf(1), 4),
    ([mpf(1), mpf(2), mpf(4)], mpf(1), 5),
]


def q_eval(a, c, t):
    v = mpc(c)
    for ak in a:
        v *= (mpc(ak) - t)
    return v


def branch_tau(a, c, r, theta):
    """tau > 0 with z = -Q(t_-)/t_-^r real, t_- = tau e^{-i theta}."""
    def f(tau):
        t = mpc(tau) * exp(-1j * theta)
        return im(-q_eval(a, c, t) / t ** r)
    # the upper endpoint collapses tau to 0, so bracket just above 0
    lo, hi = mpf('1e-30'), min(a) / 2
    flo, fhi = f(lo), f(hi)
    n = 0
    while flo * fhi > 0 and n < 200:
        hi /= 2
        fhi = f(hi)
        n += 1
    if flo * fhi > 0:
        return None
    # bisect on the interval width: |f| itself scales like tau^{-r} and never
    # reaches an absolute tolerance, so an absolute tolerance on f is the wrong test
    for _ in range(400):
        mid = (lo + hi) / 2
        if hi - lo < hi * mpf('1e-32'):
            break
        if f(lo) * f(mid) <= 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


def den_roots(a, c, r, z):
    """roots of Q(t) + z t^r, coefficients highest-first."""
    # Q(t) = c prod(a_k - t): build coefficients
    coeffs = [mpc(c)]  # constant-first, will reverse at the end
    for ak in a:
        new = [mpc(0)] * (len(coeffs) + 1)
        for i, v in enumerate(coeffs):
            new[i] += v * mpc(ak)
            new[i + 1] += -v
        coeffs = new
    while len(coeffs) < r + 1:
        coeffs.append(mpc(0))
    coeffs[r] += mpc(z)
    return polyroots(list(reversed(coeffs)), maxsteps=200, extraprec=200)


def predicted(r, j):
    om = exp(2j * pi * j / r) * exp(1j * pi / r)
    return (cos(pi / r) - om.real) / sin(pi / r)


print("upper-endpoint linear gap: measured rate against (cos(pi/r) - Re omega_j)/sin(pi/r)")
print()
worst = mpf(0)
zero_worst = mpf(0)
for a, c, r in PENCILS:
    S = sum(1 / ak for ak in a)
    b = pi / r
    print(f"a={[float(x) for x in a]} c={float(c)} r={r}   sum 1/a_k = {float(S):.6f}")
    for delta in [mpf('1e-4'), mpf('1e-5'), mpf('1e-6')]:
        theta = b - delta
        tau = branch_tau(a, c, r, theta)
        assert tau is not None and tau > 0, "no branch radius found"
        tminus = tau * exp(-1j * theta)
        z = (-q_eval(a, c, tminus) / tminus ** r).real
        tplus = tau * exp(1j * theta)
        # the r roots nearest the origin
        all_rts = den_roots(a, c, r, z)
        # the branch's DEFINING property, checked rather than assumed: t_+ must be a
        # minimum-modulus zero of the pencil THIS candidate induces.  A selector that
        # merely brackets a sign change of Im(Q/t^r) can return a different zero and
        # still produce a clean-looking coefficient, so the selector is validated here
        # rather than trusted.
        tau_min = min(abs(w) for w in all_rts)
        assert fabs(tau_min - tau) < mpf('1e-20'), (
            f"branch selector wrong: tau={tau} but min |root| = {tau_min}")
        rts = sorted(all_rts, key=lambda w: abs(w))[:r]
        line = []
        for j in range(r):
            target = exp(2j * pi * j / r) * tplus
            g = min(rts, key=lambda w: abs(w - target))
            measured = (abs(g) / tau - 1) / delta
            pred = predicted(r, j)
            err = fabs(measured - pred)
            line.append((j, measured, pred, err))
        for j, measured, pred, err in line:
            tag = "  (principal)" if j == 0 or j == r - 1 else ""
            print(f"   delta={float(delta):.0e} j={j}: measured={float(measured):+.6f} "
                  f"predicted={float(pred):+.6f} err={float(err):.2e}{tag}")
            if j == 0 or j == r - 1:
                zero_worst = max(zero_worst, fabs(pred))
                assert err < mpf('1e-2'), f"principal index {j} off by {float(err)}"
            else:
                assert pred > 0, f"retained index {j} has non-positive rate {float(pred)}"
                assert err < mpf('5e-2') * fabs(pred) + mpf('1e-3'), \
                    f"rate mismatch at j={j}: {float(measured)} vs {float(pred)}"
            worst = max(worst, err)
    print()

print(f"worst |measured - predicted| over all pencils, deltas and indices: {float(worst):.3e}")
print(f"worst |predicted| at the two principal indices (must be 0): {float(zero_worst):.3e}")
assert zero_worst < mpf('1e-30'), "principal indices must have coefficient exactly 0"
print()
print("PASS  check_upper_linear_gap")
