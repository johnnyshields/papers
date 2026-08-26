"""Is `hamp₁` satisfiable at the upper endpoint for `r >= 2`?  (`sec:dominance`,
`thm:weighted-dominance`, the upper-endpoint amplitude floor.)

The binder asks for constants `A_1 > 0` and `p_1` in N with

    A_1 * eta^p_1  <=  |W(b - eta)|      for all small eta > 0,   b = pi/r,

where `W = B(gamma)/D_t(gamma)` is the principal amplitude and `gamma(theta) =
tau(theta) e^{i theta}` is the branch.  This is checked for SATISFIABILITY before
anything is proved about it, because the upper endpoint at `r >= 2` is where the
premise is in doubt: `tau -> 0` there, `tau^r z` stays finite so `z ~ C/tau^r`, and
therefore

    D_t(gamma) = Q'(gamma) + z r gamma^{r-1} ~ C r / tau

DIVERGES.  So `|W| ~ |B(0)| tau / (C r)` vanishes, and the only question is whether
it vanishes no faster than a power of `eta`.  If `tau` decayed faster than every
power of `eta` --- exponentially, say --- then NO natural `p_1` would work and the
binder would be unsatisfiable: a hypothesis nothing can discharge, which builds
green and makes the theorem vacuous over its whole upper range.

Three assertions, each failing loudly:

1.  `tau(b - eta)` follows a power law: the local exponent `d log tau / d log eta`
    converges as `eta -> 0` rather than drifting to zero or diverging.
2.  `|W(b - eta)|` does too, and its exponent is the same as `tau`'s --- which is
    the statement that `B(gamma)` and the rest of `D_t` contribute no vanishing
    factor of their own.
3.  The binder is met at `p_1 = ceil(exponent)` with a positive `A_1`: the ratio
    `|W| / eta^{p_1}` is bounded below over three decades of `eta`.

mpmath only.
"""

import math

import mpmath as mp

mp.mp.dps = 40


def q_eval(c, a, t):
    v = mp.mpc(c)
    for ak in a:
        v = v * (mp.mpf(ak) - t)
    return v


def dq_eval(c, a, t):
    """Q'(t) by the product rule, without forming coefficients."""
    total = mp.mpc(0)
    for j in range(len(a)):
        term = mp.mpc(c) * (-1)
        for k in range(len(a)):
            if k != j:
                term = term * (mp.mpf(a[k]) - t)
        total += term
    return total


def imz(c, a, r, tau, theta):
    """`sin(arg z)` rather than `Im z`: near the upper endpoint `|z|` runs over many
    decades, so an absolute tolerance on `Im z` is meaningless while the normalized
    form stays O(1) and has the same zeros."""
    t = mp.mpf(tau) * mp.exp(1j * theta)
    w = -q_eval(c, a, t) / t ** r
    return mp.im(w) / abs(w)


def branch_tau(c, a, r, theta, x1):
    """Smallest positive tau on which z is real: the minimum-modulus branch."""
    N = 4000
    prev_tau = mp.mpf(x1) * mp.mpf("1e-9")
    prev = imz(c, a, r, prev_tau, theta)
    for k in range(1, N + 1):
        cur_tau = mp.mpf(x1) * (mp.mpf(k) / N)
        cur = imz(c, a, r, cur_tau, theta)
        if prev * cur < 0:
            return mp.findroot(lambda s: imz(c, a, r, s, theta), (prev_tau, cur_tau),
                               solver="bisect", tol=mp.mpf(10) ** (-30), maxsteps=400)
        prev_tau, prev = cur_tau, cur
    raise AssertionError(f"no branch radius found at theta={theta}")


def amplitude(c, a, r, bcoef, theta, x1):
    tau = branch_tau(c, a, r, theta, x1)
    g = tau * mp.exp(1j * theta)
    z = -q_eval(c, a, g) / g ** r
    assert abs(mp.im(z)) < mp.mpf(10) ** (-20) * max(1, abs(z)), "z not real on the branch"
    z = mp.re(z)
    dt = dq_eval(c, a, g) + z * r * g ** (r - 1)
    bval = mp.mpc(0)
    for k, coeff in enumerate(bcoef):
        bval += mp.mpf(coeff) * g ** k
    return tau, abs(bval / dt), abs(dt)


def local_exponent(f, etas):
    """d log f / d log eta between consecutive samples."""
    out = []
    for i in range(len(etas) - 1):
        out.append((mp.log(f[i + 1]) - mp.log(f[i])) / (mp.log(etas[i + 1]) - mp.log(etas[i])))
    return out


def main():
    cases = [
        # c, roots a, r, B coefficients (ascending); B(0) != 0 in each
        (1.0, [1.0, 1.0, 1.0, 2.0], 2, [1.0]),
        (1.0, [1.0, 1.0, 1.0, 2.0], 3, [1.0, 0.5]),
        (2.5, [0.4, 0.4, 1.7], 2, [3.0, 0.0, 1.0]),
        (0.8, [2.0, 2.0, 2.0, 5.0], 4, [1.0, -0.25]),
    ]
    for c, a, r, bcoef in cases:
        x1 = min(a)
        b = mp.pi / r
        etas = [mp.mpf(10) ** (-k) for k in range(3, 8)]
        taus, amps, dts = [], [], []
        for eta in etas:
            tau, amp, dt = amplitude(c, a, r, bcoef, b - eta, x1)
            taus.append(tau)
            amps.append(amp)
            dts.append(dt)

        # the premise the whole question rests on: D_t diverges
        assert dts[-1] > dts[0], f"|D_t| did not grow toward the endpoint: {dts}"

        # 1. tau follows a power law
        se = local_exponent(taus, etas)
        assert abs(se[-1] - se[-2]) < mp.mpf("2e-2"), f"tau exponent drifting: {se}"
        s = se[-1]
        assert mp.mpf("0.05") < s < 10, f"tau exponent out of range: {s}"

        # 2. |W| follows the same power law
        ae = local_exponent(amps, etas)
        assert abs(ae[-1] - ae[-2]) < mp.mpf("2e-2"), f"|W| exponent drifting: {ae}"
        assert abs(ae[-1] - s) < mp.mpf("3e-2"), f"|W| exponent {ae[-1]} != tau's {s}"

        # 3. the binder is met at the smallest natural `p_1 >= s`, with a positive
        # `A_1`.  `|W|/eta^{p_1}` settles to a constant when `p_1 = s` and GROWS
        # when `p_1 > s` --- the binder holding with room, not a failure of the
        # fit --- so what is asserted is that the ratio does not DECAY, which
        # covers both regimes and is exactly the satisfiability content.
        sf = float(s)
        p1 = max(1, int(round(sf)) if abs(sf - round(sf)) < 1e-6
                 else int(math.ceil(sf)))
        ratios = [amps[i] / etas[i] ** p1 for i in range(len(etas))]
        A1 = min(ratios)
        assert A1 > 0, "amplitude floor degenerate"
        assert ratios[-1] > 0, "ratio degenerate"
        assert ratios[-1] >= ratios[0] / 2, f"ratio decaying toward the endpoint: {ratios}"
        for i in range(len(etas)):
            assert A1 * etas[i] ** p1 <= amps[i] * (1 + mp.mpf("1e-30")), "floor violated"

        print(f"c={c} a={a} r={r}: tau~eta^{mp.nstr(s, 5)}  |W|~eta^{mp.nstr(ae[-1], 5)}  "
              f"|D_t| {mp.nstr(dts[0], 4)}->{mp.nstr(dts[-1], 4)}  "
              f"p1={p1} A1={mp.nstr(A1, 5)}")

    print("PASS: check_upper_amplitude_floor")


if __name__ == "__main__":
    main()
