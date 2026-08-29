"""Is the fixed factor's angle actually non-constant on the arc, and by how much?

`kappa_0` bounds the total variation of a branch of `arg(1/(d_t D))` along the
principal arc.  Every result in the tree produces *some* `kappa_0`; nothing says
it is positive, and at a pencil where `tau` is constant it is exactly zero --
the cofactor's argument does not move at all.  The cubic pencil has non-constant
`tau`, so the question is open there and this settles it.

Subject: `eq:Dprime-identity`, `d_t D = E(gamma)/gamma`, at Q = (1-t)^3, r = 1,
where E = -(1-t)^2 (2t+1) and gamma(theta) = tau(theta) e^{i theta} with
tau(theta) = 1/(2 cos((pi-theta)/3)).

mpmath throughout: the sweep is read off a limit as the excluded end shrinks,
and float64 runs out of digits at about 1e-8, which shows up as the error
turning over rather than continuing to fall.
"""

from mpmath import mp, mpf, mpc, cos, exp, arg, pi, fabs

mp.dps = 50


def tau(theta):
    return 1 / (2 * cos((pi - theta) / 3))


def gamma(theta):
    return mpc(tau(theta)) * exp(mpc(0, 1) * theta)


def E(t):
    return -((1 - t) ** 2) * (2 * t + 1)


def cofactor(theta):
    """d_t D along the arc, = E(gamma)/gamma."""
    return E(gamma(theta)) / gamma(theta)


def sweep(lo, hi, n):
    """Continuous branch of arg(d_t D), accumulated from principal steps."""
    total = mpf(0)
    prev = arg(cofactor(lo))
    lo_val = total
    hi_val = total
    prev_total = total
    for i in range(1, n):
        th = lo + (hi - lo) * mpf(i) / (n - 1)
        cur = arg(cofactor(th))
        step = cur - prev
        while step > pi:
            step -= 2 * pi
        while step < -pi:
            step += 2 * pi
        total += step
        lo_val = min(lo_val, total)
        hi_val = max(hi_val, total)
        prev = cur
        prev_total = total
    return total, hi_val - lo_val


def main():
    eps = mpf(10) ** (-6)
    n = 4001
    total, spread = sweep(eps, pi - eps, n)
    print(f"sweep of arg(d_t D) over (eps, pi-eps), eps = 1e-6: {mp.nstr(total, 15)}")
    print(f"spread (max - min):                                 {mp.nstr(spread, 15)}")

    # the cofactor does not vanish in between, so the angle is defined throughout
    mods = [fabs(cofactor(eps + (pi - 2 * eps) * mpf(i) / 400)) for i in range(401)]
    assert min(mods) > mpf(10) ** (-20), "cofactor vanishes on the open arc"

    # it genuinely moves: kappa_0 cannot be taken to be 0 here
    assert spread > mpf("1e-3"), f"argument looks constant: spread = {spread}"
    assert fabs(total - spread) < mpf("1e-20"), "not monotone, so sweep != variation"

    # and the value is pi/6, read off as the excluded end shrinks
    print()
    print("  epsilon      sweep - pi/6")
    prev_err = None
    for k in range(3, 10):
        e = mpf(10) ** (-k)
        s, _ = sweep(e, pi - e, 4001)
        err = s - pi / 6
        print(f"  1e-{k}       {mp.nstr(err, 6)}")
        if prev_err is not None:
            assert fabs(err) < fabs(prev_err), f"not converging to pi/6 at 1e-{k}"
        prev_err = err
    assert fabs(prev_err) < mpf("1e-8"), f"limit is not pi/6: off by {prev_err}"

    print()
    print("PASS: kappa_0 > 0 at the cubic pencil, and the sweep is pi/6")


if __name__ == "__main__":
    main()
