"""Is the upper endpoint's large-parameter circle SATISFIABLE?  (`sec:dominance`,
the `_1` retained-cluster group of `thm:weighted-dominance`.)

`EndpointSeparation`'s upper circle is conditioned on `ftUpperWindow <= |z|`: the
pencil's own term `z t^r` must dominate `Q` on a circle inside the smallest zero.
Whether a caller can ever discharge that is a question about the SPECTRAL
PARAMETER along the branch, and it is the only thing checked here.

  * `r >= 2`: `|z| -> infinity`, so every threshold is eventually cleared.
  * `r = 1`:  `|z|` tends to a FINITE limit, so no threshold above it is ever
    cleared and the hypothesis is unmeetable.

That second line is why the construction is scoped rather than stated for all `r`.
A circle stated for all `r` and dischargeable at none of `r = 1` would build green
and be vacuous there --- a hypothesis nothing can satisfy, which is not a hard
lemma but an empty one.

The RADIUS half of the same dichotomy --- `tau -> 0` at `r >= 2` against a positive
limit at `r = 1`, with the deficit equation the limit solves --- is
`check_upper_endpoint_r_one.py` (V1 and V4) and is not repeated.  Nothing there
asserts anything about `z`, which is the half the circle actually rests on.

mpmath only.
"""

import mpmath as mp

mp.mp.dps = 40


def q_eval(c, a, t):
    v = mp.mpc(c)
    for ak in a:
        v = v * (mp.mpf(ak) - t)
    return v


def imz(c, a, r, tau, theta):
    t = mp.mpf(tau) * mp.exp(1j * theta)
    w = -q_eval(c, a, t) / t ** r
    return mp.im(w) / abs(w)


def branch(c, a, r, theta, x1):
    """Smallest positive tau on which z is real, and that z."""
    N = 4000
    prev_tau = mp.mpf(x1) * mp.mpf("1e-9")
    prev = imz(c, a, r, prev_tau, theta)
    for k in range(1, N + 1):
        cur_tau = mp.mpf(x1) * (mp.mpf(k) / N)
        cur = imz(c, a, r, cur_tau, theta)
        if prev * cur < 0:
            tau = mp.findroot(lambda s: imz(c, a, r, s, theta), (prev_tau, cur_tau),
                              solver="bisect", tol=mp.mpf(10) ** (-30), maxsteps=400)
            t = tau * mp.exp(1j * theta)
            return tau, mp.re(-q_eval(c, a, t) / t ** r)
        prev_tau, prev = cur_tau, cur
    raise AssertionError(f"no branch radius at theta={theta}, r={r}")


def sweep(c, a, r):
    x1 = min(a)
    b = mp.pi / r
    out = []
    for k in range(3, 8):
        eta = mp.mpf(10) ** (-k)
        out.append(branch(c, a, r, b - eta, x1))
    return x1, out


def main():
    upper = [
        (1.0, [1.0, 1.0, 1.0, 2.0], 2),
        (1.0, [1.0, 1.0, 1.0, 2.0], 3),
        (0.8, [2.0, 2.0, 2.0, 5.0], 4),
    ]
    for c, a, r in upper:
        x1, s = sweep(c, a, r)
        taus = [t for t, _ in s]
        zs = [abs(z) for _, z in s]
        # the radius half is `check_upper_endpoint_r_one.py`; only `z` is asserted here
        assert zs[-1] > zs[0] * 100, f"|z| not diverging at r={r}: {zs}"
        assert zs[-1] > mp.mpf(10) ** 10, f"|z| not clearing a threshold at r={r}: {zs[-1]}"
        print(f"c={c} a={a} r={r}: tau {mp.nstr(taus[0], 5)}->{mp.nstr(taus[-1], 5)}  "
              f"|z| {mp.nstr(zs[0], 5)}->{mp.nstr(zs[-1], 5)}   (threshold clearable)")

    for c, a in [(1.0, [1.0, 1.0, 1.0, 2.0]), (2.5, [0.4, 0.4, 1.7])]:
        x1, s = sweep(c, a, 1)
        taus = [t for t, _ in s]
        zs = [abs(z) for _, z in s]
        assert max(zs) < 1000 * (min(zs) + mp.mpf("1e-30")), f"|z| diverged at r=1: {zs}"
        assert max(zs) < mp.mpf(10) ** 4, f"|z| unbounded at r=1: {max(zs)}"
        print(f"c={c} a={a} r=1: tau {mp.nstr(taus[0], 5)}->{mp.nstr(taus[-1], 5)}  "
              f"|z| {mp.nstr(zs[0], 5)}->{mp.nstr(zs[-1], 5)}   (threshold unmeetable)")

    print("PASS: check_upper_endpoint_regimes")


if __name__ == "__main__":
    main()
