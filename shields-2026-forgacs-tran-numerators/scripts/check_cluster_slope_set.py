"""The lower cluster's slopes are the alpha_j (`eq:lower-cluster-expansion`).

At the lower endpoint the rho zeros of the pencil that collide at x_1 leave it
linearly in the angle,

    t_j(delta) = x_1 + alpha_j delta + o(delta),
    alpha_j = -x_1 w_j / sin(pi/rho),   w_j = exp((2j-1) pi i / rho),

with j = 0 the principal upper branch.  This solves the branch numerically at a
real pencil and checks three things, each with a failing assert:

1.  The principal branch's own slope is alpha_0.
2.  The rho slopes, as a SET, are exactly {alpha_0, ..., alpha_{rho-1}}.
3.  The matching is a bijection: no alpha is hit twice and none is missed.

Point 2 is what a formalization has to be careful with.  A chart producing the
cluster labels its members by rho-th roots of unity of its OWN choosing --- the
chart's zeta_j --- and there is no reason for the chart's index 0 to be the
principal branch.  So the slope of chart member j is alpha_{(j - j_p) mod rho},
not alpha_j, where j_p is whichever chart index the principal branch turns out to
be.  The two labellings differ by a shift, and a development that identifies them
is stating the residue asymptotics at the wrong alpha for every member.  The
shift itself is algebra --- alpha_0 * zeta_j = alpha_j, so a rotation of the
index set --- and what is checked here is the fact that makes the shift the only
possible discrepancy: the slope SET is exactly the alpha set.

The branch is solved from the definition rather than from the expansion: for each
angle delta, tau is chosen so that z = -Q(tau e^{i delta}) / (tau e^{i delta})^r
is real, which is the branch condition, and the cluster is then read off the
roots of Q + z X^r nearest x_1.

mpmath only.
"""

import mpmath as mp

mp.mp.dps = 50


def q_coeffs(c, a):
    """Q = c prod (a_k - t), monomial basis, highest degree first."""
    coeffs = [mp.mpf(c)]
    for ak in a:
        new = [mp.mpf(0)] * (len(coeffs) + 1)
        for i, p in enumerate(coeffs):
            new[i] += -p
            new[i + 1] += mp.mpf(ak) * p
        coeffs = new
    return coeffs


def q_eval(c, a, t):
    v = mp.mpc(c)
    for ak in a:
        v = v * (mp.mpf(ak) - t)
    return v


def branch_z(c, a, r, delta, x1, rho):
    """tau on the branch at angle delta, and the real spectral parameter there.

    The branch condition is that z = -Q(t)/t^r be real at t = tau e^{i delta}.
    The starting guess is the manuscript's own tau'(0+) = -x_1 cot(pi/rho), which
    is exact to first order and degenerate at rho = 2 (where tau meets the
    endpoint quadratically) --- findroot handles both from the same guess.
    """
    def imz(tau):
        t = mp.mpc(tau) * mp.exp(1j * delta)
        return mp.im(-q_eval(c, a, t) / t ** r)

    guess = mp.mpf(x1) * (1 - mp.cos(mp.pi / rho) / mp.sin(mp.pi / rho) * delta)
    tau = mp.findroot(imz, guess, solver="secant", tol=mp.mpf(10) ** (-40))
    tau = mp.re(tau)
    assert tau > 0, f"branch radius not positive: {tau}"
    t = tau * mp.exp(1j * delta)
    z = -q_eval(c, a, t) / t ** r
    assert abs(mp.im(z)) < mp.mpf(10) ** (-25) * max(1, abs(z)), \
        f"z not real: {mp.im(z)}"
    return tau, mp.re(z), t


def cluster_roots(c, a, r, z, x1, rho):
    coeffs = q_coeffs(c, a)
    n = len(coeffs) - 1
    idx = n - r
    assert 0 <= idx < len(coeffs), "r exceeds deg Q; not this check's case"
    coeffs = list(coeffs)
    coeffs[idx] += z
    rts = mp.polyroots(coeffs, maxsteps=400, extraprec=600)
    rts = sorted(rts, key=lambda t: abs(t - x1))
    return rts[:rho]


def alphas(x1, rho):
    return [-mp.mpf(x1) * mp.exp(1j * (2 * m - 1) * mp.pi / rho)
            / mp.sin(mp.pi / rho) for m in range(rho)]


def main():
    cases = [
        (1.0, [1.0, 1.0, 1.0, 2.0], 1, 3),
        (1.0, [1.0, 1.0, 1.0, 2.0], 2, 3),
        (1.0, [1.0, 1.0, 3.0], 1, 2),
        (0.8, [2.0, 2.0, 2.0, 2.0, 7.0], 1, 4),
    ]
    for c, a, r, rho in cases:
        x1 = min(a)
        assert sum(1 for ak in a if ak == x1) == rho
        al = alphas(x1, rho)
        delta = mp.mpf("1e-4")
        tau, z, tplus = branch_z(c, a, r, delta, x1, rho)
        rts = cluster_roots(c, a, r, z, x1, rho)
        slopes = [(t - x1) / delta for t in rts]

        # 1. the principal branch's slope is alpha_0
        sp = (tplus - x1) / delta
        assert abs(sp - al[0]) < mp.mpf("2e-3") * abs(al[0]), \
            f"principal slope {sp} != alpha_0 {al[0]}"

        # 2 and 3. the slope set is the alpha set, bijectively
        used = {}
        for s in slopes:
            best = min(range(rho), key=lambda m: abs(s - al[m]))
            err = abs(s - al[best]) / abs(al[best])
            assert err < mp.mpf("2e-3"), f"slope {s} matches no alpha (best err {err})"
            assert best not in used, f"alpha_{best} matched twice: not a bijection"
            used[best] = s
        assert len(used) == rho, f"only {len(used)} of {rho} alphas hit"

        print(f"c={c} a={a} r={r} rho={rho}: tau={mp.nstr(tau, 8)} z={mp.nstr(z, 8)} "
              f"principal->alpha_0 ok, slope set = alpha set ({rho} of {rho})")

    print("PASS: check_cluster_slope_set")


if __name__ == "__main__":
    main()
