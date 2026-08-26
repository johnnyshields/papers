"""`sec:consequences` / `cor:differential`: the domination bound that justifies
differentiating `eq:fixed-sum` under the integral.

The proof of `cor:differential` differentiates `Phi_m(d) = kappa * E Ghat(Q_d)`
twice at `d = 0`, and needs the interchange.  `g_d` is singular at BOTH ends of
`(0, 1/4)` and the two ends are controlled by different estimates, so the
domination is a two-endpoint argument:

  * as `q -> 0`: `ell(q) = log(1/q) + O(q)`, `cosh(d ell(q)) = O(q^{-|d|})`, and
    `g_d` with its first two `d`-derivatives is `O(q^{mu-1-d0} log^2(1/q))`
    uniformly for `|d| <= d0 < mu`;
  * as `q -> 1/4`: `ell(q) = O(sqrt(1-4q))`, and the same quantities are
    `O((1-4q)^{-1/2})`.

Both majorants integrate, and NEITHER covers the other end -- which is the point,
and is asserted here rather than assumed: `check_second_endpoint_needed` shows
the `q -> 0` majorant failing near `1/4` by a factor that grows without bound
(1143 at `1-4q = 1e-8`, and rising), so a one-endpoint argument is not merely
incomplete but false.  `|d| <= d0 < mu` is separately load-bearing: it is what
puts the first exponent above `-1`, and at `d0 = mu` that majorant diverges.

The logarithmic factors do NOT bind at either end: near `0` they are dominated
by `q^{-eps}` for every `eps > 0`, so the power alone decides integrability.

`check_structural.py` owns `Phi''(0) = kappa * Cov(...)` and its sign;
`verify_monotonicity_lemmas.py` owns the closed form of `g_d` itself.  What is
new here is the interchange hypothesis.

Two measurement traps:

  * `ell` must be rationalized.  The literal `log((1+r)/(1-r))` with
    `r = sqrt(1-4q)` cancels catastrophically -- `1 - r` is `O(q)` against
    operands of size `1` -- and the error swamps the `O(q)` term being measured,
    reading the ratio as `4.06e6` instead of `2`.
  * `cosh(d ell(q)) q^{|d|}` approaches `1/2` from ABOVE at small `d` and from
    BELOW at larger `d`, so the assertion is on the distance to `1/2` and never
    on the direction.

mpmath at 40 digits; no float64 anywhere.
"""

from mpmath import mp, mpf, sqrt, log, cosh, beta, quad, diff

mp.dps = 40

QUARTER = mpf(1) / 4


def ell(q):
    """`ell(q) = log(p_+/p_-)`, the coordinate of `lem:beta-order`, rationalized."""
    root = sqrt(1 - 4 * q)
    return log((1 + root) ** 2 / (4 * q))


def g(q, s, d):
    """The density of `Q_d` from the proof of `lem:beta-order`."""
    return (2 / beta(s / 2 + d, s / 2 - d)
            * q ** (s / 2 - 1) * (1 - 4 * q) ** mpf('-0.5') * cosh(d * ell(q)))


def check_ell_expansion():
    """`ell(q) = log(1/q) + O(q)`: the difference over `q` is bounded, and is 2."""
    ratios = []
    for e in range(3, 25):
        q = mpf(10) ** (-e)
        ratios.append(abs(ell(q) - log(1 / q)) / q)
    assert max(ratios) < 5, max(ratios)
    assert abs(max(ratios) - min(ratios)) < mpf('1e-2'), (min(ratios), max(ratios))
    print(f"PASS  `cor:differential`: ell(q) = log(1/q) + O(q);"
          f" (ell - log(1/q))/q -> {mp.nstr(ratios[-1], 8)}")


def check_cosh_is_a_power():
    """`cosh(d ell(q)) = O(q^{-|d|})` and not `o()` of it: two-sided, to 1e-24.

    That two-sidedness is what `O` asserts here, and it is the whole point of
    the claim: the obstruction is this power, not the logarithm.  The limit is
    `1/2`, since
    `cosh(d ell) ~ (1/2) exp(d ell) = (1/2)(p_+/p_-)^d ~ (1/2) q^{-d}`.
    """
    for d in ('0.1', '0.6', '1.7'):
        d = mpf(d)
        vals = [cosh(d * ell(mpf(10) ** (-e))) * mpf(10) ** (-e * d)
                for e in (8, 12, 16, 20, 24)]
        assert all(mpf('0.4') < v < mpf('0.75') for v in vals), (d, vals)
        gaps = [abs(v - mpf('0.5')) for v in vals]
        assert all(a > b for a, b in zip(gaps, gaps[1:])), (d, vals)
        print(f"PASS  `cor:differential`: cosh(d*ell(q)) q^|d| in"
              f" ({mp.nstr(min(vals), 6)}, {mp.nstr(max(vals), 6)}) down to q = 1e-24,"
              f" falling to 1/2, at d = {mp.nstr(d, 3)}  (a power, not a log)")


def check_ell_at_the_far_endpoint():
    """`ell(q) = O(sqrt(1-4q))` as `q -> 1/4`; the ratio tends to exactly 2."""
    ratios = []
    for e in (2, 4, 8, 12, 16):
        eps2 = mpf(10) ** (-e)
        q = (1 - eps2) / 4
        ratios.append(ell(q) / sqrt(eps2))
    assert all(mpf('1.9') < r < mpf('2.1') for r in ratios), ratios
    assert abs(ratios[-1] - 2) < abs(ratios[0] - 2), ratios
    print(f"PASS  `cor:differential`: ell(q)/sqrt(1-4q) -> {mp.nstr(ratios[-1], 8)}"
          f" as q -> 1/4, so ell(q) = O(sqrt(1-4q)) there")


def _sup_ratio(mu, d0, points, majorant):
    """sup over `points` and over `|d| <= d0` of (|g_d| + |g_d'| + |g_d''|)/majorant."""
    s = 2 * mu
    worst = mpf(0)
    for q in points:
        maj = majorant(q)
        for k in range(-3, 4):
            d = d0 * mpf(k) / 3
            val = (abs(g(q, s, d))
                   + abs(diff(lambda t: g(q, s, t), d))
                   + abs(diff(lambda t: g(q, s, t), d, 2)))
            worst = max(worst, val / maj)
    return worst


def _near_zero():
    return [mpf(10) ** (-e) for e in (2, 4, 6, 9, 12, 15, 18)]


def _near_quarter():
    return [(1 - mpf(10) ** (-e)) / 4 for e in (1, 2, 3, 5, 8, 12)]


def check_uniform_domination():
    """Both endpoint majorants, uniformly on `|d| <= d0`, and both integrable."""
    for mu, d0 in ((mpf(1), mpf('0.6')), (mpf('2.5'), mpf('2.0')),
                   (mpf('0.4'), mpf('0.3'))):
        r0 = _sup_ratio(mu, d0, _near_zero(),
                        lambda q: q ** (mu - 1 - d0) * log(1 / q) ** 2)
        r4 = _sup_ratio(mu, d0, _near_quarter(),
                        lambda q: (1 - 4 * q) ** mpf('-0.5'))
        assert r0 < mpf('1e4'), (mu, d0, r0)
        assert r4 < mpf('1e4'), (mu, d0, r4)
        assert mu - 1 - d0 > -1, (mu, d0)
        i0 = quad(lambda q: q ** (mu - 1 - d0) * log(1 / q) ** 2, [0, QUARTER])
        i4 = quad(lambda q: (1 - 4 * q) ** mpf('-0.5'), [0, QUARTER])
        assert 0 < i0 < mp.inf and 0 < i4 < mp.inf, (mu, d0, i0, i4)
        print(f"PASS  `cor:differential`: at mu = {mp.nstr(mu, 3)},"
              f" d0 = {mp.nstr(d0, 3)}, |g_d| + |d_d g_d| + |d_d^2 g_d| <="
              f" {mp.nstr(r0, 4)} q^(mu-1-d0) log^2(1/q) near 0 (integral"
              f" {mp.nstr(i0, 6)}) and <= {mp.nstr(r4, 4)} (1-4q)^(-1/2) near 1/4"
              f" (integral {mp.nstr(i4, 6)})")


def check_second_endpoint_needed():
    """The `q -> 0` majorant is FALSE near `1/4`, so one endpoint does not suffice.

    This is the assertion that the two-endpoint structure of the proof is
    load-bearing rather than fastidious: the near-zero bound is not merely
    uninformative at the far end, it is violated there by a ratio that grows
    without bound.
    """
    mu, d0 = mpf(1), mpf('0.6')
    ratios = []
    for e in (2, 4, 6, 8):
        q = (1 - mpf(10) ** (-e)) / 4
        maj = q ** (mu - 1 - d0) * log(1 / q) ** 2
        ratios.append(g(q, 2 * mu, d0) / maj)
    assert ratios[-1] > 100, ratios
    assert all(a < b for a, b in zip(ratios, ratios[1:])), ratios
    print(f"PASS  `cor:differential`: the q->0 majorant FAILS near 1/4 -- ratio"
          f" {mp.nstr(ratios[0], 4)} -> {mp.nstr(ratios[-1], 6)} and rising, so the"
          f" second endpoint estimate is load-bearing, not decorative")


def check_compactness_load_bearing():
    """At `d0 = mu` the exponent is exactly `-1` and the majorant diverges.

    So `|d| <= d0 < mu` in the proof is a hypothesis, not decoration.
    """
    mu = mpf(1)
    assert mu - 1 - mu == -1
    tail = quad(lambda q: q ** mpf(-1), [mpf('1e-12'), QUARTER])
    assert tail > 20, tail
    print(f"PASS  `cor:differential`: at d0 = mu the exponent is exactly -1 and the"
          f" majorant diverges (int_1e-12^1/4 q^-1 = {mp.nstr(tail, 6)}),"
          f" so |d| <= d0 < mu is load-bearing")


if __name__ == '__main__':
    check_ell_expansion()
    check_ell_at_the_far_endpoint()
    check_cosh_is_a_power()
    check_uniform_domination()
    check_second_endpoint_needed()
    check_compactness_load_bearing()
    print("ALL PASS")
