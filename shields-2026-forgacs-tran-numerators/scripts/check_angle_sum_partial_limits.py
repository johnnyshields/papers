r"""Paper section `sec:dominance` (The weighted dominance bound).

The six limits the whole collar chain now rests on, and the one nonvanishing.

The chain reducing `eq:phase-derivative-bound` on the collar back to the pencil
has been driven down to arithmetic: `\tau'` and `\tau''` are quotients built
from the partials of the angle sum, so their convergence at the lower endpoint
is algebra of limits once those partials converge and the `\tau`-partial's
limit is nonzero.  Nothing above that line is analysis; everything below it is
`ftAngle`.  So the entire chain rests on:

  (i)   the six partial sums of `\sum_k \theta_k(\tau,\theta)` -- two first
        order, four second -- converging as `\theta \downarrow 0` along the
        branch; and
  (ii)  `\lim S_\tau \ne 0`, which is what makes the quotients quotients.

Neither had been measured.  Both are checked here, and (ii) turns out to be
structural rather than numerical: `S_\tau = -\sum_k \sin^2\theta_k \, a_k /
(\tau^2\sin\theta)` is a sum of terms of ONE sign, so it cannot vanish for a
positive pencil at any `\theta \in (0,\pi)` -- no case analysis, and the limit
inherits the sign.

The partials are taken on `ftAngle` itself, which is analytic in both
arguments, never on the branch radius -- that comes from bisection and is a
step function at bisection resolution, where a numerical derivative returns
noise.  `\tau` enters only as the point of evaluation.

mpmath only.
"""

from mpmath import mp, mpf, pi, atan, sin, cos, fabs, diff

mp.dps = 60
LOWEST = mpf(2) ** -11


def ft_arccot(x):
    return pi / 2 - atan(x)


def ft_angle(a, tau, s):
    return ft_arccot(cos(s) / sin(s) - a / (tau * sin(s)))


def ft_angle_sum(A, tau, s):
    return sum(ft_angle(a, tau, s) for a in A)


def ft_tau(A, r, s):
    l = len(A) - 1
    target = r * s + l * pi

    def h(x):
        return ft_angle_sum(A, x, s) - target

    lo, hi = mpf(10) ** -10, mpf(10) ** 10
    assert h(lo) > 0 > h(hi), f"the branch is not bracketed at theta = {s}"
    for _ in range(400):
        mid = (lo + hi) / 2
        if h(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


# The six partials, taken on the analytic angle sum by exact differentiation
# in each argument separately.  Named as the chain names them.
def partials(A, tau, s):
    f = lambda t, x: ft_angle_sum(A, t, x)
    S_t = diff(lambda t: f(t, s), tau)
    S_a = diff(lambda x: f(tau, x), s)
    S_tt = diff(lambda t: f(t, s), tau, 2)
    S_aa = diff(lambda x: f(tau, x), s, 2)
    S_ta = diff(lambda t: diff(lambda x: f(t, x), s), tau)
    S_at = diff(lambda x: diff(lambda t: f(t, x), tau), s)
    return {"S_t": S_t, "S_a": S_a, "S_tt": S_tt, "S_aa": S_aa,
            "S_ta": S_ta, "S_at": S_at}


PENCILS = [
    ("a = (1,2,5), r = 1", [mpf(1), mpf(2), mpf(5)], 1),
    ("a = (1,3,3,8), r = 1", [mpf(1), mpf(3), mpf(3), mpf(8)], 1),
    ("a = (1,2,5), r = 2", [mpf(1), mpf(2), mpf(5)], 2),
]

# The six do NOT all converge to nonzero values, and asserting a drift is the
# wrong test: three of them tend to ZERO linearly in theta, so an absolute
# bound on their movement measures the ladder's depth.  Each is asserted
# against its own closed form instead.
#
#   S_a  -> r            S_ta = S_at -> -Sigma'(t_a)        S_t, S_tt, S_aa -> 0
#
# The vanishing ones matter as much as the others: `tau' = -(S_a - r)/S_t` has
# BOTH parts tending to zero, so it is a 0/0 whose value comes from the rates
# and not from the limits -- which is why the quotient tends to 0 (measured
# elsewhere as tau'(0+) = 0) while neither part does anything on its own.
print("PASS  (i) each partial against its own closed form:")


def sigma_deriv(A, s):
    return sum(a / (a - s) ** 2 for a in A)


worst = mpf(0)
worst_name = None
for name, A, r in PENCILS:
    ta = ft_tau(A, r, LOWEST / 64)
    near = partials(A, ft_tau(A, r, LOWEST), LOWEST)
    finer = partials(A, ft_tau(A, r, LOWEST / 8), LOWEST / 8)
    # S_a -> r
    d = fabs(near["S_a"] - r) / max(mpf(r), mpf(1))
    assert d < mpf(10) ** -4, f"S_a is {near['S_a']}, not r = {r}, on {name}"
    worst, worst_name = (d, f"S_a on {name}") if d > worst else (worst, worst_name)
    # S_ta = S_at -> -Sigma'(t_a), and the two mixed partials agree
    assert fabs(near["S_ta"] - near["S_at"]) < mpf(10) ** -20, "mixed partials differ"
    pred = -sigma_deriv(A, ta)
    d = fabs(near["S_ta"] - pred) / fabs(pred)
    assert d < mpf(10) ** -4, (
        f"S_ta is {near['S_ta']}, predicted -Sigma'(t_a) = {pred}, on {name}")
    worst, worst_name = (d, f"S_ta on {name}") if d > worst else (worst, worst_name)
    # S_t, S_tt, S_aa -> 0, linearly: halving theta must halve them
    for k in ("S_t", "S_tt", "S_aa"):
        ratio = fabs(finer[k]) / fabs(near[k])
        assert fabs(ratio - mpf(1) / 8) < mpf(1) / 100, (
            f"{k} is not linear in theta on {name}: ratio {ratio} over an "
            f"eightfold refinement, expected 1/8")
    print(f"        {name:<22} S_a -> {mp.nstr(near['S_a'], 8)},  "
          f"S_ta -> {mp.nstr(near['S_ta'], 8)},  S_t/S_tt/S_aa -> 0 linearly")

print(f"PASS  (i) worst relative deviation from a closed form "
      f"{mp.nstr(worst, 4)} ({worst_name}); the three vanishing partials halve "
      f"when theta halves, so their rate is asserted rather than their value")

# (ii) the tau-partial cannot vanish, and the reason is a sign not a value.
print("PASS  (ii) the tau-partial is a one-signed sum, so it cannot vanish:")
for name, A, r in PENCILS:
    for j in range(0, 5):
        s = LOWEST * mpf(4) ** j
        tau = ft_tau(A, r, s)
        terms = [-(sin(ft_angle(a, tau, s)) ** 2 * a / (tau ** 2 * sin(s)))
                 for a in A]
        assert all(t < 0 for t in terms), f"a term changed sign on {name}"
        closed = sum(terms)
        num = diff(lambda t: ft_angle_sum(A, t, s), tau)
        assert fabs(closed - num) / fabs(closed) < mpf(10) ** -20, (
            f"the closed form disagrees with the derivative on {name}: "
            f"{closed} vs {num}")
        assert closed < 0
    print(f"        {name:<22} S_tau = {mp.nstr(closed, 8)} < 0, every term "
          f"negative")
print("PASS  (ii) S_tau = -sum_k sin^2(theta_k) a_k / (tau^2 sin theta), a sum "
      "of terms of ONE sign for a positive pencil at any theta in (0, pi) -- "
      "so it is nonzero structurally and its limit inherits the sign, with no "
      "case analysis and nothing measured")
# --- (iii) the rates are REGIME-SPECIFIC, and the split is at rho ---------
# Everything above is measured at pencils with a SIMPLE smallest zero, where
# the endpoint sits strictly inside the first gap and no a_k equals tau.  There
# every angle tends to 0 or pi, sin^2(theta_k) -> 0, and S_t vanishes linearly.
#
# At a REPEATED minimum that is false, and not by a little.  The rho collision
# members have a_k = tau EXACTLY at the endpoint, so their angle tends to pi/2
# and sin^2(theta_k) -> 1 rather than 0: S_t DIVERGES like -rho/theta.  So the
# linear rate above is a fact about the gap regime, not about the angle sum,
# and asserting it everywhere fails by a factor of two per rung.
#
# It also breaks the closed-form collapse rate `theta_k/theta -> t_a/(t_a-a_k)`,
# whose denominator is exactly zero on those members -- an `x/0 = 0` that would
# return a finite plausible rate for an angle that does not collapse at all.
print("PASS  (iii) at a repeated minimum the rate is different in kind:")
for name, A, r in (("a = (1,1,3), rho = 2", [mpf(1), mpf(1), mpf(3)], 1),
                   ("a = (1,1,1,4), rho = 3", [mpf(1)] * 3 + [mpf(4)], 1)):
    rho = sum(1 for x in A if x == min(A))
    prods = []
    for j in range(0, 4):
        s = LOWEST * mpf(2) ** j
        tau = ft_tau(A, r, s)
        St = diff(lambda t: ft_angle_sum(A, t, s), tau)
        prods.append(s * St)
    # theta * S_t settles instead of S_t itself -- the signature of a 1/theta
    # divergence rather than a linear vanishing
    drift = fabs((prods[0] - prods[1]) / prods[0])
    assert drift < mpf(1) / 50, f"theta*S_t has not settled on {name}: {drift}"
    assert prods[0] < 0
    # and the collapse rate's denominator vanishes on the collision members
    ta = ft_tau(A, r, LOWEST / 64)
    close = min(fabs(ta - a) for a in A)
    assert close < mpf(10) ** -3, (
        f"no a_k is at the endpoint on {name} -- this is not the repeated case")
    print(f"        {name:<24} theta*S_t -> {mp.nstr(prods[0], 7)}, so S_t "
          f"diverges like 1/theta; min_k |t_a - a_k| = {mp.nstr(close, 4)}")
print("PASS  (iii) so S_t -> 0 linearly is the SIMPLE-minimum regime only.  At "
      "a repeated minimum the collision members sit at a_k = tau, their angle "
      "tends to pi/2 rather than to 0 or pi, and S_t diverges -- which also "
      "makes t_a/(t_a - a_k) a division by zero on exactly those members")

print("ALL PASS")
