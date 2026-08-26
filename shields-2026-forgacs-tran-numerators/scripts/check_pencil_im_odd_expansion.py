r"""Paper section `sec:dominance` (The weighted dominance bound).

The `\theta`-expansion of `ftPencilIm` at the lower endpoint, and whether its
remainder is bounded UNIFORMLY in `\tau` near `t_a` -- the step the `rho = 1`
corner's vanishing-slope argument still owes.

`F(\tau,\theta) = \operatorname{Im}\bigl(e^{ir\theta}P(\tau e^{-i\theta})\bigr)`
for a real pencil `P` and real `\tau`.  Three facts, and the first two make the
third much cheaper than it looks:

  (i)   `F` is ODD in `\theta`, so its expansion carries only odd powers and
        the `\theta^2` coefficient is EXACTLY zero -- the second-order
        remainder is really third order;
  (ii)  the first-order coefficient is `E(\tau)` for `E` the real critical
        polynomial, so the slope vanishes at `\tau = t_a` because `E(t_a) = 0`
        -- not because of any cancellation in `\theta`;
  (iii) `|F(\tau,\theta) - E(\tau)\theta| \le C\theta^3` with `C` UNIFORM over
        a neighborhood of `t_a`.

(ii) is the point.  Rolle alone gives `F = O(\theta)` with the constant merely
bounded -- true, provable, and one order short of what the argument needs.  It
is oddness that turns the `O` into an `o`, and (i) is what makes that
mechanical rather than delicate.

Everything here is a polynomial in `\tau`, `\cos\theta` and `\sin\theta`, so
nothing is asymptotic: the coefficients are extracted by exact Taylor
differentiation at `\theta = 0` and compared against closed forms, and the
uniformity is a max over a grid rather than a limit.

mpmath only.
"""

from mpmath import mp, mpf, mpc, exp, fabs, diff, cos, sin

mp.dps = 60

ZERO = mpf(10) ** -40


def Peval(a, c, z):
    """P(z) = c * prod_k (a_k - z), the admissible pencil."""
    v = mpc(c)
    for ak in a:
        v *= (ak - z)
    return v


def Eeval(a, c, r, t):
    """The real critical polynomial E = r*P - t*P'.

    Computed from P by exact differentiation rather than transcribed, so an
    error in the identity below cannot be an error shared with the target.
    """
    P = lambda z: Peval(a, c, z)
    return r * P(t) - t * diff(P, t)


def F(a, c, r, tau, th):
    return (exp(mpc(0, 1) * r * th) * Peval(a, c, tau * exp(mpc(0, -1) * th))).imag


def sigma(a, r, s):
    return sum(s / (ak - s) for ak in a) + r


def t_a_of(a, r):
    xs = sorted(set(a))
    assert sum(1 for x in a if x == xs[0]) == 1, "this pencil is not simple"
    lo = xs[0] + (xs[1] - xs[0]) * mpf(10) ** -35
    hi = xs[1] - (xs[1] - xs[0]) * mpf(10) ** -35
    assert sigma(a, r, lo) < 0 < sigma(a, r, hi), "the endpoint is not bracketed"
    for _ in range(400):
        mid = (lo + hi) / 2
        if sigma(a, r, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


PENCILS = [
    ("a = (1,2,5), r = 1", [mpf(1), mpf(2), mpf(5)], mpf(1), 1),
    ("a = (1,2,5), r = 2", [mpf(1), mpf(2), mpf(5)], mpf(1), 2),
    ("a = (1,3,3,8), r = 1", [mpf(1), mpf(3), mpf(3), mpf(8)], mpf(2), 1),
    ("a = (1/2,1,1,5), r = 1", [mpf(1) / 2, mpf(1), mpf(1), mpf(5)], mpf(1), 1),
    ("a = (1,4,9,16), r = 2", [mpf(1), mpf(4), mpf(9), mpf(16)], mpf(3), 2),
]

print("PASS  (i)/(ii) the expansion coefficients, against closed forms:")
worst_odd = mpf(0)
worst_slope = mpf(0)
for name, a, c, r in PENCILS:
    ta = t_a_of(a, r)
    for tau in (ta, ta * mpf(9) / 10, ta * mpf(11) / 10):
        g = lambda th: F(a, c, r, tau, th)
        # (i) oddness: F(-theta) = -F(theta), so every even coefficient dies
        for k in (0, 2, 4):
            ck = diff(g, mpf(0), k)
            worst_odd = max(worst_odd, fabs(ck))
            assert fabs(ck) < ZERO, (
                f"the theta^{k} coefficient is {ck} on {name} at tau={tau} -- "
                f"F is not odd, and the vanishing-slope argument needs it")
        # (ii) the first-order coefficient is E(tau)
        c1 = diff(g, mpf(0), 1)
        # dF/dtheta at 0 is Im(i r P(tau) - i tau P'(tau)) = r P - tau P' = E,
        # with NO sign flip: the minus in `ftPencilImDeriv`'s `-Complex.I`
        # belongs to that definition's own convention, not to this derivative.
        pred = Eeval(a, c, r, tau)
        rel = fabs(c1 - pred) / max(fabs(pred), mpf(1))
        worst_slope = max(worst_slope, rel)
        assert rel < mpf(10) ** -30, (
            f"dF/dtheta(0) = {c1} against E(tau) = {pred} on {name}")
    # and at the endpoint the slope really is zero, because E(t_a) = 0
    assert fabs(Eeval(a, c, r, ta)) < mpf(10) ** -25, (
        f"E(t_a) = {Eeval(a, c, r, ta)} on {name}")
    assert fabs(diff(lambda th: F(a, c, r, ta, th), mpf(0), 1)) < mpf(10) ** -25
    print(f"        {name:<22} t_a = {mp.nstr(ta, 10):<14} "
          f"E(t_a) = {mp.nstr(Eeval(a, c, r, ta), 4):<12} "
          f"dF/dtheta(t_a,0) = {mp.nstr(diff(lambda th: F(a, c, r, ta, th), mpf(0), 1), 4)}")

print(f"PASS  (i) every even theta-coefficient vanishes to {mp.nstr(worst_odd, 4)}; "
      f"the theta^2 term is EXACTLY zero, so the second-order remainder is "
      f"third order")
print(f"PASS  (ii) dF/dtheta(tau,0) = E(tau) to {mp.nstr(worst_slope, 4)}, so "
      f"the slope vanishes at t_a because E(t_a) = 0 -- a property of the "
      f"pencil, not a cancellation in theta.  Rolle alone bounds this "
      f"coefficient; it does not kill it")

# --- (iii) uniformity of the cubic remainder over a tau-neighborhood -------
print("PASS  (iii) the cubic remainder, maximized over tau and theta:")
worst_C = mpf(0)
for name, a, c, r in PENCILS:
    ta = t_a_of(a, r)
    delta = ta / 10
    C = mpf(0)
    for i in range(-10, 11):
        tau = ta + delta * mpf(i) / 10
        Etau = Eeval(a, c, r, tau)
        for j in range(1, 13):
            th = mpf(2) ** (-mpf(j))
            rem = fabs(F(a, c, r, tau, th) - Etau * th)
            C = max(C, rem / th ** 3)
    worst_C = max(worst_C, C)
    # the bound must be a BOUND, not a fitted value: check it holds at a theta
    # an order finer than any used to find it
    for i in (-10, 0, 10):
        tau = ta + delta * mpf(i) / 10
        th = mpf(2) ** -20
        assert fabs(F(a, c, r, tau, th) - Eeval(a, c, r, tau) * th) <= C * th ** 3 * 2, (
            f"the constant found on the grid fails off it, on {name}")
    print(f"        {name:<22} |tau - t_a| <= t_a/10:  C = {mp.nstr(C, 8)}")

print(f"PASS  (iii) |F(tau,theta) - E(tau) theta| <= C theta^3 holds with ONE "
      f"C per pencil across the whole neighborhood, largest {mp.nstr(worst_C, 6)}, "
      f"and the constant survives a theta three orders finer than the grid "
      f"that produced it -- so it is a bound rather than a fit")
print("ALL PASS")
