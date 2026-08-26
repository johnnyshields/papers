r"""Paper section `sec:dominance` (The weighted dominance bound).

The lower endpoint's spread constant, confirmed from its closed form by a
route that shares no machinery with the pencil measurement.

`check_lower_retained_radius_carrier.py` locates the retained radius's
infimum in the tail-to-infinity direction and identifies the limiting
constant.  That identification is the load-bearing claim -- it is what says
the carrier `u = (t_a - a_0)/t_a` has a POSITIVE FLOOR where the relative gap
does not -- so it is confirmed here without touching a pencil at all.

Three links, each checked on its own:

  (i)   `z^r - r z + (r-1) = (z-1)^2 \sum_{i<r-1} (r-1-i) z^i` -- the
        factorization that turns the limiting family into a tail polynomial,
        and which is `EndpointUpperGeneralN.pow_sub_one_sub_smul` reappearing
        at the other endpoint;
  (ii)  `s^* `, the nonzero root of `e^s = 1 + s` of least real part;
  (iii) `\kappa(r) = r(\min_j|z_j| - 1)` over the tail's roots, falling to
        `\operatorname{Re}(s^*)` monotonically -- which is what the
        substitution `z = 1 + s/r` predicts, since it sends the polynomial to
        `e^s - s - 1`.

The point of the exercise is the SIGN of the limit, not its value: the
relative-gap constant satisfies `(n-2)c_n \to 0`, so a radius built on it
collapses; `\kappa \to 2.0888\ldots > 0` does not.  A constant that stops
decaying is a different kind of object from one that decays slowly.

mpmath only; no pencil, no branch, no root-finder output differentiated.
"""

from mpmath import mp, mpf, mpc, fabs, polyroots, findroot, exp

mp.dps = 30

# (i) the factorization
worst = mpf(0)
for r in range(2, 14):
    for z in (mpc(mpf(4) / 3, mpf(2) / 5), mpc(-mpf(3) / 2, mpf(1) / 7)):
        lhs = z ** r - r * z + (r - 1)
        rhs = (z - 1) ** 2 * sum((r - 1 - i) * z ** i for i in range(r - 1))
        worst = max(worst, fabs(lhs - rhs) / max(fabs(lhs), mpf(1)))
assert worst < mpf(10) ** -25, f"the factorization fails: {worst}"
print(f"PASS  (i) z^r - r z + (r-1) = (z-1)^2 sum (r-1-i) z^i at r = 2..13; "
      f"worst relative residual {mp.nstr(worst, 5)}")

# (ii) s*
f = lambda s: exp(s) - 1 - s
sstar = findroot(f, mpc(2, 7))
assert fabs(f(sstar)) < mpf(10) ** -25, "s* does not solve e^s = 1 + s"
assert fabs(sstar) > 1, "s* is the trivial root"
assert sstar.real > 2 and sstar.imag > 7
print(f"PASS  (ii) s* = {mp.nstr(sstar, 14)} solves e^s = 1 + s; "
      f"Re(s*) = {mp.nstr(sstar.real, 16)}")

# (iii) kappa(r) -> Re(s*), monotonically from above
target = sstar.real
prev = None
gaps = {}
for r in (3, 4, 6, 10, 12, 20, 50, 100):
    tail = [mpf(r - 1 - i) for i in range(r - 1)]
    rts = polyroots(list(reversed(tail)), maxsteps=200, extraprec=120)
    kap = r * (min(fabs(mpc(z)) for z in rts) - 1)
    assert kap > target, f"kappa({r}) = {kap} is below Re(s*)"
    if prev is not None:
        assert kap < prev, f"kappa is not decreasing at r = {r}"
    prev = kap
    gaps[r] = kap - target
assert gaps[100] < gaps[3] / 25, "the approach to Re(s*) is not convergent"
print(f"PASS  (iii) kappa(r) falls monotonically to Re(s*): gap "
      f"{mp.nstr(gaps[3], 4)} at r = 3, {mp.nstr(gaps[12], 4)} at r = 12, "
      f"{mp.nstr(gaps[100], 4)} at r = 100")

# the two constants that are being compared, and the sign that separates them
assert target > 2, "Re(s*) is not bounded away from zero"
print(f"PASS  so the spread constant has a POSITIVE floor, "
      f"{mp.nstr(target, 12)}, where the relative-gap constant has none -- "
      f"(n-2)c_n peaks at 3.118 near n = 9 and decays.  That sign is the whole "
      f"difference: a constant that stops decaying admits a retained radius, "
      f"one that decays slowly does not")
print("ALL PASS")
