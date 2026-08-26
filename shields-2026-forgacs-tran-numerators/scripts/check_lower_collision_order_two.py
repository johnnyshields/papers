r"""Paper section `sec:dominance` (The weighted dominance bound).

That the lower endpoint's collision has multiplicity exactly two when the
smallest zero is simple -- structurally, for every admissible pencil, rather
than at a sample of them.

`thm:weighted-dominance` carries `hrho : 0 < n_0 -> 2 <= rho`, which reads as
a wall at `rho = 1` and is not: if the collision at `t_a` has multiplicity
exactly two then the retained lower cluster is the principal pair alone,
`n_0 = 0`, and the implication is discharged vacuously.  So "multiplicity
exactly two" is what makes the corner compose, and it had been measured at six
pencil/`r` pairs.  It is an identity.

Write `g(t) = t^r/Q(t)` with `Q(t) = \prod_k (a_k - t)`, and `\Sigma` for the
critical function `\sum_k s/(a_k - s) + r`.  Then

    g'/g = r/t + \sum_k 1/(a_k - t) = \Sigma(t)/t ,

so the critical points of `g` are exactly the zeros of `\Sigma`.  Differentiate
once more and evaluate where `g' = 0`:

    g''(t_a)/g(t_a) = (g'/g)'(t_a) = \Sigma'(t_a)/t_a ,

so **`g''(t_a) = g(t_a)\,\Sigma'(t_a)/t_a`**.  Every factor on the right is
nonzero for an admissible pencil at `rho = 1`: `t_a > 0`; `Q(t_a) \ne 0` since
`t_a` lies strictly inside `(x_1, x_2)`, so `g(t_a) \ne 0`; and
`\Sigma'(t_a) = \sum_k a_k/(a_k - t_a)^2` is a sum of positive terms.  Hence
`g''(t_a) \ne 0`, the critical point is nondegenerate, and the collision is a
double root -- for EVERY admissible pencil, with no case analysis and nothing
measured.

Three things are checked: the two identities, which is what makes the argument
an identity rather than a coincidence; that the multiplicity is two and not
three; and that at `rho >= 2` the same construction does NOT apply, so the
result is not quietly claimed outside its scope.

mpmath only.
"""

from mpmath import mp, mpf, fabs, diff

mp.dps = 50

ZERO = mpf(10) ** -35


def Q(a, t):
    p = mpf(1)
    for ak in a:
        p *= (ak - t)
    return p


def g(a, r, t):
    return t ** r / Q(a, t)


def sigma(a, r, s):
    return sum(s / (ak - s) for ak in a) + r


def sigma_deriv(a, s):
    return sum(ak / (ak - s) ** 2 for ak in a)


def t_a_of(a, r):
    """The zero of Sigma strictly inside (x_1, x_2); simple smallest zero only."""
    xs = sorted(set(a))
    assert sum(1 for x in a if x == xs[0]) == 1, "this pencil is not simple"
    lo = xs[0] + (xs[1] - xs[0]) * mpf(10) ** -30
    hi = xs[1] - (xs[1] - xs[0]) * mpf(10) ** -30
    assert sigma(a, r, lo) < 0 < sigma(a, r, hi), "the endpoint is not bracketed"
    for _ in range(400):
        mid = (lo + hi) / 2
        if sigma(a, r, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


PENCILS = [
    ("a = (1,2,5), r = 1", [mpf(1), mpf(2), mpf(5)], 1),
    ("a = (1,2,5), r = 2", [mpf(1), mpf(2), mpf(5)], 2),
    ("a = (1,3,3,8), r = 1", [mpf(1), mpf(3), mpf(3), mpf(8)], 1),
    ("a = (1/2,1,1,5), r = 1", [mpf(1) / 2, mpf(1), mpf(1), mpf(5)], 1),
    ("a = (1,4,9,16), r = 2", [mpf(1), mpf(4), mpf(9), mpf(16)], 2),
    ("a = (1,2,3,4,5), r = 3", [mpf(i) for i in range(1, 6)], 3),
]

worst_first = mpf(0)
worst_second = mpf(0)
rows = []
for name, a, r in PENCILS:
    ta = t_a_of(a, r)

    # identity 1: g'/g = Sigma(t)/t, away from the endpoint as well as at it
    for probe in (ta, ta * mpf(9) / 10, ta * mpf(11) / 10):
        lhs = diff(lambda t: g(a, r, t), probe) / g(a, r, probe)
        rhs = sigma(a, r, probe) / probe
        worst_first = max(worst_first, fabs(lhs - rhs))

    # the critical point really is critical
    g1 = diff(lambda t: g(a, r, t), ta)
    assert fabs(g1 / g(a, r, ta)) < mpf(10) ** -30, (
        f"g'(t_a)/g(t_a) = {g1 / g(a, r, ta)} on {name}, not zero")

    # identity 2: g''(t_a) = g(t_a) * Sigma'(t_a) / t_a
    g2 = diff(lambda t: g(a, r, t), ta, 2)
    pred = g(a, r, ta) * sigma_deriv(a, ta) / ta
    worst_second = max(worst_second, fabs(g2 - pred) / fabs(pred))

    # multiplicity exactly two: second derivative nonzero
    assert fabs(g2) > ZERO, f"g''(t_a) vanishes on {name} -- not a double root"
    # and not three: a triple root would need g'' = 0, which the identity forbids
    rows.append((name, ta, g2, sigma_deriv(a, ta), Q(a, ta)))

print(f"PASS  g'/g = Sigma(t)/t, at the endpoint and off it; worst residual "
      f"{mp.nstr(worst_first, 5)}")
print(f"PASS  g''(t_a) = g(t_a) * Sigma'(t_a) / t_a; worst relative residual "
      f"{mp.nstr(worst_second, 5)}")
print("PASS  the collision is a double root at every pencil, and each factor "
      "of the identity is nonzero for a structural reason:")
for name, ta, g2, sd, q in rows:
    assert ta > 0 and sd > 0 and fabs(q) > ZERO
    print(f"        {name:<22} t_a = {mp.nstr(ta, 10):<14} "
          f"g''(t_a) = {mp.nstr(g2, 8):<14} Sigma'(t_a) = {mp.nstr(sd, 6)}")

# --- WHICH g, and why the other convention is a different formula ----------
# The paper writes the branch function as `g_P(t) = -Q(t)/t^r`, the reciprocal
# (up to sign) of the `g_L(t) = t^r/Q(t)` used above.  BOTH satisfy an identity
# of this shape and BOTH give a negative second derivative at `t_a`, but the
# formulas are NOT the same:
#
#     g_L'' (t_a) = g_L(t_a) * Sigma'(t_a) / t_a
#     g_P'' (t_a) = Sigma'(t_a) * Q(t_a) / t_a^(r+1)
#
# because `g_P = -1/g_L` flips the sign of the logarithmic derivative, and the
# `g` factor that survives on the right is a different function.  Transporting
# the wrong one into a proof yields a wrong formula WITH THE RIGHT SIGN, which
# no check on the value would catch -- so both are asserted here, and the
# statement above is labeled as `g_L`'s.
worst_paper = mpf(0)
for name, a_, r in PENCILS:
    ta = t_a_of(a_, r)
    gP2 = diff(lambda t: -Q(a_, t) / t ** r, ta, 2)
    pred = sigma_deriv(a_, ta) * Q(a_, ta) / ta ** (r + 1)
    worst_paper = max(worst_paper, fabs(gP2 - pred) / fabs(pred))
    assert gP2 < 0, f"g_P''(t_a) is not negative on {name}"
    # and the two conventions genuinely disagree as formulas
    other = g(a_, r, ta) * sigma_deriv(a_, ta) / ta
    assert fabs(gP2 - other) / fabs(gP2) > mpf(1) / 100, (
        f"the two conventions coincide numerically on {name} -- the "
        f"distinction this block exists for would be untestable there")
print(f"PASS  in the PAPER's convention g_P = -Q/t^r the identity reads "
      f"g_P''(t_a) = Sigma'(t_a) Q(t_a) / t_a^(r+1); worst relative residual "
      f"{mp.nstr(worst_paper, 5)}")
print("PASS  the two conventions differ as FORMULAS while agreeing in sign, "
      "so a value check cannot tell them apart -- each is stated with the g "
      "it belongs to")

print("PASS  t_a > 0, Q(t_a) != 0 because t_a lies strictly inside (x_1, x_2), "
      "and Sigma'(t_a) = sum a_k/(a_k - t_a)^2 is a sum of positive terms -- "
      "so g''(t_a) != 0 for EVERY admissible pencil with a simple smallest "
      "zero, not merely for those sampled")

# --- scope: the construction does not reach rho >= 2 ------------------------
# There the endpoint is x_1 itself, where Q vanishes and g has a pole, so
# `g''(t_a)` is not the object at all.  Asserting that keeps the result from
# being quoted outside its hypothesis.
for a in ([mpf(1), mpf(1), mpf(3)], [mpf(2), mpf(2), mpf(7)],
          [mpf(1), mpf(1), mpf(1), mpf(4)]):
    x1 = min(a)
    assert sum(1 for x in a if x == x1) >= 2, "this pencil is simple"
    assert fabs(Q(a, x1)) < ZERO, "Q does not vanish at the repeated zero"
print("PASS  at rho >= 2 the endpoint is x_1, where Q vanishes and g has a "
      "pole -- the identity's g(t_a) factor does not exist, so the argument "
      "is confined to its hypothesis rather than silently extended")

print("ALL PASS")
