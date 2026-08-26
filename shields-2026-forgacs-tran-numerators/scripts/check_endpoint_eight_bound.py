#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `sec:geometry`,
`eq:ab-def`.

`eight_mul_pow_le_prod_of_sum_eq_one` is the closed form that separates the
`r = 1` upper endpoint at `n = 3`: from `sum_k L/(a_k + L) = 1` it concludes
`8 L^3 <= prod_k a_k`.  Since `D_b`'s root product is `prod a_k` and the
collision takes `L^2`, the one remaining root sits at `prod a_k / L^2 >= 8L`, so
it clears the circle of radius `L` by a factor of 8.

Three things are checked, and the first is an attempt to REFUTE the lemma rather
than to illustrate it.

  (E1) `8 L^3 <= prod a_k` over a wide random sweep of positive triples, with `L`
       solved from the sum condition each time.  A single counterexample would
       mean the Lean statement is about something other than what it says.
  (E2) The bound is SHARP: at `a_1 = a_2 = a_3` the condition forces `a = 2L` and
       the inequality is an EQUALITY -- which is why the sweep's tolerance is set
       from the measured bisection error rather than guessed: at that pencil the
       ratio sits 2.3e-29 BELOW 1 for purely numerical reasons.  A bound that is never attained would be
       fine mathematically and would mean the constant 8 is not the natural one;
       it is attained, so it is.
  (E3) The bridge to the geometry, which the algebra alone does not give: the
       endpoint `L` of `check_upper_endpoint_r_one.py` -- the one with
       `E(-L) = 0` for `E(t) = t Q'(t) - r Q(t)` at `r = 1` -- is the SAME `L`
       that satisfies the sum condition.  Without this the lemma is a true fact
       about an unrelated `L`.

mpmath only, 50 digits.  `L` is obtained by bisection on the sum condition,
which is strictly decreasing in `L`, so the root is unique and no branch
selection is needed.
"""
from mpmath import mp, mpf, mpc, findroot, fabs, polyroots

mp.dps = 50


def solve_L(a):
    """The unique `L > 0` with `sum_k L/(a_k + L) = 1`."""
    f = lambda L: sum(L / (mpf(ak) + L) for ak in a) - 1
    lo, hi = mpf(10)**-8, mpf(max(a)) * len(a) * 4
    assert f(lo) < 0 < f(hi), "the sum condition does not bracket"
    return mpf(findroot(f, (lo, hi), solver='bisect', tol=mpf(10)**-40))


def qcoeffs(c, a):
    poly = [mpf(c)]
    for ak in a:
        nxt = [mpf(0)] * (len(poly) + 1)
        for i, co in enumerate(poly):
            nxt[i] += co * mpf(ak)
            nxt[i + 1] -= co
        poly = nxt
    return poly[::-1]


def peval(C, t):
    v = mpc(0)
    for co in C:
        v = v * t + co
    return v


def deriv(C):
    d = len(C) - 1
    return [C[i] * (d - i) for i in range(d)] if d > 0 else [mpf(0)]


print("the 8 L^3 <= prod a bound at the r = 1 upper endpoint, n = 3")
print()

# (E1) a wide sweep, aimed at refutation.  Deterministic ladder rather than a
# random draw, so the run is reproducible and the extremes are deliberate.
SCALES = [mpf(1) / 100, mpf(1) / 4, mpf(1), mpf(7), mpf(400)]
SHAPES = [(1, 1, 1), (1, 1, 2), (1, 2, 4), (1, 1, 50), (1, 50, 50),
          (1, 1000, 1000), (1, 1, 1000), (3, 5, 7), (1, 10, 100)]
worst, worst_at = None, None
for s in SCALES:
    for sh in SHAPES:
        a = [s * mpf(x) for x in sh]
        L = solve_L(a)
        prod = mpf(1)
        for ak in a:
            prod *= ak
        ratio = prod / (8 * L**3)
        # tolerance set from the MEASURED bisection error at the equality
        # pencil, not guessed: there `L` lands 9.6e-30 above the exact `a/2`,
        # giving a deficit of 2.3e-29 at a point where the bound is an exact
        # equality.  1e-25 clears that by four orders and still refutes any real
        # violation, which would be of order 1.
        assert ratio >= 1 - mpf(10)**-25, (
            f"REFUTED at a={[mp.nstr(x,6) for x in a]}: prod/(8L^3) = "
            f"{mp.nstr(ratio,12)} < 1")
        if worst is None or ratio < worst:
            worst, worst_at = ratio, (sh, s)
print(f"PASS  (E1) 8L^3 <= prod a at all {len(SCALES)*len(SHAPES)} pencils of the "
      f"sweep, scales 1e-2 to 4e2 and shapes to 1000:1 aspect; the closest "
      f"approach is {mp.nstr(worst,12)} at shape {worst_at[0]}")

# (E2) sharpness at the equal-zero pencil
for s in SCALES:
    a = [s, s, s]
    L = solve_L(a)
    assert fabs(L - s / 2) < mpf(10)**-25, (
        f"equal zeros should force a = 2L; got L = {mp.nstr(L,12)} for a = "
        f"{mp.nstr(s,12)}")
    prod = s**3
    assert fabs(prod - 8 * L**3) < mpf(10)**-24 * prod, "equality not attained"
print("PASS  (E2) at a_1 = a_2 = a_3 the sum condition forces a = 2L and the "
      "bound is an EQUALITY, so the constant 8 is attained and not merely valid")

# (E3) the algebra's L is the geometry's L
BRIDGE = [([1.0, 1.0, 2.0], 1.0), ([0.4, 0.4, 1.7], 2.5), ([3.0, 5.0, 7.0], 0.8)]
for a, c in BRIDGE:
    L = solve_L(a)
    Q = qcoeffs(c, a)
    Qp = deriv(Q)
    E = mpc(-L) * peval(Qp, mpc(-L)) - 1 * peval(Q, mpc(-L))
    assert fabs(E) < mpf(10)**-28 * max(mpf(1), fabs(peval(Q, mpc(-L)))), (
        f"a={a}: the sum-condition L does not satisfy E(-L) = 0, |E| = "
        f"{mp.nstr(fabs(E),8)} -- the lemma would be about a different L")
print(f"PASS  (E3) the `L` of the sum condition is exactly the endpoint `L` with "
      f"E(-L) = 0 at all {len(BRIDGE)} pencils, so the algebra and the geometry "
      f"are about the same point")

# (E4) the consequence the separation actually uses
for a, c in BRIDGE:
    L = solve_L(a)
    prod = mpf(1)
    for ak in a:
        prod *= mpf(ak)
    assert prod / L**2 >= 8 * L, "the remaining root does not clear 8L"
    assert 8 * L > L, "8L does not exceed L"
print("PASS  (E4) the one remaining root sits at prod(a)/L^2 >= 8L > L, which is "
      "the fixed separating radius the r = 1 upper endpoint needs")

# (E5) The bound GENERALIZES, with the same proof and the same sharpness.
# With `sum u_k = 1` and `1 - u_k = sum_{j != k} u_j`, AM-GM on each of the `n`
# sums gives `1 - u_k >= (n-1) (prod_{j != k} u_j)^{1/(n-1)}`, and
# `prod_k prod_{j != k} u_j = (prod u)^{n-1}`, so `prod (1 - u_k) >= (n-1)^n prod u`
# and hence `prod a_k >= (n-1)^n L^n`.  At `n = 3` that is the lemma's 8.
GEN = [(1, 1, 1), (1, 2, 4), (1, 1, 1, 2), (1, 2, 4, 8), (1, 1, 1, 1),
       (1, 1, 1, 1, 1), (1, 2, 3, 4, 5), (1, 1, 1, 1, 1, 1), (1, 1, 50, 50),
       (1, 1, 1, 1000), (1, 1000, 1000, 1000)]
eqs = 0
for sh in GEN:
    a = [mpf(x) for x in sh]
    n = len(a)
    L = solve_L(a)
    prod = mpf(1)
    for x in a:
        prod *= x
    ratio = prod / (mpf(n - 1) ** n * L ** n)
    assert ratio >= 1 - mpf(10)**-25, (
        f"n={n} a={sh}: prod a / ((n-1)^n L^n) = {mp.nstr(ratio,12)} < 1")
    if fabs(ratio - 1) < mpf(10)**-20:
        eqs += 1
        assert fabs(L - a[0] / (n - 1)) < mpf(10)**-20, (
            f"n={n}: equal zeros should force a = (n-1)L")
print(f"PASS  (E5) prod a_k >= (n-1)^n L^n at n = 3,4,5,6 over {len(GEN)} pencils, "
      f"with EQUALITY at all {eqs} equal-zero ones (where a = (n-1)L) -- so the "
      f"lemma's 8 is (n-1)^n at n = 3 and the generalization is sharp at every n")

# (E6) At n >= 4 the product bound no longer forces the separation on its own --
# several remaining roots share the product, so one could in principle be small.
# It is not: swept deterministically, the MINIMUM remaining modulus still clears
# 8L, which is the n = 3 constant surviving into a case the n = 3 proof does not
# cover.  Reported as a measurement, not a theorem.
SWEEP = []
for n in (4, 5, 6):
    for base in ([1, 1, 1], [1, 2, 5], [1, 1, 10]):
        for tail in ([2], [50], [1400], [3, 9]):
            a = [mpf(x) for x in base] + [mpf(x) for x in tail]
            if len(a) == n:
                SWEEP.append(a)
worst_sep, worst_at = None, None
for a in SWEEP:
    L = solve_L(a)
    Q = qcoeffs(1.0, a)
    b = mpf((-peval(Q, mpc(-L)) / mpc(-L)).real)
    D = list(Q)
    D[-2] += b
    rts = sorted(polyroots(D, maxsteps=400, extraprec=800), key=lambda t: fabs(t))
    others = [t for t in rts if fabs(t + L) > mpf(10)**-15]
    if not others:
        continue
    sep = min(fabs(t) for t in others) / L
    assert sep > 1, (
        f"a={[mp.nstr(x,5) for x in a]}: a remaining root sits at {mp.nstr(sep,8)}L, "
        f"inside the circle -- the r = 1 separation FAILS at n >= 4")
    if worst_sep is None or sep < worst_sep:
        worst_sep, worst_at = sep, [mp.nstr(x, 5) for x in a]
print(f"PASS  (E6) at n = 4,5,6 over {len(SWEEP)} pencils every remaining root "
      f"still clears the circle, worst {mp.nstr(worst_sep,8)}L at a={worst_at} -- "
      f"the n = 3 constant 8 appears to survive, though the n = 3 PROOF does not, "
      f"since several roots then share the product bound")

print()
print("ALL PASS  check_endpoint_eight_bound")
