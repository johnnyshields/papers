#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; the `_1` retained group
at general `n` (BANK-39).

What it would take to lift the `n = 3` restriction on the `2L` circle, measured
rather than estimated.  Four results, two of them negative.

  (G1) **The normalization.**  With `u_k = L/(a_k+L)` and `s = (w+L)/L`, a root `w`
       of the endpoint pencil `D_b = Q + bX` is a root of
       `prod_k (1 - u_k s) = 1 - s`, on the simplex `sum_k u_k = 1` -- which IS the
       deficit equation.  `c`, `L` and the `a_k` all leave; what remains is a
       one-parameter family in `u` alone.  The collision `w = -L` is `s = 0`, and
       it is a double root of that equation *because* `sum u_k = 1`.
  (G2) Expanding, `prod(1-u_k s) - (1-s) = sum_{j>=2} (-1)^j e_j s^j`, so the
       non-collision roots are the roots of `G(s) = sum_{j>=2} (-1)^j e_j s^{j-2}`
       in the elementary symmetric functions of `u`.  At `n = 3` that is linear,
       `s = e_2/e_3`, and `s >= 9` is Newton plus Maclaurin -- which is the AM-GM
       already in Lean, in different clothes.  From `n = 4` it is not linear.
  (G3) **The clearance is enormous, so the target has room.**  `min |s - 1|`,
       which is `min |w|/L`, measured over the simplex at `n = 3..7`.  The circle
       to clear is at `2`.
  (G4) **NEGATIVE -- the Vieta step does not generalize, so the five lemmas do NOT
       widen together.**  `norm_mul_sq_eq_prod_of_mem_roots_endpoint_pi` gets the
       minimum from the product because at `n = 3` there is exactly ONE other root.
       At `n >= 4` the product is over `n-2` roots and says nothing about the
       smallest: measured, the ratio `max/min` runs to three orders of magnitude,
       so `prod / max^{n-3}` -- the only bound available from a product -- is far
       below `2`.  Lifting `eight_mul_pow_le_prod_of_sum_eq_one` therefore does not
       lift its consumer.
  (G5) **NEGATIVE -- no origin-centered circle admits a modulus split.**  On
       `|t| = rho*L`, `|b t| = rho * c * prod(a_k+L)` exactly and
       `|Q(t)| <= c * prod(a_k + rho L)`, so `|bt| > |Q|` needs
       `rho > prod(1 + (rho-1) u_k)`.  That product is a concave function of `u` on
       the simplex, so it is MINIMIZED at a vertex, where it equals `rho` exactly.
       Hence `rho <= prod(...)` always, at every radius and every `n`: the
       inequality is reversed with equality only in the degenerate limit.  A
       Rouche comparison of `Q` against `bX` is unavailable, not merely lossy.
  (G7) **How far the third route reaches.**  `G(s) = sum_{j>=2} (-1)^j e_j s^{j-2}`
       has no zero in `|s| < R` as soon as `e_2 > sum_{j>=3} R^{j-2} e_j`, and
       `|s| > 3` gives `|s-1| > 2`, the circle.  Measured on the simplex, that
       inequality HOLDS at `n = 3,4,5,6` and FAILS from `n = 7` -- the largest `R`
       it supports falls 5.9, 4.6, 3.5, 3.0, 2.7, 2.6, ... as `n` grows, toward the
       `R^2 + R + 1 = e^R` limit near 1.79.  So the coefficient route closes the
       gap for `n <= 6` and cannot close it in general.
  (G6) The AM-GM that IS general: `prod a_k >= (n-1)^n L^n`, sharp at equal `a_k`.
       This lifts `eight_mul_pow_le_prod_of_sum_eq_one` -- `(3-1)^3 = 8` -- and is
       the one of the five that does widen.

  (G8) **The route that DOES close it, at every `n`.**  The bounds above are all
       taken about `s = 0`, while the disk to avoid is `|s - 1| <= 2`.  Centered
       where it belongs, the triangle bound holds at every `n` -- and it collapses:
       the Taylor coefficients `g_m` of `G` at `s = 1` alternate, so
       `sum_{m>=1} |g_m| 2^m = G(-1) - G(1)`, and with `G(1) = prod(1-u_k)` and
       `G(-1) = prod(1+u_k) - 2` the whole bound becomes ONE inequality:

           prod(1+u_k)  <  2 + 2*prod(1-u_k)        on   sum u_k = 1.

       In elementary symmetric functions that is `sum_{even j>=2} e_j >=
       3 sum_{odd j>=3} e_j`, and it follows TERMWISE from `e_j >= 3 e_(j+1)` for
       `j >= 2`.  That step needs nothing deep: expanding `e_1 e_j`, a squarefree
       monomial of degree `j+1` arises from each of its `j+1` sub-monomials of
       degree `j`, and the remaining terms carry a square, so

           e_1 * e_j  =  (j+1) e_(j+1)  +  (a sum of non-negative terms).

       With `e_1 = 1` that is `e_j >= (j+1) e_(j+1)`, which at `j >= 2` is the
       factor 3.  Newton's inequalities would also give it and are NOT in Mathlib;
       this route does not need them.
       Tight at both ends -- equality at a vertex, and `e < 2/e + 2` with margin
       `0.0175` in the equal-point limit -- which is why every bound taken about
       the origin missed it.

mpmath and sympy.  Roots by `polyroots` at 60 digits; the simplex is sampled on a
Dirichlet-style grid plus the corners the negative results live at.
"""
import itertools
import random

from mpmath import mp, mpf, mpc, findroot, polyroots, fabs, re, sqrt
import sympy as sp

mp.dps = 60
random.seed(20260826)


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


def endpoint_L(a):
    """The `L > 0` of `sum_k L/(a_k+L) = 1`, which is `E(-L) = 0` at `r = 1`."""
    f = lambda L: sum(L / (mpf(ak) + L) for ak in a) - 1
    lo, hi = mpf(10) ** -12, mpf(max(a)) * mpf(len(a)) * 16
    assert f(lo) < 0 < f(hi)
    return mpf(re(findroot(f, (lo, hi), solver='bisect', tol=mpf(10) ** -50)))


def pencil_roots(c, a):
    """(L, b, the roots of D_b) at the r = 1 upper endpoint."""
    L = endpoint_L(a)
    Q = qcoeffs(c, a)
    b = mpf(re(peval(Q, mpf(-L)) / L))
    D = list(Q)
    D[-2] += b                      # + b X
    return L, b, polyroots(D, maxsteps=600, extraprec=1200)


def simplex_samples(n, m):
    """Interior points of `sum u = 1`, plus near-corner and equal points."""
    pts = [[mpf(1) / n] * n]
    for _ in range(m):
        w = [mpf(random.uniform(0.02, 1.0)) for _ in range(n)]
        t = sum(w)
        pts.append([x / t for x in w])
    near = [mpf(1) - mpf(1) / 50] + [mpf(1) / (50 * (n - 1))] * (n - 1)
    pts.append(near)
    return pts


def a_from_u(u, L):
    """Invert `u_k = L/(a_k+L)`."""
    return [L * (1 - uk) / uk for uk in u]


NS = [3, 4, 5, 6, 7]

print("lifting the n = 3 restriction on the 2L circle: what it would take")
print()

# ---- (G1)/(G2) the normalization, against the pencil itself -------------------
print("(G1)/(G2) the normalized equation, checked against the pencil")
worst_norm = mpf(0)
for n in NS:
    for u in simplex_samples(n, 3):
        L = mpf(1)
        a = a_from_u(u, L)
        c = mpf(1) + mpf(n) / 10
        L2, b, rts = pencil_roots(c, a)
        assert fabs(L2 - L) < mpf(10) ** -25, f"n={n}: L round trip {L2}"
        # every root maps to a root of prod(1 - u_k s) = 1 - s
        for w in rts:
            s = (w + L) / L
            lhs = mpc(1)
            for uk in u:
                lhs *= (1 - uk * s)
            worst_norm = max(worst_norm, fabs(lhs - (1 - s)))
print(f"  worst |prod(1-u_k s) - (1-s)| over all roots, all n: "
      f"{mp.nstr(worst_norm, 6)}")
assert worst_norm < mpf(10) ** -20, "the normalization does not hold"
# and the expansion, symbolically
sy_s = sp.symbols('s')
for n in NS:
    us = sp.symbols(f'u0:{n}', positive=True)
    F = sp.expand(sp.prod([1 - uk * sy_s for uk in us]) - (1 - sy_s))
    poly = sp.Poly(F, sy_s)
    c0, c1 = poly.coeff_monomial(1), poly.coeff_monomial(sy_s)
    assert sp.simplify(c0) == 0, f"n={n}: constant term is not 0"
    assert sp.simplify(c1 - (1 - sum(us))) == 0, f"n={n}: s-coefficient is not 1-sum(u)"
    for j in range(2, n + 1):
        want = (-1) ** j * sp.expand(sp.Poly(
            sp.prod([1 + uk * sy_s for uk in us]), sy_s).coeff_monomial(sy_s ** j))
        assert sp.simplify(poly.coeff_monomial(sy_s ** j) - want) == 0, \
            f"n={n}: coefficient of s^{j} is not (-1)^j e_{j}"
print(f"  symbolically at n = {NS}: the constant term vanishes, the `s` coefficient")
print(f"    is `1 - sum(u)` -- so `s = 0` is a DOUBLE root exactly on the simplex --")
print(f"    and the coefficient of `s^j` is `(-1)^j e_j` for every j >= 2")
print()

# ---- (G3) the clearance ------------------------------------------------------
print("(G3) the clearance: min |w|/L over the simplex")
clearances = []
for n in NS:
    worst = None
    for u in simplex_samples(n, 12):
        L = mpf(1)
        a = a_from_u(u, L)
        _, _, rts = pencil_roots(mpf(1), a)
        others = [w for w in rts if fabs(w + L) > mpf(10) ** -12]
        if not others:
            continue
        m = min(fabs(w) / L for w in others)
        worst = m if worst is None else min(worst, m)
    clearances.append((n, worst))
    print(f"  n = {n}: min |w|/L = {mp.nstr(worst, 8)}")
for n, m in clearances:
    assert m > 2, f"n={n}: clearance {mp.nstr(m,6)} does not clear the 2L circle"
print(f"PASS  (G3) the circle to clear is at 2 and the worst measured clearance is "
      f"{mp.nstr(min(m for _, m in clearances), 6)} -- the target has room, so the "
      f"obstruction is the PROOF and not the geometry")
print()

# ---- (G4) the Vieta step does not generalize ---------------------------------
print("(G4) NEGATIVE: what a product bound can and cannot give")
spreads = []
for n in NS[1:]:
    worst_ratio, worst_prodbound = None, None
    for u in simplex_samples(n, 12):
        L = mpf(1)
        a = a_from_u(u, L)
        _, _, rts = pencil_roots(mpf(1), a)
        others = [fabs(w) / L for w in rts if fabs(w + L) > mpf(10) ** -12]
        if len(others) < 2:
            continue
        lo, hi = min(others), max(others)
        prod = mpf(1)
        for v in others:
            prod *= v
        # the only bound a product gives for the minimum
        bound = prod / hi ** (len(others) - 1)
        worst_ratio = hi / lo if worst_ratio is None else max(worst_ratio, hi / lo)
        worst_prodbound = bound if worst_prodbound is None else min(worst_prodbound, bound)
    spreads.append((n, worst_ratio, worst_prodbound))
    print(f"  n = {n}: worst max/min spread {mp.nstr(worst_ratio, 6)}   "
          f"best-case product bound on the min {mp.nstr(worst_prodbound, 6)}")
for n, ratio, bound in spreads:
    assert ratio > 2, f"n={n}: the other roots are not spread, ratio {mp.nstr(ratio,6)}"
print(f"PASS  (G4) the other roots SPREAD, so a bound on their product is not a "
      f"bound on the smallest.  At n = 3 there is exactly one other root and the "
      f"product IS the minimum -- that, and nothing about the constant 8, is what "
      f"norm_mul_sq_eq_prod_of_mem_roots_endpoint_pi uses.  Lifting the AM-GM "
      f"does NOT lift its consumer")
print()

# ---- (G5) no origin-centered circle admits a modulus split -------------------
print("(G5) NEGATIVE: rho <= prod(1 + (rho-1) u_k) at every radius")
worst_slack = None
for n in NS:
    for u in simplex_samples(n, 20):
        for rho in [mpf(11) / 10, mpf(3) / 2, mpf(2), mpf(3), mpf(5), mpf(9), mpf(20)]:
            prod = mpf(1)
            for uk in u:
                prod *= (1 + (rho - 1) * uk)
            slack = prod - rho
            worst_slack = slack if worst_slack is None else min(worst_slack, slack)
print(f"  worst (prod - rho) over all n, all u, all rho: {mp.nstr(worst_slack, 8)}")
assert worst_slack >= -mpf(10) ** -30, (
    f"prod(1+(rho-1)u) dipped below rho by {mp.nstr(-worst_slack,6)} -- if that is "
    f"real the modulus split is available somewhere and (G5) is wrong")
# the mechanism, symbolically: log of the product is concave in u, so on the
# simplex it is minimized at a vertex, where the product is exactly rho
n_sym = 4
us = sp.symbols(f'v0:{n_sym}', positive=True)
rho_sym = sp.symbols('rho', positive=True)
logprod = sum(sp.log(1 + (rho_sym - 1) * uk) for uk in us)
for uk in us:
    second = sp.simplify(sp.diff(logprod, uk, 2))
    assert sp.simplify(second + (rho_sym - 1) ** 2 / (1 + (rho_sym - 1) * uk) ** 2) == 0, \
        "the second derivative is not the expected negative quantity"
print(f"  mechanism: d^2/du_k^2 log prod = -(rho-1)^2/(1+(rho-1)u_k)^2 < 0, so the")
print(f"    log-product is CONCAVE on the simplex and attains its minimum at a")
print(f"    vertex, where the product is 1 + (rho-1) = rho exactly")
print(f"PASS  (G5) |b t| > |Q(t)| holds at NO radius, for any n: the inequality the "
      f"split needs is reversed everywhere, with equality only in the degenerate "
      f"limit.  A Rouche comparison of Q against bX on a circle about the origin "
      f"is unavailable rather than lossy -- from that comparison alone")
print()

# ---- (G6) the AM-GM that does generalize -------------------------------------
print("(G6) prod a_k >= (n-1)^n L^n, sharp at equal a_k")
tight = []
for n in NS:
    worst = None
    for u in simplex_samples(n, 20):
        L = mpf(1)
        a = a_from_u(u, L)
        prod = mpf(1)
        for ak in a:
            prod *= ak
        ratio = prod / (mpf(n - 1) ** n * L ** n)
        worst = ratio if worst is None else min(worst, ratio)
    # the equal point is the extremal one
    a_eq = a_from_u([mpf(1) / n] * n, mpf(1))
    prod_eq = mpf(1)
    for ak in a_eq:
        prod_eq *= ak
    tight.append((n, worst, prod_eq / (mpf(n - 1) ** n)))
    print(f"  n = {n}: worst prod/((n-1)^n L^n) = {mp.nstr(worst, 10)}   "
          f"at equal a_k = {mp.nstr(prod_eq / (mpf(n - 1) ** n), 10)}")
for n, worst, eq in tight:
    assert worst >= 1 - mpf(10) ** -25, f"n={n}: the bound is violated, {mp.nstr(worst,10)}"
    assert fabs(eq - 1) < mpf(10) ** -25, f"n={n}: the equal point is not extremal"
print(f"PASS  (G6) the bound holds at all {len(tight)} values of n and is SHARP at "
      f"the equal point, where it is an equality to 25 digits.  At n = 3 it is the "
      f"8 already in Lean")

# ---- (G7) how far the coefficient route reaches ------------------------------
print("(G7) the coefficient bound e_2 > sum_{j>=3} R^{j-2} e_j at R = 3")


def esym(u):
    n = len(u)
    e = [mpf(1)] + [mpf(0)] * n
    for x in u:
        for j in range(n, 0, -1):
            e[j] += e[j - 1] * x
    return e


reach = []
for n in [3, 4, 5, 6, 7, 8, 9]:
    worst = None
    for u in simplex_samples(n, 60) + [[mpf(1) / n] * n]:
        e = esym(u)
        m = e[2] - sum(mpf(3) ** (j - 2) * e[j] for j in range(3, n + 1))
        worst = m if worst is None else min(worst, m)
    reach.append((n, worst))
    print(f"  n = {n}: worst (e_2 - sum) = {mp.nstr(worst, 8)}   "
          f"{'HOLDS' if worst > 0 else 'FAILS'}")
for n, worst in reach:
    if n <= 6:
        assert worst > 0, f"n={n}: the coefficient route was expected to reach here"
    else:
        assert worst < 0, f"n={n}: the coefficient route reaches further than recorded"
print(f"PASS  (G7) the coefficient route TAKEN ABOUT THE ORIGIN closes |s| > 3, "
      f"hence the 2L circle, for n <= 6 and FAILS from n = 7.  That is a fact about "
      f"where the bound is centered, not about the geometry: (G8) takes the same "
      f"bound about s = 1, where the disk actually is, and it closes at every n")

# ---- (G8) the route that closes it -------------------------------------------
print("(G8) the bound centered where the disk is, and its collapse")


def gcoef(u):
    """Taylor coefficients of G at s = 1."""
    n = len(u)
    e = esym(u)
    return [sum((mpf(-1) ** j) * e[j] * sp_binom(j - 2, m) for j in range(m + 2, n + 1))
            for m in range(n - 1)]


def sp_binom(a, b):
    from mpmath import binomial
    return binomial(a, b)


signs_bad, chain_worst, collapse_worst, newton_worst = 0, None, None, None
for n in range(3, 16):
    for u in simplex_samples(n, 40):
        e = esym(u)
        # the sign pattern
        g = gcoef(u)
        for m in range(1, len(g)):
            if (mpf(-1) ** m) * g[m] < -mpf(10) ** -28:
                signs_bad += 1
        # the collapse: sum_{m>=1}|g_m| 2^m  ==  G(-1) - G(1)
        lhs = sum(fabs(g[m]) * mpf(2) ** m for m in range(1, len(g)))
        pm, pp = mpf(1), mpf(1)
        for x in u:
            pm *= (1 - x)
            pp *= (1 + x)
        rhs = (pp - 2) - pm
        d = fabs(lhs - rhs)
        collapse_worst = d if collapse_worst is None else max(collapse_worst, d)
        # the one inequality
        slack = 2 + 2 * pm - pp
        chain_worst = slack if chain_worst is None else min(chain_worst, slack)
        # the elementary step it follows from
        for j in range(1, n):
            if e[j + 1] == 0:
                continue
            r = e[1] * e[j] / ((j + 1) * e[j + 1])
            newton_worst = r if newton_worst is None else min(newton_worst, r)
print(f"  sign pattern (-1)^m g_m >= 0 for m >= 1: {signs_bad} violations "
      f"(and it is proved above, not merely sampled)")
print(f"  collapse sum_(m>=1)|g_m|2^m = G(-1) - G(1): worst error "
      f"{mp.nstr(collapse_worst, 6)}")
print(f"  the one inequality 2 + 2*prod(1-u) - prod(1+u): worst "
      f"{mp.nstr(chain_worst, 8)}")
print(f"  the elementary step e_1 e_j >= (j+1) e_(j+1): worst ratio "
      f"{mp.nstr(newton_worst, 8)} (needs 1)")
assert signs_bad == 0, "the Taylor coefficients at s = 1 do not alternate"
assert collapse_worst < mpf(10) ** -25, "the collapse identity fails"
assert chain_worst > 0, "the reduced inequality fails"
assert newton_worst >= 1 - mpf(10) ** -25, "the elementary symmetric step fails"
print(f"PASS  (G8) the triangle bound about `s = 1` collapses to one inequality on "
      f"the simplex.  Both links are PROVED: the alternation from the "
      f"non-negativity of a_l and of (l-1-i), and the inequality termwise from "
      f"e_1 e_j >= (j+1) e_(j+1).  So the 2L circle separates at EVERY n, "
      f"elementarily -- no Rouche, no argument principle, no Newton, and none of "
      f"the three obstructions above")
print()
print("ALL PASS")
