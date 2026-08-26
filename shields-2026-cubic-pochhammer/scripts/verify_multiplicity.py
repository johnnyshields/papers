#!/usr/bin/env python3
r"""Paper section `sec:threshold` (The sharp multiplicity threshold) and section `subsec:first-supercritical-case` (The first
supercritical case), with `sec:reduction`'s weight-monotonicity input
(`lem:central-products`) and `sec:kernel`'s Bernstein array (`lem:bernstein`).

The section's headline identities and the general-r residue-class reduction,
together with the structural contrast between multiplicity 3 and multiplicity 4.

  * `eq:r-degree-three`, the degree-three generalized Turanian at arbitrary multiplicity
    r, against the direct convolution symbolically in mu, and its r=4
    factorization.  Its critical factor r(4r-(r-3)mu) is what classifies the
    multiplicities, and each branch is asserted: 2mu+16 at r=2 and the constant
    36 at r=3, both by their coefficients rather than by sampling, and the whole
    coefficient negative past mu > 4r/(r-3) for r = 4..40, 100, 1000.
  * `eq:r-central-slope`, the kernel's slope in the centrality coordinate at q=1/4, equal to
    C(3r-2,r-1) r(3-r) 2^{2-3r}: positive at r=2, EXACTLY zero at r=3, negative
    for r=4..13.  The same factor r-3 governs the local slope and the
    finite-parameter Turanian, which is why cubic is the threshold.
  * the closed form of G^{(r)}_3, and `prop:multiplicity-threshold`'s local geometry at r=3: the
    quadratic term at the center cancels and the maximum is QUARTICALLY flat.
  * `prop:multiplicity-threshold`'s two minimality clauses, symbolically over the whole cone rather
    than at sampled points: (mu+al)_r(mu+be)_r - (mu)_r(mu+al+be)_r has every
    coefficient positive as a polynomial in (mu, al, be), which settles degree
    two and one-point support at once, with sampled cross-checks retained.

Why the cubic case closes.  The whole conjecture is controlled by
    G_m(p) = p(1-p) P{ Bin(3m-2,p) = 2 (mod 3) },
an exact identity checked symbolically; its monotonicity on [0,1/2] is
`lem:bernstein` (verified in verify_kernel.py).

The role of log-concavity.  Log-concavity is used once, to make the symmetric
weights w_k = f_k f_{m-k} nondecreasing toward the center; a sequence that is
not log-concave can break this, so the hypothesis is load-bearing.

Higher multiplicities.  For general r the constant-weight kernel is
    G^{(r)}_m(p) = p(1-p) P{ Bin(rm-2,p) = r-1 (mod r) },
checked for r = 2,3,4.  The Bernstein positivity that certifies the r=3 kernel
does not persist: the lifted coefficient array (the coefficients of the
projective transform P^{(r)}_m) is entirely nonnegative for r=3 but acquires
negative entries for r=4, the first obstruction sitting at index j=8 and first
appearing at m=3.  Correspondingly the constant-weight kernel J^{(4)}_m(t) dips
negative at m=3 and, over the computed range 4 <= m <= 22, nowhere else, whereas
J^{(3)}_m(t) > 0 for every m.  This failure is concrete: already for the two-term
sequence f_1=f_2=1, f_n=0 (n>=3) of `prop:multiplicity-threshold` -- equivalently
f_n = 1, only k=1,2 contributing at m=3 -- the r=4 Turanian has a
negative coefficient at m=3 with alpha=beta=1.  The coefficient factorizes as
  -(mu-16)(mu+1)(mu+2)^2(mu+3)^2(mu+4)(mu+5)(mu+6)(mu+7)/7560,
so the threshold in mu is 16 -- the coefficient vanishes there and is negative for
every real mu>16; mu=17 is the smallest INTEGER witness, at -87679680.  This
reproduces the numerical counterexample of Karp and Zhang (their Remark 5, the
series psi-tilde_r); the r=3 Turanian stays nonnegative at the same parameters.
The counterexample is verified by three independent routes (the coefficient
convolution, the beta-binomial mixture form, and the symbolic factorization).

The r=4 lifted array and its closed forms in m belong to
`check_r4_obstruction.py`, which proves them for every m; what is kept here is
the J^{(4)}_3 closed form the paper displays nowhere, which that file does not
carry.

Symbolic identities use SymPy; the kernel sign checks and the r=4 counterexample
use exact rational arithmetic.  No floating point anywhere: the ~8.8e7 sign claim
is an exact integer.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb

import sympy as sp

p, t, x = sp.symbols("p t x")
mu, q = sp.symbols("mu q")
R = sp.Rational


# ===========================================================================
# Why the cubic case closes: the control quantity
# ===========================================================================
def check_control_quantity() -> None:
    """G_m(p) = p(1-p) P{Bin(3m-2,p) = 2 (mod 3)}."""
    for m in range(2, 7):
        n = 3 * m - 2
        G = sum(comb(n, 3 * r - 1) * p ** (3 * r) * (1 - p) ** (3 * (m - r))
                for r in range(1, m))
        prob = sum(comb(n, k) * p ** k * (1 - p) ** (n - k)
                   for k in range(n + 1) if k % 3 == 2)
        assert sp.expand(G - p * (1 - p) * prob) == 0, m
    print("PASS: G_m(p) = p(1-p) P{Bin(3m-2,p) = 2 (mod 3)}")


# ===========================================================================
# The role of log-concavity: w_k = f_k f_{m-k} nondecreasing (and its failure)
# ===========================================================================
def check_log_concavity_role() -> None:
    # log-concave, no internal zeros -> w_k nondecreasing toward the center
    f = {1: Fraction(1), 2: Fraction(4), 3: Fraction(9), 4: Fraction(16), 5: Fraction(25)}
    ks = sorted(f)
    for i in range(1, len(ks) - 1):
        assert f[ks[i]] ** 2 >= f[ks[i - 1]] * f[ks[i + 1]]
    for m in (5, 6, 7, 8, 9):
        w = {r: f.get(r, Fraction(0)) * f.get(m - r, Fraction(0)) for r in range(1, m)}
        for r in range(1, m // 2):
            assert w[r + 1] >= w[r]
    # a non-log-concave sequence breaks monotonicity of the paired weights
    g = {1: Fraction(1), 2: Fraction(10), 3: Fraction(1), 4: Fraction(10), 5: Fraction(1)}
    assert g[3] ** 2 < g[2] * g[4]                                 # not log-concave
    m = 6
    wg = {r: g.get(r, Fraction(0)) * g.get(m - r, Fraction(0)) for r in range(1, m)}
    assert not all(wg[r + 1] >= wg[r] for r in range(1, m // 2))   # w not monotone
    # The implication is one-directional at fixed m.  Log-concavity gives w_k
    # nondecreasing for EVERY m, and quantifying over all m recovers log-concavity,
    # but no SINGLE m does: at m the condition constrains f only at the indices the
    # pairing reaches.  Witness: (f_n) not log-concave whose weights are still
    # nondecreasing at m=4, because m=4 tests only w_1 <= w_2, i.e. log-concavity
    # at n=2, while the failure sits at n=3.
    h = {1: Fraction(1), 2: Fraction(2), 3: Fraction(1), 4: Fraction(9)}
    assert h[2] ** 2 >= h[1] * h[3]                                # holds at n=2
    assert h[3] ** 2 < h[2] * h[4]                                 # FAILS at n=3
    m = 4
    wh = {r: h.get(r, Fraction(0)) * h.get(m - r, Fraction(0)) for r in range(1, m)}
    assert all(wh[r + 1] >= wh[r] for r in range(1, m // 2))        # yet w monotone at m=4
    # and the failure does surface once a larger m reaches index 3
    m = 6
    wh6 = {r: h.get(r, Fraction(0)) * h.get(m - r, Fraction(0)) for r in range(1, m)}
    assert not all(wh6[r + 1] >= wh6[r] for r in range(1, m // 2))
    print("PASS: log-concavity => w_k nondecreasing (load-bearing hypothesis); no "
          "single m recovers the converse, though all m together do")


# ===========================================================================
# Higher multiplicities: general-r kernel and the r=4 obstruction
# ===========================================================================
def general_r_kernel(rmult: int, m: int):
    """The constant-weight kernel of the general-`r` family `eq:general-r`, at
    degree `m`: the coefficient convolution of `F_{f,r}` read off the residue
    class, `p(1-p) P{Bin(rm-2,p) = r-1 (mod r)}`."""
    n = rmult * m - 2
    return sum(comb(n, rmult * r - 1) * p ** (rmult * r) * (1 - p) ** (rmult * (m - r))
               for r in range(1, m))


def check_general_r_kernel() -> None:
    for rmult in (2, 3, 4):
        for m in range(2, 6):
            n = rmult * m - 2
            prob = sum(comb(n, k) * p ** k * (1 - p) ** (n - k)
                       for k in range(n + 1) if k % rmult == (rmult - 1) % rmult)
            assert sp.expand(general_r_kernel(rmult, m) - p * (1 - p) * prob) == 0, (rmult, m)
            # only the residue class r-1 works: the other classes are not the kernel
            for other in range(rmult - 1):
                probo = sum(comb(n, k) * p ** k * (1 - p) ** (n - k)
                            for k in range(n + 1) if k % rmult == other)
                assert sp.expand(general_r_kernel(rmult, m)
                                 - p * (1 - p) * probo) != 0, (rmult, m, other)
    print("PASS: `eq:general-r`'s kernel G^{(r)}_m(p) = p(1-p) P{Bin(rm-2,p) = r-1 "
          "(mod r)} for r=2,3,4, and no other residue class gives the kernel")


def check_general_r_weighted_analogue() -> None:
    """The general-r analogue weighted by the products f_k f_{m-k}.  Not a paper
    display; the paper states the constant-weight reduction only.

    `sec:threshold` states the general-r reduction in the constant-weight case and then
    says the weighted analogue holds too.  With symbolic weights w_k, the weighted
    general-r kernel is the same p(1-p) * (weighted residue-class sum), and it
    reproduces the coefficient convolution through the beta-binomial mixture --
    checked here with symbolic w, so it is the identity and not one instance.
    """
    for rmult in (2, 3, 4):
        for m in range(2, 6):
            n = rmult * m - 2
            w = sp.symbols(f"w1:{m}")
            wmap = {k: w[min(k, m - k) - 1] for k in range(1, m)}   # symmetric
            Gw = sum(wmap[k] * comb(n, rmult * k - 1)
                     * p ** (rmult * k) * (1 - p) ** (rmult * (m - k))
                     for k in range(1, m))
            # the weighted residue-class form: weight w_{j/r} on j = rk
            weighted_prob = sum(
                wmap[j // rmult] * comb(n, j - 1) * p ** (j - 1) * (1 - p) ** (n - j + 1)
                for j in range(rmult, rmult * m, rmult) if j // rmult in wmap)
            assert sp.expand(Gw - p * (1 - p) * weighted_prob) == 0, (rmult, m)
            # p <-> 1-p symmetry survives the weighting
            assert sp.expand(Gw - Gw.subs(p, 1 - p)) == 0, (rmult, m)
    print("PASS: the weighted general-r analogue -- symbolic w_k, r=2,3,4 -- is the "
          "same p(1-p) * (weighted residue-class sum), and stays p <-> 1-p symmetric")


def check_not_termwise_obvious() -> None:
    """Positivity is not termwise in the monomial basis -- the motivation for the
    Bernstein route of `lem:bernstein` `eq:G-J`.  Not a paper display.

    J_m has genuinely negative monomial coefficients for every m in range, while
    every Bernstein coefficient is nonnegative -- which is exactly why the paper
    needs the projective transform rather than a termwise bound.
    """
    neg_ms = []
    for m in range(2, 12):
        poly = sp.Poly(sp.expand(Jr_gen(3, m)), t)
        negs = [c for c in poly.all_coeffs() if c < 0]
        assert negs, ("expected negative monomial coefficients", m)
        neg_ms.append(m)
    # the smallest case, explicitly
    assert sp.expand(Jr_gen(3, 3) - (21 * t ** 2 - 42 * t ** 3
                                     + 42 * t ** 5 - 21 * t ** 6)) == 0
    # yet the Bernstein array is nonnegative on the same range
    for m in range(2, 12):
        assert all(c >= 0 for c in lifted_array(3, m)), m
    print(f"PASS: J_m has negative MONOMIAL coefficients for every m in "
          f"{neg_ms[0]}..{neg_ms[-1]} while every Bernstein coefficient is >= 0 "
          f"-- positivity is not termwise in the monomial basis")


def Jr_gen(rmult: int, m: int):
    n = rmult * m - 2
    return sum(comb(n, rmult * r - 1) * t ** (rmult * r - 1) * (r - (m - r) * t)
               for r in range(1, m))


def lifted_array(rmult: int, m: int) -> list:
    """Coefficients of P^{(r)}_m(x) = (1+x)^{n+1} J^{(r)}_m(x/(1+x))."""
    n = rmult * m - 2
    poly = sp.Poly(sp.expand(sp.cancel((1 + x) ** (n + 1) * Jr_gen(rmult, m).subs(t, x / (1 + x)))), x)
    return [int(poly.coeff_monomial(x ** j)) for j in range(n + 2)]


def first_negative(coeffs: list):
    for j, c in enumerate(coeffs):
        if c < 0:
            return j
    return None


def check_r4_m3_displayed_forms() -> None:
    """The r = 4, m = 3 obstruction in closed form -- a script-side extra the paper
    displays nowhere -- asserted against Jr_gen and the projective lift rather than
    transcribed:

        J^{(4)}_3(t) = 120 t^3 (1 - 2t + 2t^4 - t^5)

        (1+x)^11 J^{(4)}_3(x/(1+x))
            = 120x^3 + 720x^4 + 1680x^5 + 1680x^6 + 240x^7
              - 840x^8 - 600x^9 - 120x^10

    Exact over the integers.  The lifted ARRAY, its first negative index, and
    the closed forms of a_7, a_8, a_9 in m belong to `check_r4_obstruction.py`,
    which settles them for every m rather than at m=3; what is pinned here is
    the J^{(4)}_3 algebra that file does not carry.
    """
    closed = sp.expand(120 * t ** 3 * (1 - 2 * t + 2 * t ** 4 - t ** 5))
    assert sp.expand(Jr_gen(4, 3) - closed) == 0
    # the equivalent factored form, so neither display can drift unnoticed
    assert sp.expand(closed + 120 * t ** 3 * (t - 1)
                     * (t ** 4 - t ** 3 - t ** 2 - t + 1)) == 0
    # `eq:P-def` lifts by (1+x)^{n+1} with n+1 = rm-1, so the lift has degree at
    # most rm-1 and its top coefficient is J^{(r)}_m(1) -- read off the
    # polynomial rather than written down, for r = 3, 4 and several m.  It is
    # exactly rm-1 when J^{(r)}_m(1) != 0, and one less when the top cancels,
    # which is what puts the trailing zero on the m=3 array above.
    tops = 0
    for rmult in (3, 4):
        for mm in range(2, 7):
            J = Jr_gen(rmult, mm)
            lift = sp.Poly(sp.expand(sp.cancel(
                (1 + x) ** (rmult * mm - 1) * J.subs(t, x / (1 + x)))), x)
            assert lift.degree() <= rmult * mm - 1, (rmult, mm, lift.degree())
            top = lift.coeff_monomial(x ** (rmult * mm - 1))
            assert top == sp.expand(J.subs(t, 1)), (rmult, mm, top)
            assert (lift.degree() == rmult * mm - 1) == (top != 0), (rmult, mm)
            tops += 1
    assert sp.expand(Jr_gen(4, 3).subs(t, 1)) == 0                 # the m=3 cancellation
    print(f"PASS: the J^(4)_3 closed form and its factored equivalent are exact, "
          f"and the projective lift of `eq:P-def` has degree rm-1 with top "
          f"coefficient J^(r)_m(1) ({tops} cases, r = 3,4)")


def check_kernel_sign_contrast(m_max: int = 12) -> None:
    """J^{(3)}_m(t) > 0 on (0,1) for m <= m_max; J^{(4)}_m dips negative at m=3.

    Positivity for r=3 is settled EXACTLY on the tested range by counting roots in
    [0,1]: sp.Poly.count_roots is exact, so "no interior root plus a positive value
    at t=1/2" is a proof for that m.  The statement for every m is `lem:bernstein`; what
    this function adds is the contrast with r=4.
    """
    for m in range(2, m_max + 1):
        n = 3 * m - 2
        poly = sp.Poly(sp.expand(Jr_gen(3, m)), t)
        # roots in [0,1] are exactly the boundary ones t=0 and t=1
        interior = poly.count_roots(0, 1) - sum(
            1 for b in (sp.Integer(0), sp.Integer(1)) if poly.eval(b) == 0)
        assert interior == 0, (m, interior)
        assert poly.eval(sp.Rational(1, 2)) > 0, m
        for it in range(1, 40):
            tv = Fraction(it, 40)
            val = sum(comb(n, 3 * r - 1) * tv ** (3 * r - 1) * (r - (m - r) * tv)
                      for r in range(1, m))
            assert val > 0, (m, tv)
    # r=4, m=3 genuinely has an interior sign change -- the structural contrast
    poly4 = sp.Poly(sp.expand(Jr_gen(4, 3)), t)
    interior4 = poly4.count_roots(0, 1) - sum(
        1 for b in (sp.Integer(0), sp.Integer(1)) if poly4.eval(b) == 0)
    assert interior4 >= 1, interior4
    # r=4: an explicit negative value at m=3
    m, tv = 3, Fraction(3, 5)
    n = 4 * m - 2
    j43 = sum(comb(n, 4 * r - 1) * tv ** (4 * r - 1) * (r - (m - r) * tv) for r in range(1, m))
    assert j43 < 0, j43
    # r=4: positive on (0,1) for the neighboring m (constant weights break only at m=3)
    for m in (2, 4, 5, 6, 7):
        n = 4 * m - 2
        for it in range(1, 40):
            tv = Fraction(it, 40)
            val = sum(comb(n, 4 * r - 1) * tv ** (4 * r - 1) * (r - (m - r) * tv)
                      for r in range(1, m))
            assert val > 0, (m, tv)
    # r=4 is obstructed at m=3 only over the computed range: for 4 <= m <= 22 the
    # constant-weight derivative has no interior root and is positive throughout, so
    # there is no shrinking-interval phenomenon.  This is evidence for the question
    # `sec:conclusion` (Concluding remarks) leaves open -- whether the constant-weight kernel
    # at multiplicity four stays monotone in every degree.  The index-9 / m >= 7 form
    # of it is check_r4_obstruction.py's own lead, not a paper claim.
    clean4 = []
    for mm in range(4, 23):
        p4 = sp.Poly(sp.expand(Jr_gen(4, mm)), t)
        interior4m = p4.count_roots(0, 1) - sum(
            1 for b in (sp.Integer(0), sp.Integer(1)) if p4.eval(b) == 0)
        assert interior4m == 0, (mm, interior4m)
        for tv in (sp.Rational(1, 10), sp.Rational(1, 2), sp.Rational(9, 10)):
            assert p4.eval(tv) > 0, (mm, tv)
        clean4.append(mm)
    assert clean4 == list(range(4, 23))
    print(f"PASS: J^(3)_m > 0 on (0,1) for 2<=m<=12 (exact root count, no interior "
          f"root); J^(4)_3 has an interior sign change, J^(4)_3(3/5) = {j43} < 0 -- "
          f"and m=3 is the ONLY obstructed degree at r=4 over 4<=m<=22, where "
          f"J^(4)_m has no interior root and is positive throughout")


# ---------------------------------------------------------------------------
# The r=4 failure, reproduced exactly for the constant sequence f_n = 1
# ---------------------------------------------------------------------------
def _fact(n: int) -> int:
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


def _poch(u: Fraction, j: int) -> Fraction:
    q = Fraction(1)
    for i in range(j):
        q *= u + i
    return q


def _turan_const_conv(rmult: int, m: int, mu, al, be) -> Fraction:
    """[x^m] of the r-th Turanian for f_n = 1, via the coefficient convolution."""
    def C(u, v):
        return sum(_poch(u, rmult * k) * _poch(v, rmult * (m - k))
                   / (_fact(rmult * k - 1) * _fact(rmult * (m - k) - 1))
                   for k in range(1, m))
    return C(mu + al, mu + be) - C(mu, mu + al + be)


def _turan_const_beta(rmult: int, m: int, mu, al, be) -> Fraction:
    """Same coefficient via the beta-binomial mixture form (independent route)."""
    N = rmult * m
    def C(u, v):
        pref = _poch(u + v, N) / _fact(N) * N * (N - 1)
        return pref * sum(comb(rmult * m - 2, rmult * k - 1)
                          * _poch(u, rmult * k) * _poch(v, rmult * (m - k)) / _poch(u + v, N)
                          for k in range(1, m))
    return C(mu + al, mu + be) - C(mu, mu + al + be)


def check_r4_counterexample() -> None:
    mu, al, be, m = Fraction(17), Fraction(1), Fraction(1), 3
    c_conv = _turan_const_conv(4, m, mu, al, be)
    c_beta = _turan_const_beta(4, m, mu, al, be)
    assert c_conv == c_beta, (c_conv, c_beta)                 # two routes agree
    assert c_conv < 0, c_conv                                 # negative -> not log-concave
    assert c_conv == Fraction(-87679680), c_conv              # exact, not a float sign
    # The threshold in mu is 16, not 17: the coefficient factorizes as
    #   -(mu-16)(mu+1)(mu+2)^2(mu+3)^2(mu+4)(mu+5)(mu+6)(mu+7)/7560,
    # so it VANISHES at mu=16 and is negative for every real mu>16.  mu=17 is only
    # the smallest INTEGER witness; mu=16 passing a ">= 0" test does so by equality,
    # which is a weak witness for a claimed sign change, so mu=15 is asserted too.
    assert _turan_const_conv(4, m, Fraction(16), al, be) == 0
    assert _turan_const_conv(4, m, Fraction(15), al, be) == Fraction(34790976) > 0
    mus = sp.symbols("mus")
    factored = sp.factor(sp.together(sum(
        (sp.rf(mus + 1, 4 * k) / sp.factorial(4 * k - 1))
        * (sp.rf(mus + 1, 4 * (m - k)) / sp.factorial(4 * (m - k) - 1))
        - (sp.rf(mus, 4 * k) / sp.factorial(4 * k - 1))
        * (sp.rf(mus + 2, 4 * (m - k)) / sp.factorial(4 * (m - k) - 1))
        for k in range(1, m))))
    claimed = -((mus - 16) * (mus + 1) * (mus + 2) ** 2 * (mus + 3) ** 2
                * (mus + 4) * (mus + 5) * (mus + 6) * (mus + 7)) / 7560
    assert sp.simplify(sp.expand(factored - claimed)) == 0, factored
    # negative for every real mu > 16, integer or not
    for v in ("16.0001", "16.5", "23", "500"):
        assert factored.subs(mus, sp.Rational(v)) < 0, v
    for v in ("0", "1", "9", "15.9999"):
        assert factored.subs(mus, sp.Rational(v)) >= 0, v
    for mm in range(2, 9):                                    # the cubic case holds here
        assert _turan_const_conv(3, mm, mu, al, be) >= 0
    # A second witness at different shifts, independent of the mu-threshold route
    # above: at a=b=2 the failure is already present AT mu=16, where a=b=1 gives
    # exactly zero.  Corroborates the first from a different direction.
    c2 = _turan_const_conv(4, 3, 16, 2, 2)
    assert c2 == -9229440, c2
    assert _turan_const_conv(4, 3, 16, 1, 1) == 0
    assert _turan_const_conv(3, 3, 16, 2, 2) > 0               # cubic still holds
    print(f"PASS: r=4 counterexample f_n=1, m=3, a=b=1: [x^3] = {c_conv} < 0 at mu=17 "
          f"(exact); threshold is mu=16, where it is 0, and negative for all real mu>16. "
          f"Second witness at a=b=2 is already negative AT mu=16, [x^3] = {c2} "
          f"(r=3 stays >= 0 throughout)")


# ===========================================================================
# `sec:threshold`'s headline identities
# ===========================================================================
def poch(a, j):
    out = sp.Integer(1)
    for i in range(j):
        out *= a + i
    return out


def a_coeff(n, m, r):
    """Coefficient of x^n in F_{1,r}(m;x)."""
    return poch(m, r * n) / sp.factorial(r * n - 1)


def closed_form(r):
    """`eq:r-degree-three`."""
    return (r * (4 * r - (r - 3) * mu) * poch(mu + 2, r - 2) * poch(mu + 1, 2 * r - 1)
            / (sp.factorial(r - 1) * sp.factorial(2 * r - 1)))


def check_all_r_degree_three():
    """`eq:r-degree-three` against the direct convolution, symbolically in mu."""
    for r in range(2, 16):
        direct = sp.expand(2 * a_coeff(1, mu + 1, r) * a_coeff(2, mu + 1, r)
                           - a_coeff(1, mu, r) * a_coeff(2, mu + 2, r)
                           - a_coeff(2, mu, r) * a_coeff(1, mu + 2, r))
        assert sp.simplify(sp.together(direct - closed_form(r))) == 0, r
    # and it must reproduce the r=4 factorization the proposition also displays
    r4 = -((mu - 16) * (mu + 1) * (mu + 2) ** 2 * (mu + 3) ** 2
           * (mu + 4) * (mu + 5) * (mu + 6) * (mu + 7)) / 7560
    assert sp.simplify(sp.expand(closed_form(4) - r4)) == 0
    print("PASS  `eq:r-degree-three` equals the direct degree-three convolution, r = 2..15, "
          "and specializes to the r=4 factorization")


def check_multiplicity_classification():
    """`cor:multiplicity`: the critical factor classifies r.

    At r = 2 and r = 3 the factor is positive for EVERY mu >= 0, and that is
    settled by its coefficients rather than by sampling: it expands to 2mu + 16
    at r = 2 and to the constant 36 at r = 3, the mu term canceling outright
    because r - 3 = 0.  Sampling five values of mu tested a polynomial identity
    at five points; the coefficients test it everywhere.
    """
    assert sp.Poly(2 * (4 * 2 - (2 - 3) * mu), mu).all_coeffs() == [2, 16]
    assert sp.Poly(3 * (4 * 3 - (3 - 3) * mu), mu).all_coeffs() == [36]
    for r in (2, 3):
        crit = sp.Poly(sp.expand(r * (4 * r - (r - 3) * mu)), mu)
        assert all(c > 0 for c in crit.all_coeffs()), (r, crit.all_coeffs())
        assert crit.eval(0) > 0, r                       # so crit > 0 for every mu >= 0
        for v in [0, 1, 10, 10 ** 3, 10 ** 6]:           # sampled cross-check
            assert crit.eval(v) > 0, (r, v)
    for r in list(range(4, 41)) + [100, 1000]:
        thr = R(4 * r, r - 3)
        crit = r * (4 * r - (r - 3) * mu)
        assert sp.nsimplify(crit.subs(mu, thr), rational=True) == 0, r
        assert sp.nsimplify(crit.subs(mu, thr + R(1, 10)), rational=True) < 0, r
        assert sp.nsimplify(crit.subs(mu, thr - R(1, 10)), rational=True) > 0, r
        # the whole coefficient, not only the factor, is negative past the threshold
        assert sp.nsimplify(closed_form(r).subs(mu, thr + 1), rational=True) < 0, r
        if r == 4:
            assert thr == 16, thr                        # the paper's own threshold
    print("PASS  `cor:multiplicity`: the critical factor is 2mu+16 at r=2 and the constant 36 "
          "at r=3, positive for every mu >= 0 by its COEFFICIENTS; negative past "
          "mu = 4r/(r-3) for r = 4..40, 100, 1000, that threshold being mu > 16 at r = 4")


def check_two_term_witness():
    """f_1 = f_2 = 1 realizes the same coefficient, and is admissible."""
    f = {1: sp.Integer(1), 2: sp.Integer(1)}
    sup = sorted(n for n in f if f[n] > 0)
    assert sup == list(range(sup[0], sup[-1] + 1))            # interval support
    assert f[2] ** 2 >= f[1] * 0                              # log-concave
    for r in range(2, 12):
        F = lambda m: sum(f.get(n, 0) * poch(m, r * n) / sp.factorial(r * n - 1) * x ** n
                          for n in (1, 2, 3))
        coef = sp.expand(sp.expand(F(mu + 1) ** 2 - F(mu) * F(mu + 2)).coeff(x, 3))
        assert sp.simplify(coef - closed_form(r)) == 0, r
    print("PASS  f = (1,1,0,0,...) is log-concave with interval support and gives the "
          "same degree-three coefficient, r = 2..11")


def check_central_slope():
    """`eq:r-central-slope`: the kernel's slope in q at the center, and its sign."""
    xx = sp.Symbol('xx')
    for r in range(2, 14):
        # the kernel at m=3 from the definition, then in the centrality coordinate
        G_def = sum(sp.binomial(3 * r - 2, r * k - 1) * p ** (r * k) * (1 - p) ** (r * (3 - k))
                    for k in (1, 2))
        G_cl = sp.binomial(3 * r - 2, r - 1) * p ** r * (1 - p) ** r * (p ** r + (1 - p) ** r)
        assert sp.simplify(sp.expand(G_def - G_cl)) == 0, r
        G = sp.binomial(3 * r - 2, r - 1) * (R(1, 4) - xx ** 2) ** r \
            * ((R(1, 2) + xx) ** r + (R(1, 2) - xx) ** r)
        slope = sp.limit(sp.diff(G, xx) / (-2 * xx), xx, 0)     # dG/dq at q=1/4
        claim = sp.binomial(3 * r - 2, r - 1) * r * (3 - r) * sp.Integer(2) ** (2 - 3 * r)
        assert sp.simplify(slope - claim) == 0, (r, slope)
        assert sp.sign(slope) == (1 if r == 2 else (0 if r == 3 else -1)), r
    # r=3 explicitly: p^3+(1-p)^3 = 1-3q, so the kernel is 21 q^3 (1-3q)
    assert sp.simplify(sp.expand(p ** 3 + (1 - p) ** 3 - (1 - 3 * p * (1 - p)))) == 0
    G3 = 21 * q ** 3 * (1 - 3 * q)
    assert sp.simplify(sp.expand(sp.diff(G3, q) - 63 * q ** 2 * (1 - 4 * q))) == 0
    assert sp.diff(G3, q).subs(q, R(1, 4)) == 0
    for v in [R(1, 100), R(1, 8), R(1, 5), R(24, 100)]:
        assert sp.nsimplify(sp.diff(G3, q).subs(q, v), rational=True) > 0
    print("PASS  `eq:r-central-slope` = C(3r-2,r-1) r(3-r) 2^{2-3r}: > 0 at r=2, EXACTLY 0 at r=3, "
          "< 0 for r = 4..13; at r=3 the kernel is 21q^3(1-3q), rising on (0,1/4)")


def check_r3_quartically_flat():
    """`prop:multiplicity-threshold`: at r=3 the quadratic term cancels and the center is quartically flat."""
    xx = sp.Symbol('xx')
    e = sp.expand((21 * (p * (1 - p)) ** 3 * (1 - 3 * p * (1 - p))).subs(p, R(1, 2) + xx))
    assert sp.expand(e - (R(21, 256) - R(63, 8) * xx ** 4
                          + 42 * xx ** 6 - 63 * xx ** 8)) == 0, sp.expand(e)
    for r in range(2, 15):
        G = sp.binomial(3 * r - 2, r - 1) * (p * (1 - p)) ** r * (p ** r + (1 - p) ** r)
        P = sp.Poly(sp.expand(G.subs(p, R(1, 2) + xx)), xx)
        c2, c4 = P.coeff_monomial(xx ** 2), P.coeff_monomial(xx ** 4)
        if r == 2:
            assert c2 < 0, r                       # quadratic maximum
        elif r == 3:
            assert c2 == 0 and c4 < 0, (r, c2, c4)  # cancels; quartic maximum
        else:
            assert c2 > 0, (r, c2)                  # quadratic minimum
    print("PASS  `prop:multiplicity-threshold`: G^(3)_3(1/2+x) = 21/256 - (63/8)x^4 + 42x^6 - 63x^8, so the "
          "center is a quartically flat maximum; the x^2 coefficient is < 0 at r=2, "
          "EXACTLY 0 at r=3, and > 0 for r = 4..14")


def check_minimality_over_the_whole_cone():
    r"""`prop:multiplicity-threshold`'s minimality clauses, over the whole parameter cone at once.

    Both clauses reduce to one polynomial statement: for every N >= 1,

        (mu+al)_N (mu+be)_N - (mu)_N (mu+al+be)_N

    has every coefficient POSITIVE as a polynomial in (mu, al, be), and no
    constant term.  Hence it is > 0 whenever al, be > 0 and mu >= 0 -- the whole
    cone, including the paper's own al = be = 1, which no sampled grid below
    contains.  Degree two is this at N = r, and a one-point support {a} is this
    at N = ra, so a single symbolic assertion covers both.
    """
    al, be = sp.symbols('al be')
    for N in range(1, 12):
        e = sp.expand(poch(mu + al, N) * poch(mu + be, N)
                      - poch(mu, N) * poch(mu + al + be, N))
        P = sp.Poly(e, mu, al, be)
        cs = P.coeffs()
        assert cs and all(c > 0 for c in cs), (N, min(cs))
        assert P.eval({mu: 0, al: 0, be: 0}) == 0, N        # no constant term
        # and the paper's own point, which the sampled grids miss
        assert e.subs({al: 1, be: 1, mu: 0}) > 0, N
        for mv in (0, sp.Rational(1, 3), 4, 31):
            assert e.subs({al: 1, be: 1, mu: mv}) > 0, (N, mv)
    print("PASS  `prop:multiplicity-threshold`: (mu+al)_N(mu+be)_N - (mu)_N(mu+al+be)_N has every coefficient "
          "positive in (mu,al,be) and no constant term, for N = 1..11 -- so both "
          "minimality clauses hold on the whole cone, alpha=beta=1 included")


def check_degree_and_support_minimal():
    """`prop:multiplicity-threshold`: degree three and two support points are both minimal.

    The sampled cross-check kept beside check_minimality_over_the_whole_cone:
    what is added here is that the degree-two coefficient IS that Turanian and
    that a one-point support has 2a as its only active degree, neither of which
    the symbolic statement says.
    """
    # (mu)_N is log-concave, so its generalized Turanian is nonnegative
    for N in range(1, 10):
        d2 = sp.diff(sum(sp.log(mu + j) for j in range(N)), mu, 2)
        assert sp.simplify(d2 + sum(1 / (mu + j) ** 2 for j in range(N))) == 0, N
    pts = [(R(a, 3), R(b, 2), R(c, 5)) for a in (0, 1, 4, 31)
           for b in (1, 3, 9) for c in (1, 7, 23)]
    # degree two: only k=1 contributes, and the coefficient is that Turanian at N=r
    for r in range(2, 13):
        for mv, av, bv in pts:
            F = lambda m: poch(m, r) / sp.factorial(r - 1) * x
            direct = sp.Rational(sp.expand(F(mv + av) * F(mv + bv)
                                           - F(mv) * F(mv + av + bv)).coeff(x, 2))
            closed = sp.Rational((poch(mv + av, r) * poch(mv + bv, r)
                                  - poch(mv, r) * poch(mv + av + bv, r))
                                 / sp.factorial(r - 1) ** 2)
            assert direct == closed and direct > 0, (r, mv, av, bv)
    print(f"PASS  `prop:multiplicity-threshold`: the degree-two coefficient is f_1^2 times the Turanian of "
          f"(mu)_r, POSITIVE at all {len(pts)} rational points for r = 2..12, so degree "
          f"two can never be the first failure")
    # one-point support {a}: the only active degree is 2a, with the Turanian of (mu)_{ra}
    n = 0
    for r in range(2, 9):
        for a in (1, 2, 3):
            for mv, av, bv in pts[:18]:
                F = lambda m: poch(m, r * a) / sp.factorial(r * a - 1) * x ** a
                D = sp.expand(F(mv + av) * F(mv + bv) - F(mv) * F(mv + av + bv))
                assert [d for d in range(1, 2 * a + 2)
                        if sp.expand(D.coeff(x, d)) != 0] == [2 * a], (r, a)
                c = sp.Rational(D.coeff(x, 2 * a))
                t = sp.Rational((poch(mv + av, r * a) * poch(mv + bv, r * a)
                                 - poch(mv, r * a) * poch(mv + av + bv, r * a))
                                / sp.factorial(r * a - 1) ** 2)
                assert c == t and c > 0, (r, a, mv, av, bv)
                n += 1
    print(f"PASS  `prop:multiplicity-threshold`: one-point support has 2a as its only active degree, with the "
          f"Turanian of (mu)_{{ra}} there, positive at all {n} points -- so f_1=f_2=1 uses "
          f"the smallest possible support")


def main() -> None:
    check_all_r_degree_three()
    check_multiplicity_classification()
    check_two_term_witness()
    check_central_slope()
    check_r3_quartically_flat()
    check_minimality_over_the_whole_cone()
    check_degree_and_support_minimal()
    check_control_quantity()
    check_log_concavity_role()
    check_general_r_kernel()
    check_general_r_weighted_analogue()
    check_not_termwise_obvious()
    check_r4_m3_displayed_forms()
    check_kernel_sign_contrast()
    check_r4_counterexample()
    print("ALL PASS: verify_multiplicity")


if __name__ == "__main__":
    main()
