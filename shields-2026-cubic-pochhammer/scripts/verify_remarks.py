#!/usr/bin/env python3
r"""Paper section 6 (Concluding remarks).

Verifies the identities behind the three remarks and the structural contrast
between multiplicity 3 and multiplicity 4.

Why the cubic case closes.  The whole conjecture is controlled by
    G_m(p) = p(1-p) P{ Bin(3m-2,p) = 2 (mod 3) },
an exact identity checked symbolically; its monotonicity on [0,1/2] is
Lemma 4.2 (verified in verify_kernel.py).

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
negative (first at m=3), whereas J^{(3)}_m(t) > 0 for every m.  This failure is
concrete: already for the constant sequence f_n = 1 the r=4 Turanian has a
negative coefficient at m=3 with alpha=beta=1.  The coefficient factorizes as
  -(mu-16)(mu+1)(mu+2)^2(mu+3)^2(mu+4)(mu+5)(mu+6)(mu+7)/7560,
so the threshold in mu is 16 -- the coefficient vanishes there and is negative for
every real mu>16; mu=17 is the smallest INTEGER witness, at -87679680.  This
reproduces the numerical counterexample of Karp and Zhang (their Remark 5, the
series psi-tilde_r); the r=3 Turanian stays nonnegative at the same parameters.
The counterexample is verified by three independent routes (the coefficient
convolution, the beta-binomial mixture form, and the symbolic factorization).

Symbolic identities use SymPy; the kernel sign checks and the r=4 counterexample
use exact rational arithmetic.  No floating point anywhere: the ~1e7 sign claim
is an exact integer.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb

import sympy as sp

p, t, x = sp.symbols("p t x")


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
    print("PASS: G^{(r)}_m(p) = p(1-p) P{Bin(rm-2,p) = r-1 (mod r)} for r=2,3,4, "
          "and no other residue class gives the kernel")


def check_general_r_weighted_analogue() -> None:
    """The paper's "and in general its analogue weighted by the products f_k f_{m-k}".

    Section 6 states the general-r reduction in the constant-weight case and then
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
    """Section 6: the positivity "is not termwise obvious in the monomial basis".

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


def check_lifted_array_obstruction() -> None:
    # r=3: the lifted array is entirely nonnegative (the Bernstein certificate)
    for m in range(2, 7):
        assert first_negative(lifted_array(3, m)) is None, m
    # r=4: nonnegative at m=2, but the first obstruction is at index 8 from m=3 on
    assert first_negative(lifted_array(4, 2)) is None
    for m in range(3, 7):
        assert first_negative(lifted_array(4, m)) == 8, m
    print("PASS: lifted array nonneg for r=3; r=4 first obstruction at j=8 (m>=3)")


def check_kernel_sign_contrast(m_max: int = 12) -> None:
    """J^{(3)}_m(t) > 0 on (0,1) for m <= m_max; J^{(4)}_m dips negative at m=3.

    Positivity for r=3 is settled EXACTLY on the tested range by counting roots in
    [0,1]: sp.Poly.count_roots is exact, so "no interior root plus a positive value
    at t=1/2" is a proof for that m.  The statement for every m is Lemma 4.2; what
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
    # r=4: positive on (0,1) for the neighbouring m (constant weights break only at m=3)
    for m in (2, 4, 5, 6, 7):
        n = 4 * m - 2
        for it in range(1, 40):
            tv = Fraction(it, 40)
            val = sum(comb(n, 4 * r - 1) * tv ** (4 * r - 1) * (r - (m - r) * tv)
                      for r in range(1, m))
            assert val > 0, (m, tv)
    print(f"PASS: J^(3)_m > 0 on (0,1) for 2<=m<=12 (exact root count, no interior "
          f"root); J^(4)_3 has an interior sign change, J^(4)_3(3/5) = {j43} < 0")


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
    print(f"PASS: r=4 counterexample f_n=1, m=3, a=b=1: [x^3] = {c_conv} < 0 at mu=17 "
          f"(exact); threshold is mu=16, where it is 0, and negative for all real mu>16 "
          f"(r=3 stays >= 0)")


def main() -> None:
    check_control_quantity()
    check_log_concavity_role()
    check_general_r_kernel()
    check_general_r_weighted_analogue()
    check_not_termwise_obvious()
    check_lifted_array_obstruction()
    check_kernel_sign_contrast()
    check_r4_counterexample()
    print("ALL PASS: verify_remarks")


if __name__ == "__main__":
    main()
