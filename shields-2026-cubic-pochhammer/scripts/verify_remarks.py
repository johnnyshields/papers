#!/usr/bin/env python3
r"""Paper section 6 (Concluding remarks).

Verifies the identities behind the three remarks and the structural contrast
between multiplicity 3 and multiplicity 4.

Why the cubic case closes.  The whole conjecture is controlled by
    G_m(p) = p(1-p) P{ Bin(3m-2,p) = 2 (mod 3) },
an exact identity checked symbolically; its monotonicity on [0,1/2] is
Lemma 4.2 (verified in verify_kernel.py).

The role of log-concavity.  Log-concavity is used once, to make the symmetric
weights w_r = f_r f_{m-r} nondecreasing toward the center; a sequence that is
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
negative coefficient at m=3, the smallest such shift being mu=17 with
alpha=beta=1 (mu=16 is still nonnegative), reproducing the numerical
counterexample of Karp and Zhang (their Remark 3.7, the series psi-tilde_r);
the r=3 Turanian stays nonnegative at the same parameters.  The counterexample
is verified by two independent routes (the coefficient convolution and the
beta-binomial mixture form).

Symbolic identities use SymPy; the kernel sign checks and the r=4 counterexample
use exact rational arithmetic.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb

import mpmath as mp
import sympy as sp

mp.mp.dps = 40
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
# The role of log-concavity: w_r = f_r f_{m-r} nondecreasing (and its failure)
# ===========================================================================
def check_log_concavity_role() -> None:
    # log-concave, no internal zeros -> w_r nondecreasing toward the center
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
    print("PASS: log-concavity <=> w_r nondecreasing (load-bearing hypothesis)")


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
    print("PASS: G^{(r)}_m(p) = p(1-p) P{Bin(rm-2,p) = r-1 (mod r)} for r=2,3,4")


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


def check_kernel_sign_contrast() -> None:
    """J^{(3)}_m(t) > 0 for all m; J^{(4)}_m(t) dips negative first at m=3."""
    # r=3: strictly positive on (0,1)
    for m in range(2, 13):
        n = 3 * m - 2
        for it in range(1, 40):
            tv = Fraction(it, 40)
            val = sum(comb(n, 3 * r - 1) * tv ** (3 * r - 1) * (r - (m - r) * tv)
                      for r in range(1, m))
            assert val > 0, (m, tv)
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
    print(f"PASS: J^(3)_m > 0 for all m; J^(4)_3(3/5) = {float(j43):.3f} < 0")


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
    assert _turan_const_conv(4, m, Fraction(16), al, be) >= 0  # genuine sign change in mu
    for mm in range(2, 9):                                    # the cubic case holds here
        assert _turan_const_conv(3, mm, mu, al, be) >= 0
    print(f"PASS: r=4 counterexample f_n=1, m=3, mu=17, a=b=1: [x^3] = {float(c_conv):.3e} < 0 "
          f"(r=3 stays >= 0)")


def main() -> None:
    check_control_quantity()
    check_log_concavity_role()
    check_general_r_kernel()
    check_lifted_array_obstruction()
    check_kernel_sign_contrast()
    check_r4_counterexample()
    print("ALL PASS: verify_remarks")


if __name__ == "__main__":
    main()
