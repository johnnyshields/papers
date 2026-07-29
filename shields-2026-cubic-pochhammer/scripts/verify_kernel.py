#!/usr/bin/env python3
r"""Paper section 4 (The cubic residue kernel).

The heart of the note.  With n = 3m-2 and t = p/(1-p), the constant-weight
kernel derivative reduces to a polynomial J_m(t) whose positivity on (0,1) is
certified by nonnegative Bernstein coefficients; monotone weights (eq. (4.1),
which the log-concave products w_k = f_k f_{m-k} of eq. (2.1) satisfy) are then
inserted through a one-sign-change pairing.

Section 4.1 (constant weight, Lemma 4.2):
  * the t-substitution of G_m, and the derivative identity eq. (4.2) with J_m,
    eq. (4.3), and its nu = 3k-1 form;
  * the projective transform eq. (4.4), its expansion eq. (4.5), the coefficient
    formula eq. (4.6) with S_{n,j}, eq. (4.7);
  * the two elementary binomial identities behind eq. (4.6);
  * the root-of-unity counts R_a(j) and the two residue-class moments, the
    R-expansion eq. (4.9), and the six-case closed form eq. (4.8);
  * the exponential bounds eq. (4.10)-(4.11), their increments, that each fails
    one step below its stated range and both are ATTAINED at m=3, and
    n+1 = 3m-1 = 2 or 5 (mod 6), shown load-bearing;
  * nonnegativity of every S_{n,j}, the positive xi^2 coefficient
    (3 S_{n,2} = 9 delta), the Bernstein reconstruction of J_m, and J_m(t) > 0
    with G_m strictly increasing.

Section 4.2 (monotone weights, Lemma 4.3, Theorem 4.1):
  * the weighted derivative eq. (4.12)-(4.13), the paired blocks eq. (4.14), the
    even-m center block eq. (4.15), with its m/2 derived, and
    sum_k B_{m,k} = J_m;
  * sign(B_{m,k}) = sign(H_{m,k}), the hyperbolic form eq. (4.16), monotonicity
    of d -> d tanh(3dz/2), the positive final block, the single sign change, and
    the proof's implication B_{m,k} <= 0 => B_{m,k-1} < 0;
  * Theorem 4.1: G_{m,w} nondecreasing on [0,1/2] under the ordering eq. (4.1),
    strictly if the weights are not all zero (and exactly zero if they are), with
    eq. (4.1)'s ordering shown load-bearing.  The proof applies Lemma 3.1; the
    three-term split checked here is Lemma 3.1's own pivot, reproduced at the
    section-4 level on the actual blocks.

NOTE ON SYMBOLS.  The SymPy symbol `x` in this file is the paper's projective
variable xi of eqs. (4.4)-(4.6); the symbol used for the paper's z in eq. (4.16)
is also spelled x in the mpmath helpers.  The paper's delta = n+1-j is spelled
`d` in the integer helpers.  These are transliterations, not different objects.

Symbolic identities use SymPy; signs and the sign-change pattern use exact
Fractions; monotonicity and positivity ranges use mpmath.
"""
from __future__ import annotations

import itertools
import random
from fractions import Fraction
from math import comb

import mpmath as mp
import sympy as sp

mp.mp.dps = 40

t, x, p = sp.symbols("t x p")


# ===========================================================================
# Constant-weight building blocks (symbolic)
# ===========================================================================
def Gm_p(m):
    """G_m(p) = sum_{k=1}^{m-1} C(3m-2,3k-1) p^{3k}(1-p)^{3(m-k)}."""
    n = 3 * m - 2
    return sum(comb(n, 3 * r - 1) * p ** (3 * r) * (1 - p) ** (3 * (m - r))
               for r in range(1, m))


def Jr(m):
    """J_m(t), eq. (4.3)."""
    n = 3 * m - 2
    return sum(comb(n, 3 * r - 1) * t ** (3 * r - 1) * (r - (m - r) * t)
               for r in range(1, m))


def Jk(m):
    """J_m(t) in the nu = 3k-1 form under eq. (4.3)."""
    n = 3 * m - 2
    return sp.Rational(1, 3) * sum(
        comb(n, k) * t ** k * ((k + 1) - (n - k + 1) * t)
        for k in range(0, n + 1) if k % 3 == 2
    )


def Psum(m):
    """P_m(x), eq. (4.5)."""
    n = 3 * m - 2
    return sp.Rational(1, 3) * sum(
        comb(n, k) * x ** k * (1 + x) ** (n - k) * ((k + 1) + (2 * k - n) * x)
        for k in range(0, n + 1) if k % 3 == 2
    )


def check_t_substitution_and_derivative() -> None:
    for m in range(2, 6):
        n = 3 * m - 2
        # G_m(t/(1+t)) = (1+t)^{-3m} sum_k C(n,3k-1) t^{3k}
        lhs = sp.simplify(Gm_p(m).subs(p, t / (1 + t)))
        rhs = sp.simplify(sum(comb(n, 3 * r - 1) * t ** (3 * r) for r in range(1, m))
                          / (1 + t) ** (3 * m))
        assert sp.simplify(lhs - rhs) == 0, m
        # eq. (4.2): d/dt G_m(t/(1+t)) = 3 J_m(t)/(1+t)^{3m+1}
        dGdt = sp.diff(rhs, t)
        assert sp.simplify(dGdt - 3 * Jr(m) / (1 + t) ** (3 * m + 1)) == 0, m
        # nu = 3k-1 rewrite of J_m
        assert sp.expand(Jr(m) - Jk(m)) == 0, m
    # the substitution's range claim: t = p/(1-p) carries [0,1/2] onto [0,1]
    # bijectively and increasingly, which is what lets monotonicity in t stand in
    # for monotonicity in p
    for i in range(0, 501):
        pv = Fraction(i, 1000)                       # p in [0, 1/2]
        tv = pv / (1 - pv)
        assert 0 <= tv <= 1, (pv, tv)
        assert tv == 1 if pv == Fraction(1, 2) else tv < 1
    for i in range(0, 1001):
        tv = Fraction(i, 1000)                       # t in [0, 1]
        pv = tv / (1 + tv)
        assert 0 <= pv <= Fraction(1, 2), (tv, pv)
    prev = None
    for i in range(0, 501):
        pv = Fraction(i, 1000)
        tv = pv / (1 - pv)
        if prev is not None:
            assert tv > prev                         # strictly increasing
        prev = tv
    # and p > 1/2 leaves the range, so the restriction is real
    assert Fraction(3, 5) / (1 - Fraction(3, 5)) > 1
    print("PASS: G_m t-form, derivative eq. (4.2)-(4.3), nu=3k-1 rewrite, and "
          "0<=p<=1/2 <=> 0<=t<=1 (increasing bijection)")


def check_projective_transform() -> None:
    for m in range(2, 6):
        n = 3 * m - 2
        # eq. (4.4)=(4.5): P_m(x) = (1+x)^{n+1} J_m(x/(1+x))
        lhs = sp.expand(sp.cancel((1 + x) ** (n + 1) * Jr(m).subs(t, x / (1 + x))))
        assert sp.expand(lhs - Psum(m)) == 0, m
    print("PASS: projective transform P_m = (1+x)^{n+1} J_m(x/(1+x)) (eqs. 4.4-4.5)")


# ===========================================================================
# Binomial identities behind eq. (4.6); S_{n,j}, moments, R-expansion, table
# ===========================================================================
def check_binomial_identities(n_max: int = 40) -> None:
    for n in range(n_max + 1):
        for j in range(n + 2):
            for k in range(j + 1):
                assert comb(n, k) * comb2(n - k, j - k) == comb(n, j) * comb(j, k)
                lhs = comb(n, k) * comb2(n - k, j - k - 1)
                num = comb(n + 1, j) * comb(j, k) * (j - k)
                assert num % (n + 1) == 0 and lhs == num // (n + 1)
    print("PASS: the two binomial identities behind eq. (4.6)")


def comb2(a: int, b: int) -> int:
    return comb(a, b) if 0 <= b <= a else 0


def S_sum(n: int, j: int) -> int:
    """S_{n,j}, eq. (4.7)."""
    return sum(comb(j, k) * (n - k + 1) * (2 * k + 1 - j)
               for k in range(j + 1) if k % 3 == 2)


def R(a: int, j: int) -> int:
    return sum(comb(j, k) for k in range(j + 1) if k % 3 == a % 3)


def _zw_mul(u, v):
    """Multiply in Z[omega], omega a primitive cube root: omega^2 = -1-omega.

    Elements are pairs (a, b) meaning a + b*omega, so the arithmetic is exact
    integer arithmetic and the root-of-unity filter needs no complex numerics.
    """
    a, b = u
    c, d = v
    return (a * c - b * d, a * d + b * c - b * d)


def _zw_pow(u, e):
    out, base = (1, 0), u
    while e:
        if e & 1:
            out = _zw_mul(out, base)
        base = _zw_mul(base, base)
        e >>= 1
    return out


def _zw_filter_sum(a: int, j: int):
    r"""sum_{l=0}^{2} omega^{-a l} (1 + omega^l)^j, exactly in Z[omega].

    This is the middle expression of the paper's filter
    R_a(j) = (1/3) sum_l omega^{-a l} (1 + omega^l)^j.
    """
    powers = [(1, 0), (0, 1), (-1, -1)]              # omega^0, omega^1, omega^2
    total = (0, 0)
    for l in range(3):
        one_plus = (1 + powers[l][0], powers[l][1])
        term = _zw_mul(powers[(-a * l) % 3], _zw_pow(one_plus, j))
        total = (total[0] + term[0], total[1] + term[1])
    return total


def check_R_and_moments(j_max: int = 60) -> None:
    twocos = [2, 1, -1, -2, -1, 1]                 # 2 cos((j-2a) pi/3), by (j-2a) mod 6
    # the tabulated values ARE the trigonometry the paper writes, not a separate
    # claim: 2 cos(k pi/3) = 2, 1, -1, -2, -1, 1 for k = 0..5
    for k in range(6):
        assert sp.simplify(2 * sp.cos(sp.pi * k / 3) - twocos[k]) == 0, k
    for j in range(j_max + 1):
        for a in range(3):
            assert 3 * R(a, j) == 2 ** j + twocos[(j - 2 * a) % 6], (a, j)
            # the paper's trigonometric closed form, as trigonometry
            assert sp.simplify(
                3 * R(a, j) - (2 ** j + 2 * sp.cos(sp.pi * (j - 2 * a) / 3))) == 0, (a, j)
            # the middle expression of the root-of-unity filter itself, in exact
            # Z[omega] arithmetic (basis {1, omega}, omega^2 = -1-omega)
            total = _zw_filter_sum(a, j)
            assert total == (3 * R(a, j), 0), (a, j, total)
        # residue-class moments used in eq. (4.9)
        m1 = sum(k * comb(j, k) for k in range(j + 1) if k % 3 == 2)
        assert m1 == j * R(1, j - 1)
        m2 = sum(k * k * comb(j, k) for k in range(j + 1) if k % 3 == 2)
        assert m2 == j * (j - 1) * R(0, j - 2) + j * R(1, j - 1)
    print("PASS: R_a(j) closed form (table, trigonometry, and the omega-filter) "
          "and the two residue-class moments")


def check_R_pascal_route(j_max: int = 60) -> None:
    """The C-free route: Pascal's rule plus seeds determines every R_a(j).

    The paper offers this so the six-case table needs no appeal to C:
    R_a(j+1) = R_a(j) + R_{a-1}(j) (subscripts mod 3), with R_0(0) = 1 and
    R_1(0) = R_2(0) = 0.  Recomputed here by pure integer recursion and compared
    against the direct residue-class sums.
    """
    cur = [1, 0, 0]                                 # R_0(0), R_1(0), R_2(0)
    assert cur == [R(0, 0), R(1, 0), R(2, 0)]
    for j in range(j_max):
        nxt = [cur[a] + cur[(a - 1) % 3] for a in range(3)]
        for a in range(3):
            assert nxt[a] == R(a, j + 1), (a, j + 1, nxt[a], R(a, j + 1))
        cur = nxt
    print(f"PASS: the C-free Pascal recurrence R_a(j+1)=R_a(j)+R_{{a-1}}(j) with "
          f"R_0(0)=1, R_1(0)=R_2(0)=0 reproduces every R_a(j), j<={j_max}")


def S_from_R(n: int, j: int) -> int:
    """eq. (4.9), valid for j >= 2."""
    d = n + 1 - j
    return (d * (2 * j * R(1, j - 1) + (1 - j) * R(2, j))
            + j * (j - 1) * (-2 * R(0, j - 2) + 3 * R(1, j - 1) - R(2, j)))


def three_S_table(n: int, j: int) -> int:
    """eq. (4.8)."""
    d = n + 1 - j
    res = j % 6
    if res == 0:
        return d * (2 ** j - 3 * j - 1) - 3 * j * (j - 1)
    if res == 1:
        return d * (2 ** j - 2) - 3 * j * (j - 1)
    if res == 2:
        return d * (2 ** j + 3 * j - 1)
    if res == 3:
        return d * (2 ** j + 3 * j + 1) + 3 * j * (j - 1)
    if res == 4:
        return d * (2 ** j + 2) + 3 * j * (j - 1)
    return d * (2 ** j - 3 * j + 1)


def poly_coeff_projective(m: int) -> list:
    """[x^j] P_m(x) from a direct SymPy polynomial expansion of eq. (4.5)."""
    poly = sp.Poly(sp.expand(Psum(m)), x)
    n = 3 * m - 2
    return [int(poly.coeff_monomial(x ** j)) for j in range(n + 2)]


def check_congruence_is_load_bearing(n_max: int = 199) -> None:
    """n+1 = 3m-1 = 2 or 5 (mod 6) is what makes S_{n,j} >= 0 -- not decoration.

    The paper uses the congruence exactly once, to get delta >= 2 in the
    j = 0 (mod 6) branch of eq. (4.8), where 3S_{n,j} = delta(2^j-3j-1)-3j(j-1)
    would otherwise go negative.  Dropping the restriction on n and sweeping all
    n < n_max in exact integers finds genuine negative values, and every one of
    them sits at n+1 = 0 or 1 (mod 6) -- precisely the residues n = 3m-2 cannot
    take.  So the keystone positivity certificate is false for general n and the
    congruence is the whole reason it holds here.
    """
    negatives = [(n, j, S_sum(n, j))
                 for n in range(2, n_max + 1)
                 for j in range(n + 2)
                 if S_sum(n, j) < 0]
    assert negatives, "S_{n,j} should go negative once the congruence is dropped"
    # the witnesses the paper's restriction excludes
    assert S_sum(5, 6) == -30, S_sum(5, 6)
    assert S_sum(6, 6) == -15, S_sum(6, 6)
    # every failure is at an excluded residue, and none at an admissible one
    assert sorted({(n + 1) % 6 for n, _, _ in negatives}) == [0, 1]
    assert all((n + 1) % 6 not in (2, 5) for n, _, _ in negatives)
    # delta >= 2 is what rescues the j = 0 (mod 6) branch, and j = 6 is the ONLY
    # place it is needed: with delta = 1 that branch reads 2^j-3j-1-3j(j-1),
    # negative at j=6 (= -45) and positive from j=12 on, since the exponential
    # then dominates.  So the congruence is load-bearing at exactly one j.
    assert (2 ** 6 - 3 * 6 - 1) - 3 * 6 * 5 == -45
    assert all((2 ** j - 3 * j - 1) - 3 * j * (j - 1) > 0
               for j in range(12, 200, 6))
    # with the paper's delta >= 2 the same branch is nonnegative at j = 6
    assert 2 * (2 ** 6 - 3 * 6 - 1) - 3 * 6 * 5 == 0
    # and no n of the paper's own form ever fails
    for m in range(2, (n_max + 2) // 3 + 1):
        n = 3 * m - 2
        if n > n_max:
            break
        assert all(S_sum(n, j) >= 0 for j in range(n + 2)), m
    print(f"PASS: the congruence n+1 = 2,5 (mod 6) is load-bearing -- "
          f"{len(negatives)} negative S_(n,j) once it is dropped (n<={n_max}), "
          f"first S_(5,6)={S_sum(5, 6)}, S_(6,6)={S_sum(6, 6)}, all at n+1 = 0,1 (mod 6)")


def check_S_and_coeff(max_m: int = 60) -> None:
    for m in range(2, max_m + 1):
        n = 3 * m - 2
        # n+1 = 3m-1 = 2 or 5 (mod 6)
        assert (n + 1) % 6 in (2, 5)
        symbolic = poly_coeff_projective(m) if m <= 6 else None
        for j in range(n + 2):
            s = S_sum(n, j)
            d = n + 1 - j                            # delta
            if j >= 2:
                assert s == S_from_R(n, j), (m, j)
            assert 3 * s == three_S_table(n, j), (m, j)
            assert s >= 0, (m, j, s)                 # nonnegativity of S_{n,j}
            # the two branch bounds the congruence buys, which the case
            # inspection in the proof of Lemma 4.2 consumes
            if j % 6 == 1:
                assert d >= 1, (m, j, d)             # j = 1 (mod 6) => delta >= 1
            if j % 6 == 0 and j > 0:
                assert d >= 2, (m, j, d)             # j = 0 (mod 6), j>0 => delta >= 2
            # eq. (4.6): [x^j] P_m = C(n+1,j)/(3(n+1)) S_{n,j}
            num = comb(n + 1, j) * s
            den = 3 * (n + 1)
            assert num % den == 0, (m, j)
            coeff = num // den
            # first equality of eq. (4.6) (direct residue-class sum)
            direct = sum(
                comb(n, k) * ((k + 1) * comb2(n - k, j - k) + (2 * k - n) * comb2(n - k, j - k - 1))
                for k in range(j + 1) if k % 3 == 2
            )
            assert direct % 3 == 0 and direct // 3 == coeff, (m, j)
            if symbolic is not None:
                assert symbolic[j] == coeff, (m, j)    # independent SymPy route
        # positive xi^2 coefficient: 3 S_{n,2} = 9 delta, delta = n-1 > 0
        assert three_S_table(n, 2) == 9 * (n - 1) and S_sum(n, 2) > 0
        assert comb(n + 1, 2) * S_sum(n, 2) // (3 * (n + 1)) > 0
    print(f"PASS: S_{{n,j}} formulas, nonnegativity, eq.(4.6), delta bounds, "
          f"xi^2 coefficient > 0 (2<=m<={max_m})")


def check_exponential_bounds(j_max: int = 200) -> None:
    # eq. (4.10): 2^j - 2 >= 3j(j-1) for j >= 7, equality at j=7
    assert 2 ** 7 - 2 == 3 * 7 * 6
    for j in range(7, j_max):
        assert 2 ** j - 2 >= 3 * j * (j - 1)
        assert 2 ** j - 6 * j > 0                    # increment of (4.10)
    # eq. (4.11): 2(2^j - 3j - 1) >= 3j(j-1) for j >= 6, equality at j=6
    assert 2 * (2 ** 6 - 3 * 6 - 1) == 3 * 6 * 5
    for j in range(6, j_max):
        assert 2 * (2 ** j - 3 * j - 1) >= 3 * j * (j - 1)
        assert 2 ** (j + 1) - 6 * j - 6 > 0          # increment of (4.11)
    # the paper states both increments positive "for j >= 6"; (4.10)'s loop above
    # starts at its own threshold j=7, so pin j=6 for the increment claim too
    assert 2 ** 6 - 6 * 6 > 0
    # j = 5 (mod 6): 2^j - 3j + 1 > 0 for j >= 5, increment 2^j - 3 > 0
    for j in range(5, j_max):
        assert 2 ** j - 3 * j + 1 > 0 and 2 ** j - 3 > 0
    # both thresholds are load-bearing: each bound FAILS one step below its range
    assert not (2 ** 6 - 2 >= 3 * 6 * 5), "eq. (4.10) should fail at j=6"
    assert not (2 * (2 ** 5 - 3 * 5 - 1) >= 3 * 5 * 4), "eq. (4.11) should fail at j=5"
    print("PASS: exponential bounds eq. (4.10)-(4.11), their increments, and the "
          "failure of each bound one step below its stated range")


def check_exponential_bounds_are_attained() -> None:
    """Neither exponential bound can be weakened: both are attained at m = 3.

    The equalities at j = 7 in eq. (4.10) and j = 6 in eq. (4.11) are not
    abstract -- at m = 3 (so n = 7) they are realized by the paper's own family,
    where S_{7,7} = 0 with delta = 1 (the j = 1 (mod 6) branch) and S_{7,6} = 0
    with delta = 2 (the j = 0 (mod 6) branch).  Weakening either bound by any
    positive amount would therefore make the certificate false.
    """
    assert 3 * 3 - 2 == 7
    assert S_sum(7, 7) == 0 and S_sum(7, 6) == 0, (S_sum(7, 7), S_sum(7, 6))
    assert (7 + 1 - 7) == 1 and (7 + 1 - 6) == 2      # the two delta values
    assert three_S_table(7, 7) == 0 and three_S_table(7, 6) == 0
    print("PASS: eqs. (4.10)-(4.11) are ATTAINED at m=3 -- S_(7,7)=S_(7,6)=0 -- "
          "so neither bound can be weakened")


def check_bernstein_reconstruction() -> None:
    """J_m(t) = sum_j b_j C(n+1,j) t^j (1-t)^{n+1-j}, b_j = S_{n,j}/(3(n+1))."""
    for m in range(2, 6):
        n = 3 * m - 2
        recon = sum(
            sp.Rational(S_sum(n, j), 3 * (n + 1)) * comb(n + 1, j)
            * t ** j * (1 - t) ** (n + 1 - j)
            for j in range(n + 2)
        )
        assert sp.expand(recon - Jr(m)) == 0, m
    print("PASS: Bernstein reconstruction of J_m with b_j = S_{n,j}/(3(n+1)) >= 0")


def check_Jm_positive_and_Gm_increasing() -> None:
    for m in range(2, 12):
        n = 3 * m - 2
        Jfun = sp.lambdify(t, Jr(m), "mpmath")
        for tt in [mp.mpf(i) / 20 for i in range(1, 20)]:
            assert Jfun(tt) > 0, (m, tt)
        Gfun = sp.lambdify(p, Gm_p(m), "mpmath")
        grid = [mp.mpf(i) / 200 for i in range(0, 101)]      # [0, 1/2]
        vals = [Gfun(pp) for pp in grid]
        for a, b in zip(vals, vals[1:]):
            assert b > a, (m,)                                # strictly increasing
    print("PASS: J_m(t) > 0 on (0,1) and G_m strictly increasing on [0,1/2]")


# ===========================================================================
# 4.2  Monotone weights
# ===========================================================================
def check_weighted_derivative() -> None:
    for m in range(2, 6):
        n = 3 * m - 2
        wsyms = sp.symbols(f"w1:{m}")
        w = {r: wsyms[r - 1] for r in range(1, m)}
        # Derive the t-form of G_{m,w} from eq. (2.5) by substituting p = t/(1+t),
        # rather than writing it down: the unweighted case does this at
        # check_t_substitution_and_derivative, and assuming it here would leave
        # the substitution step of eq. (4.12) untested.
        Gw_p = sum(w[r] * comb(n, 3 * r - 1) * p ** (3 * r) * (1 - p) ** (3 * (m - r))
                   for r in range(1, m))
        Gw_t = sum(w[r] * comb(n, 3 * r - 1) * t ** (3 * r) for r in range(1, m)) / (1 + t) ** (3 * m)
        assert sp.simplify(Gw_p.subs(p, t / (1 + t)) - Gw_t) == 0, ("substitution", m)
        Jw = sum(w[r] * comb(n, 3 * r - 1) * t ** (3 * r - 1) * (r - (m - r) * t) for r in range(1, m))
        assert sp.simplify(sp.diff(Gw_t, t) - 3 * Jw / (1 + t) ** (3 * m + 1)) == 0, m
    print("PASS: weighted derivative eq. (4.12)-(4.13), including the "
          "t-substitution of eq. (2.5)")


def check_block_domain_guard() -> None:
    """B_{m,k} is undefined for 2k > m, and for k = m/2 at odd m; the guard fires.

    eq. (4.14) covers 1 <= k < m/2 and eq. (4.15) only k = m/2 at even m.  Outside
    that range there is no formula to return -- B_block(7, 4) would otherwise
    evaluate the centre-block expression at an index it does not describe -- so the
    precondition is asserted, and exercised here on both sides of the boundary.
    """
    bad = [(7, 4), (7, 5), (5, 3), (4, 3), (6, 4)]     # 2k > m
    for m, r in bad:
        assert 2 * r > m
        for fn in (B_block, lambda mm, rr: B_eval(mm, rr, Fraction(1, 3))):
            try:
                fn(m, r)
            except AssertionError:
                pass
            else:
                raise AssertionError(f"guard did not fire for m={m}, k={r}")
    # k = m/2 at ODD m is also out of domain (there is no integer centre block)
    for m, r in [(5, 2), (7, 3)]:
        assert 2 * r < m                                # in domain, must NOT raise
        B_block(m, r)
        B_eval(m, r, Fraction(1, 3))
    print(f"PASS: the B_{{m,k}} domain guard fires on all {len(bad)} out-of-domain "
          f"indices and passes in-domain ones")


def check_kernel_scope_edges() -> None:
    """The two scope edges of section 4 that the sweeps never cross.

    G_{m,w} is asserted nondecreasing on [0,1/2] only; by the p <-> 1-p symmetry
    of eq. (2.5) it DECREASES on [1/2,1], so the restriction is real and not an
    artefact of where the grids happen to stop.  And m >= 2 is needed for the
    strict half: at m = 1 the sum of eq. (4.13) is empty, so J_1 == 0 and no
    strictness claim can hold.
    """
    for m in (4, 5, 7):
        n = 3 * m - 2
        wmap = {r: 1 for r in range(1, m)}
        G = sum(wmap[r] * comb(n, 3 * r - 1) * p ** (3 * r) * (1 - p) ** (3 * (m - r))
                for r in range(1, m))
        Gf = sp.lambdify(p, sp.expand(G), "mpmath")
        left = [Gf(mp.mpf(i) / 200) for i in range(0, 101)]        # [0, 1/2]
        right = [Gf(mp.mpf(i) / 200) for i in range(100, 201)]     # [1/2, 1]
        for a, b in zip(left, left[1:]):
            assert b > a, ("not increasing on [0,1/2]", m)
        for a, b in zip(right, right[1:]):
            assert b < a, ("not DEcreasing on [1/2,1] -- scope claim is empty", m)
        assert abs(left[-1] - right[0]) < mp.mpf("1e-30")          # they meet at 1/2
    # m = 1: eq. (4.13) is an empty sum
    assert sum(comb(1, 3 * r - 1) * t ** (3 * r - 1) * (1 - r) for r in range(1, 1)) == 0
    print("PASS: scope edges -- G_{m,w} DEcreases on [1/2,1] (so [0,1/2] is a real "
          "restriction), and J_1 == 0 so m >= 2 is needed for strictness")


def B_block(m: int, r: int):
    """B_{m,k}(t), eq. (4.14), and the even-m center block eq. (4.15).

    Same domain guard as B_eval: eq. (4.14) covers 1 <= k < m/2 and eq. (4.15)
    only k = m/2 at even m.
    """
    assert 1 <= r and 2 * r <= m, ("B_{m,k} undefined for 2k > m", m, r)
    assert 2 * r < m or m % 2 == 0, ("k = m/2 requires even m", m, r)
    n = 3 * m - 2
    if 2 * r < m:
        return comb(n, 3 * r - 1) * (t ** (3 * r - 1) * (r - (m - r) * t)
                                     + t ** (3 * (m - r) - 1) * ((m - r) - r * t))
    return comb(n, 3 * r - 1) * sp.Rational(m, 2) * t ** (3 * m // 2 - 1) * (1 - t)  # r = m/2


def check_block_decomposition() -> None:
    for m in range(2, 8):
        n = 3 * m - 2
        base = sp.symbols(f"a0:{m // 2 + 1}")
        w = {r: base[min(r, m - r)] for r in range(1, m)}          # symmetric
        Jw = sum(w[r] * comb(n, 3 * r - 1) * t ** (3 * r - 1) * (r - (m - r) * t)
                 for r in range(1, m))
        paired = sum(w[r] * B_block(m, r) for r in range(1, m // 2 + 1))
        assert sp.expand(Jw - paired) == 0, m
        if m % 2 == 0:                                              # eq. (4.15)
            center = comb(n, 3 * m // 2 - 1) * sp.Rational(m, 2) * t ** (3 * m // 2 - 1) * (1 - t)
            # Derive eq. (4.15) rather than restate it: at k = m/2 the summand of
            # eq. (4.13) appears ONCE (pairing k with m-k would double-count it),
            # so the center block carries m/2.  The comparison is against the
            # k = m/2 term extracted straight from eq. (4.13), so the coefficient is
            # derived rather than restated.
            kc = m // 2
            center_from_413 = sp.expand(
                comb(n, 3 * kc - 1) * t ** (3 * kc - 1) * (kc - (m - kc) * t))
            assert sp.expand(center_from_413 - center) == 0, ("eq. (4.15) coefficient", m)
            # and the naive double-count (m in place of m/2) is genuinely wrong
            naive = sp.expand(comb(n, 3 * kc - 1) * m * t ** (3 * kc - 1) * (1 - t))
            assert sp.expand(naive - center) != 0, m
            assert sp.expand(B_block(m, m // 2) - center) == 0, m
            assert center.subs(t, sp.Rational(1, 3)) > 0, m         # positivity
        # constant weights: sum_k B_{m,k} = J_m
        allones = sum(B_block(m, r) for r in range(1, m // 2 + 1))
        assert sp.expand(allones - Jr(m)) == 0, m
    print("PASS: J_{m,w} = sum_k w_k B_{m,k}, center block, and sum_k B_{m,k} = J_m")


def check_block_sign_form() -> None:
    """sign(B_{m,k}) = sign(H_{m,k}); the hyperbolic identity eq. (4.16)."""
    for m in range(2, 8):
        n = 3 * m - 2
        for r in range(1, (m + 1) // 2):            # r < m/2
            d = m - 2 * r
            H = r - (m - r) * t + t ** (3 * d) * ((m - r) - r * t)
            assert sp.expand(B_block(m, r) - comb(n, 3 * r - 1) * t ** (3 * r - 1) * H) == 0
            # algebraic middle form of eq. (4.16)
            mid = sp.Rational(1, 2) * (m * (1 - t) * (1 + t ** (3 * d)) - d * (1 + t) * (1 - t ** (3 * d)))
            assert sp.expand(H - mid) == 0, (m, r)
    # tanh form of eq. (4.16), checked numerically
    for m, r in [(5, 1), (7, 2), (9, 1), (11, 3)]:
        d = m - 2 * r
        for xv in [mp.mpf("0.2"), mp.mpf("1"), mp.mpf("3")]:
            tv = mp.e ** (-xv)
            H = r - (m - r) * tv + tv ** (3 * d) * ((m - r) - r * tv)
            hyp = (mp.mpf(1) / 2 * (1 + tv) * (1 + tv ** (3 * d))
                   * (m * mp.tanh(xv / 2) - d * mp.tanh(3 * d * xv / 2)))
            assert abs(H - hyp) < mp.mpf("1e-30"), (m, r, xv)
    print("PASS: sign(B_{m,k})=sign(H_{m,k}) and hyperbolic form eq. (4.16)")


def check_block_monotone_ingredients() -> None:
    # d -> d tanh(3 d x/2) strictly increasing in d > 0
    for xv in [mp.mpf("0.1"), mp.mpf("1"), mp.mpf("5")]:
        vals = [d * mp.tanh(3 * d * xv / 2) for d in [mp.mpf(i) / 5 for i in range(1, 80)]]
        for aa, bb in zip(vals, vals[1:]):
            assert bb > aa
    # odd-m final block: m tanh(x/2) - tanh(3x/2) > 0 for m >= 3; tanh(3y) < 3 tanh y
    for xv in [mp.mpf(i) / 10 for i in range(1, 120)]:
        assert mp.tanh(3 * xv) < 3 * mp.tanh(xv)
        assert 3 * mp.tanh(xv / 2) - mp.tanh(3 * xv / 2) > 0
    print("PASS: d tanh(3dz/2) increasing; odd-m final block positive")


def B_eval(m: int, r: int, tv: Fraction) -> Fraction:
    """B_{m,k}(t) in exact rational arithmetic (eqs. 4.14-4.15).

    eq. (4.14) is defined for 1 <= k < m/2 and eq. (4.15) only at k = m/2 for
    EVEN m, so 2r > m has no definition to return; the guard keeps the centre-block
    formula from being evaluated at an index it does not describe.
    """
    assert 1 <= r and 2 * r <= m, ("B_{m,k} undefined for 2k > m", m, r)
    assert 2 * r < m or m % 2 == 0, ("k = m/2 requires even m", m, r)
    n = 3 * m - 2
    c = comb(n, 3 * r - 1)
    if 2 * r < m:
        return c * (tv ** (3 * r - 1) * (r - (m - r) * tv)
                    + tv ** (3 * (m - r) - 1) * ((m - r) - r * tv))
    return c * Fraction(m, 2) * tv ** (3 * m // 2 - 1) * (1 - tv)      # r = m/2


def check_single_sign_change(trials: int = 6000, seed: int = 20260721) -> None:
    """Exact-sign scan: B_{m,1..floor(m/2)}(t) has at most one sign change, neg->pos."""
    rng = random.Random(seed)
    for _ in range(trials):
        m = rng.randint(2, 24)
        tv = Fraction(rng.randint(1, 999), 1000)
        signs = []
        for r in range(1, m // 2 + 1):
            val = B_eval(m, r, tv)
            signs.append(0 if val == 0 else (1 if val > 0 else -1))
        # the last block is strictly positive
        assert signs[-1] == 1, (m, tv)
        nz = [s for s in signs if s != 0]
        changes = sum(1 for a, b in zip(nz, nz[1:]) if a != b)
        assert changes <= 1, (m, tv, signs)
        if changes == 1:
            assert nz[0] == -1 and nz[-1] == 1, (m, tv, signs)   # neg -> pos
        # the proof's own step, one strength above the sign pattern it yields:
        # B_{m,k} <= 0  =>  B_{m,k-1} < 0  for 2 <= k < m/2, because
        # d -> d tanh(3dz/2) is strictly increasing and k-1 raises d by 2
        blocks = [B_eval(m, r, tv) for r in range(1, m // 2 + 1)]
        for k in range(2, m // 2 + 1):
            if 2 * k < m and blocks[k - 1] <= 0:
                assert blocks[k - 2] < 0, ("B_k<=0 => B_{k-1}<0 fails", m, tv, k)
    print("PASS: paired blocks have at most one sign change, neg->pos, and "
          "B_{m,k}<=0 => B_{m,k-1}<0 (Lemma 4.3)")


def check_theorem_kernel(trials: int = 2000, seed: int = 20260722) -> None:
    """Theorem 4.1: J_{m,w}(t) >= 0 (>0 if weights not all zero); G_{m,w} increasing."""
    rng = random.Random(seed)
    for _ in range(trials):
        m = rng.randint(2, 16)
        L = m // 2
        # nondecreasing nonnegative symmetric weights w_1<=...<=w_L
        ws, cur = [], Fraction(0)
        allzero = rng.random() < 0.15
        for _k in range(L):
            cur += Fraction(0) if allzero else Fraction(rng.randint(0, 5))
            ws.append(cur)
        tv = Fraction(rng.randint(1, 999), 1000)
        blocks = [B_eval(m, r, tv) for r in range(1, L + 1)]
        Jw = sum(ws[r - 1] * blocks[r - 1] for r in range(1, L + 1))
        assert Jw >= 0, (m, tv)
        if any(x != 0 for x in ws):
            assert Jw > 0, (m, tv)
        else:
            # eq. (4.1) admits w == 0, and then the derivative vanishes identically:
            # NONNEGATIVITY holds but positivity does not.  This is why Theorem 4.1
            # carries "if the weights are not all zero" and why the summarizing
            # sentence in section 4.2 must say nonnegativity, not positivity.
            assert Jw == 0, (m, tv, Jw)
        # three-term decomposition around the last negative block
        neg = [i for i, b in enumerate(blocks) if b < 0]
        if neg:
            q = neg[-1]
            c = ws[q]
            term1 = c * sum(blocks)
            term2 = sum((ws[i] - c) * blocks[i] for i in range(q + 1))
            term3 = sum((ws[i] - c) * blocks[i] for i in range(q + 1, L))
            assert term1 + term2 + term3 == Jw
            assert term1 >= 0 and term2 >= 0 and term3 >= 0
    # G_{m,w} nondecreasing on [0,1/2] for a couple of explicit weightings
    for m, wmap in [(5, {1: 1, 2: 2, 3: 2, 4: 1}), (6, {1: 1, 2: 3, 3: 4, 4: 3, 5: 1})]:
        n = 3 * m - 2
        Gexpr = sum(wmap[r] * comb(n, 3 * r - 1) * p ** (3 * r) * (1 - p) ** (3 * (m - r))
                    for r in range(1, m))
        Gfun = sp.lambdify(p, Gexpr, "mpmath")
        vals = [Gfun(mp.mpf(i) / 200) for i in range(0, 101)]
        for a, b in zip(vals, vals[1:]):
            assert b > a, m
    print("PASS: Theorem 4.1 (J_{m,w}>=0, strict; G_{m,w} increasing on [0,1/2])")


def check_weight_monotonicity_is_load_bearing() -> None:
    """eq. (4.1) is load-bearing: DECREASING weights break Theorem 4.1.

    The hypothesis 0 <= w_1 <= ... <= w_{floor(m/2)} is what lets Lemma 3.1
    absorb the one-sign-change block pattern.  Reversing it -- weights that
    decrease toward the center, still nonnegative and still symmetric -- drives
    J_{m,w} negative, so the conclusion genuinely needs the ordering and not just
    nonnegativity of the weights.
    """
    found = []
    for m in (13, 15, 17):
        L = m // 2
        ws = [Fraction(L - k) for k in range(L)]       # DECREASING: L, L-1, ..., 1
        assert all(x >= 0 for x in ws) and ws[0] > ws[-1]
        for num in (930, 953, 970, 985):
            tv = Fraction(num, 1000)
            Jw = sum(ws[r - 1] * B_eval(m, r, tv) for r in range(1, L + 1))
            if Jw < 0:
                found.append((m, tv, Jw))
    assert found, "expected decreasing weights to break Theorem 4.1"
    # the same m and t with the paper's ordering restored stays nonnegative
    for m, tv, _ in found:
        L = m // 2
        ws_ok = [Fraction(k + 1) for k in range(L)]    # nondecreasing
        Jw_ok = sum(ws_ok[r - 1] * B_eval(m, r, tv) for r in range(1, L + 1))
        assert Jw_ok > 0, (m, tv, Jw_ok)
    m0, t0, j0 = found[0]
    print(f"PASS: eq. (4.1) is load-bearing -- decreasing weights give "
          f"J_{{m,w}} < 0 ({len(found)} witnesses, first m={m0}, t={t0}, "
          f"J={float(j0):.3e}), while the same (m,t) with nondecreasing weights is > 0")


def check_monotone_weights_need_not_be_log_concave() -> None:
    """Section 4.2 assumes eq. (4.1) only, which is STRICTLY weaker than
    log-concavity of the weights.

    The section title says "monotone weights", not "log-concave weights", and
    that distinction is real: eq. (4.1) asks for symmetry plus
    0 <= w_1 <= ... <= w_{floor(m/2)}, and a weight sequence can satisfy it while
    failing w_k^2 >= w_{k-1} w_{k+1}.  Theorem 4.1 still applies to those weights,
    so the hypothesis really is the weaker one.  Conversely, the weights the paper
    feeds in -- w_k = f_k f_{m-k} from a log-concave (f_n), eq. (2.1) -- always
    satisfy eq. (4.1), so the implication runs one way only.
    """
    def is_log_concave(seq: list) -> bool:
        nz = [i for i, v in enumerate(seq) if v > 0]
        if nz and nz != list(range(nz[0], nz[-1] + 1)):
            return False
        return all(seq[i] ** 2 >= seq[i - 1] * seq[i + 1]
                   for i in range(1, len(seq) - 1))

    witnesses = [(6, {1: 1, 2: 1, 3: 10, 4: 1, 5: 1}),
                 (7, {1: 1, 2: 2, 3: 50, 4: 50, 5: 2, 6: 1}),
                 (8, {1: 0, 2: 1, 3: 1, 4: 100, 5: 1, 6: 1, 7: 0})]
    for m, wmap in witnesses:
        L = m // 2
        full = [wmap[k] for k in range(1, m)]
        assert all(x >= 0 for x in full), (m, full)
        assert all(wmap[k] == wmap[m - k] for k in range(1, m)), (m, full)
        assert all(wmap[k] <= wmap[k + 1] for k in range(1, L)), (m, full)
        assert not is_log_concave(full), ("expected NOT log-concave", m, full)
        for num in range(1, 1000, 7):                  # Theorem 4.1 still holds
            tv = Fraction(num, 1000)
            Jw = sum(wmap[r] * B_eval(m, r, tv) for r in range(1, L + 1))
            assert Jw > 0, (m, tv, Jw)

    # the converse direction: log-concave (f_n) always yields eq. (4.1) weights
    checked = 0
    for m in range(3, 8):
        for combo in itertools.product([0, 1, 2, 4], repeat=m):
            f = [0] + list(combo[1:]) + [combo[0]]
            if not is_log_concave(f[:m + 1]):
                continue
            wmap = {k: f[k] * f[m - k] for k in range(1, m)}
            assert all(wmap[k] == wmap[m - k] for k in range(1, m)), (m, f)
            assert all(wmap[k] <= wmap[k + 1] for k in range(1, m // 2)), (m, f)
            checked += 1
    assert checked > 0
    print(f"PASS: eq. (4.1) is strictly weaker than log-concavity of the weights "
          f"-- {len(witnesses)} monotone non-log-concave witnesses (first m=6, "
          f"w=(1,1,10,1,1)) still satisfy Theorem 4.1, while all {checked} "
          f"log-concave-derived weight sets satisfy eq. (4.1)")


def main() -> None:
    check_t_substitution_and_derivative()
    check_projective_transform()
    check_binomial_identities()
    check_R_and_moments()
    check_R_pascal_route()
    check_congruence_is_load_bearing()
    check_S_and_coeff()
    check_exponential_bounds()
    check_exponential_bounds_are_attained()
    check_bernstein_reconstruction()
    check_Jm_positive_and_Gm_increasing()
    check_weighted_derivative()
    check_block_decomposition()
    check_block_sign_form()
    check_block_monotone_ingredients()
    check_single_sign_change()
    check_theorem_kernel()
    check_weight_monotonicity_is_load_bearing()
    check_monotone_weights_need_not_be_log_concave()
    check_block_domain_guard()
    check_kernel_scope_edges()
    print("ALL PASS: verify_kernel")


if __name__ == "__main__":
    main()
