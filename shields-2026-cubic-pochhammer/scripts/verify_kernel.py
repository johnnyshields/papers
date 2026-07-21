#!/usr/bin/env python3
r"""Paper section 4 (The cubic residue kernel).

The heart of the note.  With n = 3m-2 and t = p/(1-p), the constant-weight
kernel derivative reduces to a polynomial J_m(t) whose positivity on (0,1) is
certified by nonnegative Bernstein coefficients; log-concave weights are then
inserted through a one-sign-change pairing.

Section 4.1 (constant weight, Lemma 4.2):
  * the t-substitution of G_m, and the derivative identity eq. (4.2) with J_m,
    eq. (4.3), and its k = 3r-1 form;
  * the projective transform eq. (4.4), its expansion eq. (4.5), the coefficient
    formula eq. (4.6) with S_{n,j}, eq. (4.7);
  * the two elementary binomial identities behind eq. (4.6);
  * the root-of-unity counts R_a(j) and the two residue-class moments, the
    R-expansion eq. (4.9), and the six-case closed form eq. (4.8);
  * the exponential bounds eq. (4.10)-(4.11) and their increments, and
    n+1 = 3m-1 = 2 or 5 (mod 6);
  * nonnegativity of every S_{n,j}, the positive x^2 coefficient (3S=9d), the
    Bernstein reconstruction of J_m, and J_m(t) > 0 with G_m strictly increasing.

Section 4.2 (log-concave weights, Lemma 4.3, Theorem 4.1):
  * the weighted derivative eq. (4.12)-(4.13), the paired blocks eq. (4.14), the
    even-m center block eq. (4.15), and sum_r B_{m,r} = J_m;
  * sign(B_{m,r}) = sign(H_{m,r}), the hyperbolic form eq. (4.16), monotonicity
    of d -> d tanh(3dx/2), the positive final block, and the single sign change;
  * Theorem 4.1: G_{m,w} nondecreasing on [0,1/2], strictly if the weights are
    not all zero, via the three-term decomposition.

Symbolic identities use SymPy; signs and the sign-change pattern use exact
Fractions; monotonicity and positivity ranges use mpmath.
"""
from __future__ import annotations

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
    """G_m(p) = sum_{r=1}^{m-1} C(3m-2,3r-1) p^{3r}(1-p)^{3(m-r)}."""
    n = 3 * m - 2
    return sum(comb(n, 3 * r - 1) * p ** (3 * r) * (1 - p) ** (3 * (m - r))
               for r in range(1, m))


def Jr(m):
    """J_m(t), eq. (4.3)."""
    n = 3 * m - 2
    return sum(comb(n, 3 * r - 1) * t ** (3 * r - 1) * (r - (m - r) * t)
               for r in range(1, m))


def Jk(m):
    """J_m(t) in the k = 3r-1 form under eq. (4.3)."""
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
        # G_m(t/(1+t)) = (1+t)^{-3m} sum_r C(n,3r-1) t^{3r}
        lhs = sp.simplify(Gm_p(m).subs(p, t / (1 + t)))
        rhs = sp.simplify(sum(comb(n, 3 * r - 1) * t ** (3 * r) for r in range(1, m))
                          / (1 + t) ** (3 * m))
        assert sp.simplify(lhs - rhs) == 0, m
        # eq. (4.2): d/dt G_m(t/(1+t)) = 3 J_m(t)/(1+t)^{3m+1}
        dGdt = sp.diff(rhs, t)
        assert sp.simplify(dGdt - 3 * Jr(m) / (1 + t) ** (3 * m + 1)) == 0, m
        # k = 3r-1 rewrite of J_m
        assert sp.expand(Jr(m) - Jk(m)) == 0, m
    print("PASS: G_m t-form, derivative eq. (4.2)-(4.3), and k=3r-1 rewrite")


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


def check_R_and_moments(j_max: int = 60) -> None:
    twocos = [2, 1, -1, -2, -1, 1]                 # 2 cos(k pi/3), k = 0..5
    for j in range(j_max + 1):
        for a in range(3):
            assert 3 * R(a, j) == 2 ** j + twocos[(j - 2 * a) % 6], (a, j)
        # residue-class moments used in eq. (4.9)
        m1 = sum(k * comb(j, k) for k in range(j + 1) if k % 3 == 2)
        assert m1 == j * R(1, j - 1)
        m2 = sum(k * k * comb(j, k) for k in range(j + 1) if k % 3 == 2)
        assert m2 == j * (j - 1) * R(0, j - 2) + j * R(1, j - 1)
    print("PASS: R_a(j) closed form and the two residue-class moments")


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


def check_S_and_coeff(max_m: int = 60) -> None:
    for m in range(2, max_m + 1):
        n = 3 * m - 2
        # n+1 = 3m-1 = 2 or 5 (mod 6)
        assert (n + 1) % 6 in (2, 5)
        symbolic = poly_coeff_projective(m) if m <= 6 else None
        for j in range(n + 2):
            s = S_sum(n, j)
            if j >= 2:
                assert s == S_from_R(n, j), (m, j)
            assert 3 * s == three_S_table(n, j), (m, j)
            assert s >= 0, (m, j, s)                 # nonnegativity of S_{n,j}
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
        # positive x^2 coefficient: 3 S_{n,2} = 9d, d = n-1 > 0
        assert three_S_table(n, 2) == 9 * (n - 1) and S_sum(n, 2) > 0
        assert comb(n + 1, 2) * S_sum(n, 2) // (3 * (n + 1)) > 0
    print(f"PASS: S_{{n,j}} formulas, nonnegativity, eq.(4.6), x^2 > 0 (2<=m<={max_m})")


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
    # j = 5 (mod 6): 2^j - 3j + 1 > 0 for j >= 5, increment 2^j - 3 > 0
    for j in range(5, j_max):
        assert 2 ** j - 3 * j + 1 > 0 and 2 ** j - 3 > 0
    print("PASS: exponential bounds eq. (4.10)-(4.11) and their increments")


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
# 4.2  Log-concave weights
# ===========================================================================
def check_weighted_derivative() -> None:
    for m in range(2, 6):
        n = 3 * m - 2
        wsyms = sp.symbols(f"w1:{m}")
        w = {r: wsyms[r - 1] for r in range(1, m)}
        Gw_t = sum(w[r] * comb(n, 3 * r - 1) * t ** (3 * r) for r in range(1, m)) / (1 + t) ** (3 * m)
        Jw = sum(w[r] * comb(n, 3 * r - 1) * t ** (3 * r - 1) * (r - (m - r) * t) for r in range(1, m))
        assert sp.simplify(sp.diff(Gw_t, t) - 3 * Jw / (1 + t) ** (3 * m + 1)) == 0, m
    print("PASS: weighted derivative eq. (4.12)-(4.13)")


def B_block(m: int, r: int):
    """B_{m,r}(t), eq. (4.14), and the even-m center block eq. (4.15)."""
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
            assert sp.expand(B_block(m, m // 2) - center) == 0, m
        # constant weights: sum_r B_{m,r} = J_m
        allones = sum(B_block(m, r) for r in range(1, m // 2 + 1))
        assert sp.expand(allones - Jr(m)) == 0, m
    print("PASS: J_{m,w} = sum_r w_r B_{m,r}, center block, and sum_r B_{m,r} = J_m")


def check_block_sign_form() -> None:
    """sign(B_{m,r}) = sign(H_{m,r}); the hyperbolic identity eq. (4.16)."""
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
    print("PASS: sign(B_{m,r})=sign(H_{m,r}) and hyperbolic form eq. (4.16)")


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
    print("PASS: d tanh(3dx/2) increasing; odd-m final block positive")


def B_eval(m: int, r: int, tv: Fraction) -> Fraction:
    """B_{m,r}(t) in exact rational arithmetic (eqs. 4.14-4.15)."""
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
    print("PASS: paired blocks have at most one sign change, neg->pos (Lemma 4.3)")


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
        w = {r: ws[min(r, m - r) - 1] for r in range(1, m)}
        tv = Fraction(rng.randint(1, 999), 1000)
        blocks = [B_eval(m, r, tv) for r in range(1, L + 1)]
        Jw = sum(ws[r - 1] * blocks[r - 1] for r in range(1, L + 1))
        assert Jw >= 0, (m, tv)
        if any(x != 0 for x in ws):
            assert Jw > 0, (m, tv)
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


def main() -> None:
    check_t_substitution_and_derivative()
    check_projective_transform()
    check_binomial_identities()
    check_R_and_moments()
    check_S_and_coeff()
    check_exponential_bounds()
    check_bernstein_reconstruction()
    check_Jm_positive_and_Gm_increasing()
    check_weighted_derivative()
    check_block_decomposition()
    check_block_sign_form()
    check_block_monotone_ingredients()
    check_single_sign_change()
    check_theorem_kernel()
    print("ALL PASS: verify_kernel")


if __name__ == "__main__":
    main()
