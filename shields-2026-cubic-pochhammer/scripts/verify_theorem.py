#!/usr/bin/env python3
r"""Paper section 5 (Proof of the theorem) and its corollaries.

Assembles the reduction into the main theorem and its consequences:

  * eq. (5.1): [x^m] of the Turanian equals C_{m,f}(mu+a,mu+b) - C_{m,f}(mu,mu+a+b),
    checked by direct convolution of the two defining series;
  * the imbalance arithmetic: the two parameter pairs share the sum
    s = 2mu+a+b, with deviations d_1 = |a-b|/2 <= d_2 = (a+b)/2;
  * Proposition 5.1: at fixed s, d -> C_{m,f}(s/2+d, s/2-d) is nonincreasing,
    strictly when some product f_r f_{m-r} is positive;
  * Theorem 1.1: coefficientwise nonnegativity of the Turanian on random
    rational log-concave sequences (exact arithmetic);
  * Corollary 5.2: the strict classification [x^m] Turanian > 0 iff some
    f_r f_{m-r} > 0 (mu >= 0, a,b > 0);
  * Corollary 5.3: the Stirling ratio (mu)_{3n}/(3n-1)! = Gamma(3n+mu)/
    (Gamma(mu)Gamma(3n)) ~ (3n)^mu/Gamma(mu), the shared radius of convergence,
    and midpoint (hence full) concavity of mu -> log F_f(mu;x).

Exact convolution work uses Fractions; asymptotics use mpmath.
"""
from __future__ import annotations

import random
from fractions import Fraction

import mpmath as mp

mp.mp.dps = 40


# ===========================================================================
# Exact building blocks over Q
# ===========================================================================
def factorial(n: int) -> int:
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


def poch(u: Fraction, j: int) -> Fraction:
    p = Fraction(1)
    for i in range(j):
        p *= u + i
    return p


def F_coeffs(f: dict, u: Fraction, deg: int) -> list:
    """[x^0..x^deg] of F_f(u;x) = sum_{n>=1} f_n (u)_{3n}/(3n-1)! x^n."""
    a = [Fraction(0)] * (deg + 1)
    for n in range(1, deg + 1):
        a[n] = f.get(n, Fraction(0)) * poch(u, 3 * n) / factorial(3 * n - 1)
    return a


def conv_coeff(a: list, b: list, m: int) -> Fraction:
    return sum(a[r] * b[m - r] for r in range(0, m + 1))


def C_coef(m: int, f: dict, u: Fraction, v: Fraction) -> Fraction:
    """C_{m,f}(u,v), eq. (2.2)."""
    total = Fraction(0)
    for r in range(1, m):
        fr, fmr = f.get(r, Fraction(0)), f.get(m - r, Fraction(0))
        if fr and fmr:
            total += (fr * fmr * poch(u, 3 * r) * poch(v, 3 * (m - r))
                      / (factorial(3 * r - 1) * factorial(3 * (m - r) - 1)))
    return total


def rand_logconcave(rng: random.Random, lo: int, hi: int) -> dict:
    f = {lo: Fraction(rng.randint(1, 6))}
    ratio = Fraction(rng.randint(3, 9), rng.randint(1, 3))
    for n in range(lo, hi):
        f[n + 1] = f[n] * ratio
        ratio *= Fraction(rng.randint(1, 20), rng.randint(21, 40))
    ks = sorted(f)
    for i in range(1, len(ks) - 1):
        assert f[ks[i]] ** 2 >= f[ks[i - 1]] * f[ks[i + 1]]
    return f


# ===========================================================================
# 5.1  eq. (5.1) and the imbalance arithmetic
# ===========================================================================
def check_delta_C_and_imbalance(trials: int = 200, deg: int = 10,
                                seed: int = 20260721) -> None:
    rng = random.Random(seed)
    for _ in range(trials):
        lo = rng.randint(1, 2)
        hi = rng.randint(lo + 3, lo + 6)
        f = rand_logconcave(rng, lo, hi)
        mu = Fraction(rng.randint(0, 5), rng.randint(1, 4))
        al = Fraction(rng.randint(1, 5), rng.randint(1, 4))
        be = Fraction(rng.randint(1, 5), rng.randint(1, 4))
        Fa = F_coeffs(f, mu + al, deg)
        Fb = F_coeffs(f, mu + be, deg)
        F0 = F_coeffs(f, mu, deg)
        Fs = F_coeffs(f, mu + al + be, deg)
        for m in range(2, deg + 1):
            # direct convolution of the products vs C_{m,f}
            assert conv_coeff(Fa, Fb, m) == C_coef(m, f, mu + al, mu + be)
            assert conv_coeff(F0, Fs, m) == C_coef(m, f, mu, mu + al + be)
            turan = conv_coeff(Fa, Fb, m) - conv_coeff(F0, Fs, m)
            delta = C_coef(m, f, mu + al, mu + be) - C_coef(m, f, mu, mu + al + be)
            assert turan == delta                                 # eq. (5.1)
        # shared sum and ordered deviations
        s = 2 * mu + al + be
        assert (mu + al) + (mu + be) == s and mu + (mu + al + be) == s
        d1 = abs(al - be) / 2
        d2 = (al + be) / 2
        assert (mu + al) - s / 2 == (al - be) / 2 and mu - s / 2 == -(al + be) / 2
        assert d1 <= d2
    print("PASS: eq. (5.1) via direct convolution; shared sum, d_1 <= d_2")


# ===========================================================================
# 5.1  Proposition 5.1 (Schur-concavity of the convolution)
# ===========================================================================
def check_schur_concavity(trials: int = 300, seed: int = 20260722) -> None:
    rng = random.Random(seed)
    for _ in range(trials):
        lo = rng.randint(1, 2)
        hi = rng.randint(lo + 2, lo + 6)
        f = rand_logconcave(rng, lo, hi)
        s = Fraction(rng.randint(4, 14), rng.randint(1, 3))
        ds = sorted(Fraction(rng.randint(0, 100), 100) * (s / 2) for _ in range(6))
        for m in range(2, 2 * hi):
            has_pair = any(f.get(r, 0) and f.get(m - r, 0) for r in range(1, m))
            vals = [C_coef(m, f, s / 2 + d, s / 2 - d) for d in ds]
            for (da, va), (db, vb) in zip(zip(ds, vals), zip(ds[1:], vals[1:])):
                assert va >= vb                                   # nonincreasing
                if has_pair and da < db:
                    assert va > vb                                # strict
    print("PASS: Proposition 5.1 (C_{m,f}(s/2+d,s/2-d) nonincreasing, strict)")


# ===========================================================================
# Theorem 1.1 and Corollary 5.2
# ===========================================================================
def check_main_theorem(trials: int = 200, deg: int = 12, seed: int = 20260723) -> None:
    rng = random.Random(seed)
    for _ in range(trials):
        lo = rng.randint(1, 2)
        hi = rng.randint(lo + 3, lo + 7)
        f = rand_logconcave(rng, lo, hi)
        mu = Fraction(rng.randint(0, 5), rng.randint(1, 4))
        al = Fraction(rng.randint(1, 5), rng.randint(1, 4))
        be = Fraction(rng.randint(1, 5), rng.randint(1, 4))
        Fa, Fb = F_coeffs(f, mu + al, deg), F_coeffs(f, mu + be, deg)
        F0, Fs = F_coeffs(f, mu, deg), F_coeffs(f, mu + al + be, deg)
        for m in range(2, deg + 1):
            c = conv_coeff(Fa, Fb, m) - conv_coeff(F0, Fs, m)
            assert c >= 0, (m, c)                                 # Theorem 1.1
            has_pair = any(f.get(r, 0) and f.get(m - r, 0) for r in range(1, m))
            if al > 0 and be > 0:
                assert (c > 0) == has_pair, (m, c, has_pair)      # Corollary 5.2
    print("PASS: Theorem 1.1 nonnegativity and Corollary 5.2 strict classification")


# ===========================================================================
# Corollary 5.3 (Stirling ratio, radius, log-concavity in mu)
# ===========================================================================
def coeff_ratio(mu, n: int):
    """(mu)_{3n}/(3n-1)! as Gamma(3n+mu)/(Gamma(mu)Gamma(3n))."""
    return mp.rf(mu, 3 * n) / mp.factorial(3 * n - 1)


def check_stirling() -> None:
    for mu in [mp.mpf("0.7"), mp.mpf("1.5"), mp.mpf("3.2")]:
        for n in [5, 20, 100]:
            gamma_form = mp.gamma(3 * n + mu) / (mp.gamma(mu) * mp.gamma(3 * n))
            assert abs(coeff_ratio(mu, n) - gamma_form) < mp.mpf("1e-30")
        # asymptotic ~ (3n)^mu/Gamma(mu): the correction is O(1/n) with the
        # Stirling constant mu(mu-1)/6, so (ratio-1)*n -> mu(mu-1)/6.
        prev = None
        for n in [200, 400, 800, 1600]:
            ratio = coeff_ratio(mu, n) * mp.gamma(mu) / mp.mpf(3 * n) ** mu
            scaled = (ratio - 1) * n
            if prev is not None:
                assert abs(scaled - mu * (mu - 1) / 6) < abs(prev - mu * (mu - 1) / 6)
            prev = scaled
        assert abs(prev - mu * (mu - 1) / 6) < mp.mpf("1e-3")
    print("PASS: Stirling ratio identity and (3n)^mu/Gamma(mu) asymptotic (O(1/n))")


def check_radius_of_convergence() -> None:
    """f_n = 1: the coefficients (mu)_{3n}/(3n-1)! grow polynomially, so their
    n-th root decreases to 1 (radius R = 1, matching sum f_n x^n = sum x^n)."""
    for mu in [mp.mpf("0.7"), mp.mpf("2"), mp.mpf("4.5")]:
        roots = [coeff_ratio(mu, n) ** (mp.mpf(1) / n) for n in (400, 1600, 6400, 25600)]
        for a, b in zip(roots, roots[1:]):
            assert 1 < b < a                          # decreasing to 1 from above
        assert abs(roots[-1] - 1) < mp.mpf("0.02")
    print("PASS: radius of convergence R = 1 for f_n = 1 (matches sum f_n x^n)")


def F_analytic(mu, xv):
    """F_f(mu;x) = sum_{n>=1} (mu)_{3n}/(3n-1)! x^n for f_n = 1, |x| < 1."""
    return mp.nsum(lambda n: coeff_ratio(mu, int(n)) * xv ** int(n), [1, mp.inf])


def check_log_concavity_in_mu() -> None:
    for xv in [mp.mpf("0.2"), mp.mpf("0.5"), mp.mpf("0.8")]:
        # midpoint concavity: F(mu+h)^2 >= F(mu)F(mu+2h)
        for mu in [mp.mpf("0.5"), mp.mpf("1.3"), mp.mpf("3")]:
            for h in [mp.mpf("0.3"), mp.mpf("1")]:
                lhs = F_analytic(mu + h, xv) ** 2
                rhs = F_analytic(mu, xv) * F_analytic(mu + 2 * h, xv)
                assert lhs >= rhs, (xv, mu, h)
        # full concavity: second difference of mu -> log F is <= 0 on a grid
        mus = [mp.mpf(i) / 10 for i in range(3, 40)]
        logs = [mp.log(F_analytic(mu, xv)) for mu in mus]
        for a, b, c in zip(logs, logs[1:], logs[2:]):
            assert a - 2 * b + c < mp.mpf("1e-30")               # concave
    print("PASS: mu -> log F_f(mu;x) midpoint-concave, hence concave (Corollary 5.3)")


def main() -> None:
    check_delta_C_and_imbalance()
    check_schur_concavity()
    check_main_theorem()
    check_stirling()
    check_radius_of_convergence()
    check_log_concavity_in_mu()
    print("ALL PASS: verify_theorem")


if __name__ == "__main__":
    main()
