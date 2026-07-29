#!/usr/bin/env python3
r"""Paper section 5 (Proof of the theorem), and section 1 (Introduction), Theorem 1.1.

Assembles the reduction into the main theorem and its consequences:

  * eq. (5.1): [x^m] of the Turanian equals C_{m,f}(mu+a,mu+b) - C_{m,f}(mu,mu+a+b),
    checked by direct convolution of the two defining series;
  * the imbalance arithmetic: the two parameter pairs share the sum
    s = 2mu+a+b, with deviations d_1 = |a-b|/2 <= d_2 = (a+b)/2;
  * Proposition 5.1: at fixed s, d -> C_{m,f}(s/2+d, s/2-d) is nonincreasing,
    strictly when some product f_k f_{m-k} is positive;
  * Theorem 1.1: coefficientwise nonnegativity of the Turanian on random
    rational log-concave sequences (exact arithmetic);
  * Corollary 5.2: the strict classification [x^m] Turanian > 0 iff some
    f_k f_{m-k} > 0 (mu >= 0, a,b > 0);
  * Remark 5.4: the interval-support clause of the hypothesis is necessary for
    the conclusion -- f_1 = f_4 = 1 satisfies the pointwise log-concavity
    inequality everywhere it is defined, yet [x^5] Turanian = -9360 at mu = 2,
    a = b = 1;
  * Corollary 5.3: the Stirling ratio (mu)_{3n}/(3n-1)! = Gamma(3n+mu)/
    (Gamma(mu)Gamma(3n)) ~ (3n)^mu/Gamma(mu), the shared radius of convergence,
    and midpoint (hence full) concavity of mu -> log F_f(mu;x);
  * the Section 1 triplication identity: for f_n = 1, F_f(mu;x) =
    3x d/dx _3F_2(mu/3,(mu+1)/3,(mu+2)/3; 1/3,2/3; x), i.e.
    [x^n] F_f = 3n [x^n] _3F_2 for all n >= 1.

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
            # direct convolution of the products vs C_{m,f}, which together give
            # eq. (5.1) termwise
            assert conv_coeff(Fa, Fb, m) == C_coef(m, f, mu + al, mu + be)
            assert conv_coeff(F0, Fs, m) == C_coef(m, f, mu, mu + al + be)
        # the two pairs share their sum, and the imbalances are ordered
        s = 2 * mu + al + be
        assert (mu + al) + (mu + be) == s == mu + (mu + al + be)
        d1 = abs(al - be) / 2
        d2 = (al + be) / 2
        assert d1 <= d2
        # d_1 = |alpha-beta|/2 is an ABSOLUTE value, so reading it off the signed
        # deviation above needs C_{m,f} to be symmetric in its two arguments.
        # That swap is what makes the imbalance well defined; assert it directly.
        for m in range(2, deg + 1):
            assert (C_coef(m, f, mu + al, mu + be)
                    == C_coef(m, f, mu + be, mu + al)), (m,)
    print("PASS: eq. (5.1) via direct convolution; shared sum, d_1 <= d_2, and "
          "C_{m,f}(u,v) = C_{m,f}(v,u)")


def check_degenerate_shifts(trials: int = 60, deg: int = 9,
                            seed: int = 20260728) -> None:
    """The two degenerate cases of the Theorem 1.1 proof.

    "The coefficients of degrees 0 and 1 in eq. (1.3) vanish" -- the series starts
    at n = 1, so the product starts at degree 2.  "If alpha = 0 or beta = 0, the
    Turanian is identically zero" -- both terms of eq. (5.1) then coincide.  Both
    need alpha or beta pinned to 0 and m taken below 2, so they are driven here
    rather than left to the randomized parameter sweeps.
    """
    rng = random.Random(seed)
    for _ in range(trials):
        lo = rng.randint(1, 2)
        hi = rng.randint(lo + 3, lo + 7)
        f = rand_logconcave(rng, lo, hi)
        mu = Fraction(rng.randint(0, 5), rng.randint(1, 4))
        gam = Fraction(rng.randint(1, 5), rng.randint(1, 4))
        # degrees 0 and 1 vanish
        Fa, Fb = F_coeffs(f, mu + gam, deg), F_coeffs(f, mu + gam, deg)
        assert conv_coeff(Fa, Fb, 0) == 0
        assert conv_coeff(Fa, Fb, 1) == 0
        # alpha = 0: the Turanian is identically zero
        for al, be in [(Fraction(0), gam), (gam, Fraction(0))]:
            Fa = F_coeffs(f, mu + al, deg)
            Fb = F_coeffs(f, mu + be, deg)
            F0 = F_coeffs(f, mu, deg)
            Fs = F_coeffs(f, mu + al + be, deg)
            for m in range(0, deg + 1):
                c = conv_coeff(Fa, Fb, m) - conv_coeff(F0, Fs, m)
                assert c == 0, ("Turanian not identically zero", m, al, be, c)
    print("PASS: degrees 0 and 1 vanish; alpha=0 or beta=0 gives Turanian = 0")


def check_schur_boundary(deg: int = 8) -> None:
    """What happens at d = s/2, which Proposition 5.1 excludes.

    The proposition is stated for 0 <= d < s/2 on (0,inf)^2.  At d = s/2 the second
    argument is v = 0, off the domain, and there C_{m,f}(s,0) = 0 because
    (0)_{3(m-k)} = 0: the nonincreasing conclusion extends by continuity, while
    strictness at the endpoint does not follow from the proposition.  Kept separate
    from check_schur_concavity, which stays inside the stated range.
    """
    f = {n: Fraction(n + 1) for n in range(1, deg + 1)}
    for n in range(2, deg):
        assert f[n] ** 2 >= f[n - 1] * f[n + 1], n
    for s in [Fraction(6), Fraction(15, 2)]:
        for m in range(2, deg + 1):
            assert C_coef(m, f, s, Fraction(0)) == 0, (m, s)      # v = 0 kills it
            interior = C_coef(m, f, s / 2 + s * Fraction(49, 100),
                              s / 2 - s * Fraction(49, 100))
            assert interior >= 0
            # the boundary value is the infimum of the interior values
            assert C_coef(m, f, s, Fraction(0)) <= interior, (m, s)
    print("PASS: the excluded boundary d = s/2 gives v = 0 and C_{m,f}(s,0) = 0, "
          "below every interior value (Proposition 5.1's domain is real)")


def check_cor_strict_mu_zero(trials: int = 60, deg: int = 9,
                             seed: int = 20260730) -> None:
    """Corollary 5.2's mu = 0 branch, in the form its proof uses.

    The proof says: if mu = 0 then F_f(0;x) = 0, so the coefficient EQUALS
    C_{m,f}(alpha,beta), a sum of nonnegative terms with at least one strictly
    positive.  That identification is what is asserted here, alongside the strict
    classification at mu = 0.
    """
    rng = random.Random(seed)
    for _ in range(trials):
        lo = rng.randint(1, 2)
        hi = rng.randint(lo + 3, lo + 7)
        f = rand_logconcave(rng, lo, hi)
        al = Fraction(rng.randint(1, 5), rng.randint(1, 4))
        be = Fraction(rng.randint(1, 5), rng.randint(1, 4))
        Fa, Fb = F_coeffs(f, al, deg), F_coeffs(f, be, deg)
        F0, Fs = F_coeffs(f, Fraction(0), deg), F_coeffs(f, al + be, deg)
        for m in range(2, deg + 1):
            c = conv_coeff(Fa, Fb, m) - conv_coeff(F0, Fs, m)
            # the identification the proof uses
            assert c == C_coef(m, f, al, be), (m,)
            has_pair = any(f.get(r, 0) and f.get(m - r, 0) for r in range(1, m))
            assert (c > 0) == has_pair, (m, c, has_pair)          # strict, at mu=0
    print("PASS: Corollary 5.2 at mu=0 -- the coefficient EQUALS C_{m,f}(alpha,beta), "
          "and is > 0 exactly when some f_k f_{m-k} > 0")


def check_hypothesis_and_indexing(deg: int = 10) -> None:
    """Three prose-level claims of section 1 that reduce to computations.

    (i) The stated definition: (f_n) nonnegative, f_n^2 >= f_{n-1}f_{n+1} where the
        three terms are defined, and positive support an interval of integers.
    (ii) The remark that indexing from n >= 1 is equivalent to Karp-Zhang's n >= 0:
        restriction preserves log-concavity and interval support, and any admissible
        tail extends by setting f_0 = 0.
    (iii) Log-concavity with no internal zeros makes f_{n+1}/f_n nonincreasing on the
        support, which is why R > 0 in Corollary 5.3.
    """
    cases = [
        {n: Fraction(1) for n in range(1, deg + 1)},
        {n: Fraction(2) ** n for n in range(1, deg + 1)},
        {n: (Fraction(0) if n < 3 or n > 7 else Fraction(8 - n)) for n in range(1, deg + 1)},
        {n: (Fraction(5) if n == 4 else Fraction(0)) for n in range(1, deg + 1)},
    ]
    for f in cases:
        supp = [n for n in sorted(f) if f[n] > 0]
        # (i) nonnegative, interval support, log-concave where defined
        assert all(v >= 0 for v in f.values())
        assert supp == list(range(supp[0], supp[-1] + 1)), ("internal zero", f)
        for n in supp[1:-1]:
            assert f[n] ** 2 >= f[n - 1] * f[n + 1], (n, f)
        # (ii) extending by f_0 = 0 preserves both properties
        g = dict(f)
        g[0] = Fraction(0)
        gsupp = [n for n in sorted(g) if g[n] > 0]
        assert gsupp == supp
        for n in gsupp[1:-1]:
            assert g[n] ** 2 >= g[n - 1] * g[n + 1], (n,)
        # and restricting back to n >= 1 recovers f
        assert {n: v for n, v in g.items() if n >= 1} == f
        # (iii) f_{n+1}/f_n nonincreasing on the support, hence R > 0
        ratios = [f[n + 1] / f[n] for n in supp[:-1]]
        for a, b in zip(ratios, ratios[1:]):
            assert b <= a, ("ratio not nonincreasing", f)
        if ratios:
            # bounded ratios give a positive radius: limsup |f_n|^{1/n} < inf
            assert max(ratios) < Fraction(10 ** 9)
    print("PASS: section 1's hypothesis (nonnegative, interval support, "
          "log-concave), the n>=1 vs n>=0 equivalence, and f_{n+1}/f_n "
          "nonincreasing (hence R > 0)")


def check_internal_zeros_load_bearing() -> None:
    """Remark 5.4: the interval-support clause is necessary for the CONCLUSION.

    Section 1 hypothesises f_n^2 >= f_{n-1}f_{n+1} where defined AND positive
    support an interval of integers.  The second clause does not follow from the
    first: with f_1 = f_4 = 1 the two positive indices differ by 3, so the RIGHT
    side f_{n-1}f_{n+1} vanishes at every index (a nonzero product would need two
    positive indices exactly 2 apart) and the inequality holds throughout.  It is
    NOT an equality throughout -- at n = 4 it reads 1 >= 0 -- so the remark must
    not claim both sides vanish; the strict index is pinned below.  (A lone
    internal zero would fail: f_k = 0 with f_{k-1}, f_{k+1} > 0 gives
    0 >= f_{k-1}f_{k+1} > 0.)  On such a sequence the weights w_k = f_k f_{m-k}
    decrease toward the centre, eq. (4.2) fails, and so does Theorem 1.1.  This
    crosses the boundary the other checks stay inside.
    """
    f = {1: Fraction(1), 4: Fraction(1)}                 # support {1,4}, zeros at 2,3

    # (i) the pointwise inequality holds at every index where it is defined, and
    #     the right side vanishes there -- which is WHY it holds.
    for n in range(2, 9):
        a, b, c = f.get(n - 1, Fraction(0)), f.get(n, Fraction(0)), f.get(n + 1, Fraction(0))
        assert a * c == 0, ("f_{n-1}f_{n+1} should vanish at every index", n)
        assert b * b >= a * c, ("pointwise log-concavity fails", n)
    # (i') it is strict exactly at n = 4.  Remark 5.4's prose says "strictly at
    #      n = 4"; an earlier draft said "both sides vanishing", which is false
    #      there.  Pin the strict set so that wording cannot drift again.
    strict = [n for n in range(2, 9)
              if f.get(n, Fraction(0)) ** 2
              > f.get(n - 1, Fraction(0)) * f.get(n + 1, Fraction(0))]
    assert strict == [4], f"inequality should be strict exactly at n=4, got {strict}"
    # (ii) but the support is not an interval.
    supp = sorted(k for k, v in f.items() if v > 0)
    assert supp != list(range(supp[0], supp[-1] + 1)), "support must NOT be an interval"
    # (iii) a lone internal zero would have failed (i) -- minimality of the run.
    g = {1: Fraction(1), 3: Fraction(1)}
    assert not (g.get(2, Fraction(0)) ** 2 >= g[1] * g[3]), \
        "a single internal zero must contradict the inequality"

    # (iv) eq. (4.2) fails at m = 5: the weights decrease toward the centre.
    m = 5
    w = [f.get(k, Fraction(0)) * f.get(m - k, Fraction(0)) for k in range(1, m)]
    assert w == [Fraction(1), Fraction(0), Fraction(0), Fraction(1)], w
    assert w[0] > w[1], "weights must decrease toward the centre for this to bite"

    # (v) the conclusion fails, at the value the paper prints, by two routes.
    mu, al, be = Fraction(2), Fraction(1), Fraction(1)
    via_C = C_coef(m, f, mu + al, mu + be) - C_coef(m, f, mu, mu + al + be)
    via_conv = (conv_coeff(F_coeffs(f, mu + al, m), F_coeffs(f, mu + be, m), m)
                - conv_coeff(F_coeffs(f, mu, m), F_coeffs(f, mu + al + be, m), m))
    assert via_C == via_conv, (via_C, via_conv)
    assert via_C == Fraction(-9360), f"paper prints -9360, got {via_C}"

    # (vi) restoring interval support at the same m and shifts restores the sign.
    h = {n: Fraction(1) for n in range(1, m + 1)}
    good = C_coef(m, h, mu + al, mu + be) - C_coef(m, h, mu, mu + al + be)
    assert good > 0, good
    print("PASS: Remark 5.4 -- interval support is load-bearing for Theorem 1.1, "
          "not just for its proof: f_1=f_4=1 gives [x^5] Turanian = -9360 at "
          "mu=2, a=b=1 (two routes agree), while f_n=1 gives > 0")


def check_extremal_log_concave(deg: int = 9) -> None:
    """The extremal side of the hypothesis: equality in log-concavity.

    Equality f_n^2 = f_{n-1} f_{n+1} means geometric (f_n), which gives CONSTANT
    weights w_k and so the degenerate side of Lemma 3.1.  That case and single-point
    support are the two boundaries of the admissible class, and both are named
    explicitly here rather than sampled.
    """
    cases = {
        "f_n = 1": {n: Fraction(1) for n in range(1, deg + 1)},
        "geometric q=2": {n: Fraction(2) ** n for n in range(1, deg + 1)},
        "geometric q=1/3": {n: Fraction(1, 3) ** n for n in range(1, deg + 1)},
        "support {3}": {n: (Fraction(5) if n == 3 else Fraction(0))
                        for n in range(1, deg + 1)},
    }
    for name, f in cases.items():
        supp = [n for n in sorted(f) if f[n] > 0]
        for n in supp[1:-1]:
            assert f[n] ** 2 >= f[n - 1] * f[n + 1], (name, n)
        for mu, al, be in [(Fraction(0), Fraction(1), Fraction(2)),
                           (Fraction(3, 2), Fraction(1, 3), Fraction(1, 3)),
                           (Fraction(4), Fraction(2), Fraction(5))]:
            Fa, Fb = F_coeffs(f, mu + al, deg), F_coeffs(f, mu + be, deg)
            F0, Fs = F_coeffs(f, mu, deg), F_coeffs(f, mu + al + be, deg)
            for m in range(2, deg + 1):
                c = conv_coeff(Fa, Fb, m) - conv_coeff(F0, Fs, m)
                assert c == C_coef(m, f, mu + al, mu + be) - C_coef(
                    m, f, mu, mu + al + be), (name, m)       # eq. (5.1)
                assert c >= 0, ("Theorem 1.1", name, m, c)
                has_pair = any(f.get(r, 0) and f.get(m - r, 0) for r in range(1, m))
                assert (c > 0) == has_pair, ("Corollary 5.2", name, m, c, has_pair)
    print(f"PASS: Theorem 1.1, eq. (5.1) and Corollary 5.2 on the extremal cases "
          f"({', '.join(cases)})")


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
        # Proposition 5.1 states 0 <= d < s/2, so draw strictly inside it.  The
        # boundary d = s/2 (i.e. v = 0) lies outside both that range and the
        # proposition's domain (0,inf)^2; it is handled by check_schur_boundary.
        ds = sorted(Fraction(rng.randint(0, 99), 100) * (s / 2) for _ in range(6))
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


def check_mu_zero_boundary(trials: int = 80, deg: int = 10,
                           seed: int = 20260727) -> None:
    """Theorem 1.1's boundary case mu = 0.

    The proof disposes of it by F_f(0;x) = 0 -- which holds because (0)_{3n} = 0
    for every n >= 1 -- leaving the Turanian equal to F_f(alpha;x)F_f(beta;x),
    of nonnegative coefficients.  Driven with mu pinned to 0 so the mechanism
    itself -- and not just the resulting inequality -- is asserted.
    """
    rng = random.Random(seed)
    for n in range(1, 3 * deg + 1):
        assert poch(Fraction(0), 3 * n) == 0, n           # (0)_{3n} = 0
    for _ in range(trials):
        lo = rng.randint(1, 2)
        hi = rng.randint(lo + 3, lo + 7)
        f = rand_logconcave(rng, lo, hi)
        F0 = F_coeffs(f, Fraction(0), deg)
        assert all(c == 0 for c in F0), F0                # F_f(0;x) = 0
        al = Fraction(rng.randint(1, 5), rng.randint(1, 4))
        be = Fraction(rng.randint(1, 5), rng.randint(1, 4))
        Fa, Fb = F_coeffs(f, al, deg), F_coeffs(f, be, deg)
        Fs = F_coeffs(f, al + be, deg)
        for m in range(2, deg + 1):
            assert conv_coeff(F0, Fs, m) == 0, (m,)       # second term drops out
            c = conv_coeff(Fa, Fb, m) - conv_coeff(F0, Fs, m)
            assert c == conv_coeff(Fa, Fb, m) >= 0, (m, c)
    print("PASS: mu=0 boundary case -- F_f(0;x)=0, Turanian = F_f(alpha)F_f(beta) >= 0")


# ===========================================================================
# Corollary 5.3 (Stirling ratio, radius, log-concavity in mu)
# ===========================================================================
def coeff_ratio(mu, n: int):
    """(mu)_{3n}/(3n-1)! as Gamma(3n+mu)/(Gamma(mu)Gamma(3n))."""
    return mp.rf(mu, 3 * n) / mp.factorial(3 * n - 1)


def check_stirling() -> None:
    # At mu = 1 the asymptotic is EXACT: (1)_{3n}/(3n-1)! = (3n)!/(3n-1)! = 3n =
    # (3n)^1/Gamma(1), so the residual is identically zero.  The convergence test
    # below is therefore non-strict, since 0 < 0 is false while the claim holds.
    for mu in [mp.mpf("0.7"), mp.mpf(1), mp.mpf("1.5"), mp.mpf("3.2"), mp.mpf(6)]:
        for n in [5, 20, 100]:
            gamma_form = mp.gamma(3 * n + mu) / (mp.gamma(mu) * mp.gamma(3 * n))
            # RELATIVE tolerance: the quantity reaches ~1e7 at (mu,n)=(3.2,100) and
            # grows with both arguments, so the comparison must scale with it.
            assert abs(coeff_ratio(mu, n) - gamma_form) <= mp.mpf("1e-30") * abs(gamma_form)
        # asymptotic ~ (3n)^mu/Gamma(mu): the correction is O(1/n) with the
        # Stirling constant mu(mu-1)/6, so (ratio-1)*n -> mu(mu-1)/6.
        target = mu * (mu - 1) / 6
        prev = None
        for n in [200, 400, 800, 1600]:
            ratio = coeff_ratio(mu, n) * mp.gamma(mu) / mp.mpf(3 * n) ** mu
            scaled = (ratio - 1) * n
            if prev is not None:
                # non-strict: exact at mu = 1, where both sides are 0
                assert abs(scaled - target) <= abs(prev - target), (mu, n)
            prev = scaled
        # RELATIVE to the scale of the limit, which is mu(mu-1)/6 and so grows
        # quadratically in mu.
        assert abs(prev - target) <= mp.mpf("1e-3") * (1 + abs(target)), (mu, prev, target)
        if mu == 1:
            assert target == 0 and prev == 0            # the exact case
    print("PASS: Stirling ratio identity and (3n)^mu/Gamma(mu) asymptotic (O(1/n)), "
          "including the exact case mu=1")


def check_radius_of_convergence() -> None:
    """f_n = 1: the coefficients (mu)_{3n}/(3n-1)! grow polynomially, so their
    n-th root decreases to 1 (radius R = 1, matching sum f_n x^n = sum x^n)."""
    for mu in [mp.mpf("0.7"), mp.mpf("2"), mp.mpf("4.5")]:
        roots = [coeff_ratio(mu, n) ** (mp.mpf(1) / n) for n in (400, 1600, 6400, 25600)]
        for a, b in zip(roots, roots[1:]):
            assert 1 < b < a                          # decreasing to 1 from above
        # the n-th root converges to 1 like ~3e-4 at n = 25600
        assert abs(roots[-1] - 1) < mp.mpf("3e-3")
    print("PASS: radius of convergence R = 1 for f_n = 1 (matches sum f_n x^n)")


def check_radius_matches_general_f() -> None:
    """Corollary 5.3's radius claim for a NON-constant log-concave (f_n).

    The corollary asserts F_f(mu;.) has the same radius R as sum f_n x^n for every
    admissible (f_n), not only f_n = 1: the extra factor (mu)_{3n}/(3n-1)! grows
    polynomially, so it cannot move the radius.  Checked on geometric weights
    f_n = r^n, which are log-concave with no internal zeros and radius 1/r.
    """
    for r, R in [(mp.mpf("0.5"), mp.mpf(2)), (mp.mpf("0.25"), mp.mpf(4)),
                 (mp.mpf(2), mp.mpf("0.5"))]:
        for mu in [mp.mpf("0.7"), mp.mpf(3)]:
            # |f_n c_n|^{1/n} -> r * 1 = r, so the radius is 1/r = R
            roots = [(r ** n * coeff_ratio(mu, n)) ** (mp.mpf(1) / n)
                     for n in (400, 1600, 6400, 25600)]
            for a, b in zip(roots, roots[1:]):
                assert b < a                          # decreasing toward r
            assert abs(roots[-1] - r) < mp.mpf("3e-3") * r, (r, mu, roots[-1])
            assert abs(1 / roots[-1] - R) < mp.mpf("1e-2") * R, (r, mu, R)
    print("PASS: F_f(mu;.) shares the radius of sum f_n x^n for geometric f_n "
          "(Corollary 5.3, general (f_n))")


def check_continuity_in_mu() -> None:
    """mu -> F_f(mu;x) is finite, positive and CONTINUOUS on (0,inf).

    Corollary 5.3 needs continuity to upgrade midpoint concavity to concavity, and
    it is the one hypothesis of that step the harness otherwise never touches.
    Checked by evaluating at nearby mu and bounding the increment, plus positivity
    and finiteness on a grid.
    """
    for xv in [mp.mpf("0.2"), mp.mpf("0.6")]:
        for mu in [mp.mpf("0.3"), mp.mpf(1), mp.mpf("2.5"), mp.mpf(5)]:
            base = F_analytic(mu, xv)
            assert mp.isfinite(base) and base > 0, (mu, xv, base)
            prev = None
            for h in [mp.mpf("1e-2"), mp.mpf("1e-3"), mp.mpf("1e-4")]:
                gap = abs(F_analytic(mu + h, xv) - base)
                assert mp.isfinite(gap)
                if prev is not None:
                    assert gap < prev                 # increment -> 0 with h
                prev = gap
            assert prev < mp.mpf("1e-3") * base, (mu, xv, prev)
    print("PASS: mu -> F_f(mu;x) finite, positive and continuous on (0,inf)")


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


# ===========================================================================
# Section 1 intro: the f_n = 1 triplication identity
#   F_f(mu;x) = 3x d/dx 3F2(mu/3,(mu+1)/3,(mu+2)/3; 1/3,2/3; x)
# ===========================================================================
def check_triplication_3F2(deg: int = 12) -> None:
    """For f_n = 1 the Pochhammer triplication (mu)_{3n} = 3^{3n} (mu/3)_n
    ((mu+1)/3)_n ((mu+2)/3)_n together with (3n)! = 3^{3n} n! (1/3)_n (2/3)_n
    gives [x^n] F_f = (mu)_{3n}/(3n-1)! = 3n (mu/3)_n((mu+1)/3)_n((mu+2)/3)_n
    / (n! (1/3)_n (2/3)_n) = 3n [x^n] 3F2, i.e. F_f = 3x d/dx 3F2.  Both sides
    are compared exactly over Q: the left from the defining series (poch as in
    F_coeffs), the right from the 3F2 coefficient (a)_n(b)_n(c)_n/((d)_n(e)_n n!)
    scaled by the derivative factor 3n.  (Paper Section 1.)"""
    third = Fraction(1, 3)
    for mu in [Fraction(0), Fraction(1), Fraction(7, 5), Fraction(5, 2), Fraction(11, 3)]:
        for n in range(1, deg + 1):
            lhs = poch(mu, 3 * n) / factorial(3 * n - 1)             # [x^n] F_f, f_n=1
            c_n = (poch(mu * third, n) * poch((mu + 1) * third, n)
                   * poch((mu + 2) * third, n)
                   / (factorial(n) * poch(third, n) * poch(2 * third, n)))  # [x^n] 3F2
            assert lhs == 3 * n * c_n, (mu, n, lhs, 3 * n * c_n)
    print("PASS: f_n=1 triplication F_f = 3x d/dx 3F2(mu/3,(mu+1)/3,(mu+2)/3;1/3,2/3;x)")


def main() -> None:
    check_hypothesis_and_indexing()
    check_internal_zeros_load_bearing()
    check_delta_C_and_imbalance()
    check_degenerate_shifts()
    check_schur_concavity()
    check_schur_boundary()
    check_main_theorem()
    check_extremal_log_concave()
    check_mu_zero_boundary()
    check_cor_strict_mu_zero()
    check_triplication_3F2()
    check_stirling()
    check_radius_of_convergence()
    check_radius_matches_general_f()
    check_continuity_in_mu()
    check_log_concavity_in_mu()
    print("ALL PASS: verify_theorem")


if __name__ == "__main__":
    main()
