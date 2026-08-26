#!/usr/bin/env python3
r"""Paper section `sec:cubic-proof` (Proof of the cubic theorem) and section `sec:consequences` (Consequences),
with `sec:introduction`'s hypothesis of `thm:main` and the objects it
consumes from `sec:reduction`.

Assembles the reduction into the main theorem and its consequences:

  * `eq:delta-C`: [x^m] of the Turanian equals C_{m,f}(mu+a,mu+b) - C_{m,f}(mu,mu+a+b),
    checked by direct convolution of the two defining series;
  * the imbalance arithmetic: the two parameter pairs share the sum
    s = 2mu+a+b, with deviations d_1 = |a-b|/2 <= d_2 = (a+b)/2;
  * `cor:C-schur`: at fixed s, d -> C_{m,f}(s/2+d, s/2-d) is nonincreasing on
    the CLOSED [0, s/2], strictly when some product f_k f_{m-k} is positive --
    the endpoint reached through the identity C_{m,f}(s,0) = 0;
  * `thm:main`: coefficientwise nonnegativity of the Turanian on random
    rational log-concave sequences (exact arithmetic);
  * `cor:strict`: the strict classification [x^m] Turanian > 0 iff some
    f_k f_{m-k} > 0 (mu >= 0, a,b > 0), together with the two support
    descriptions it reads off -- I = {a,...,b} giving exactly the degrees
    2a,...,2b, and I = {a,a+1,...} giving exactly m >= 2a;
  * `rem:internal-zeros`: the interval-support clause of the hypothesis is necessary for
    the conclusion -- f_1 = f_4 = 1 satisfies the pointwise log-concavity
    inequality everywhere it is defined, yet [x^5] Turanian = -9360 at mu = 2,
    a = b = 1;
  * `cor:ordinary`: the Stirling ratio (mu)_{3n}/(3n-1)! = Gamma(3n+mu)/
    (Gamma(mu)Gamma(3n)) ~ (3n)^mu/Gamma(mu), local uniform convergence in mu on
    the proof's own 0 <= mu <= M under its majorant M e^M (3n)^M, the shared
    radius of convergence, and STRICT midpoint (hence strict) concavity of
    mu -> log F_f(mu;x);

  * `subsec:hypergeometric-specialization`'s triplication identity: for f_n = 1, F_f(mu;x) =
    3x d/dx _3F_2(mu/3,(mu+1)/3,(mu+2)/3; 1/3,2/3; x), i.e.
    [x^n] F_f = 3n [x^n] _3F_2 for all n >= 1.

`thm:main`'s own fixed-sum form -- the closed imbalance range 0 <= d1 <= d2
<= s/2, the arbitrary-weight `cor:C-schur`, `cor:strict`'s exact support
I+I, and `cor:differential` -- is covered in check_fixed_sum_schur.py.  What is
checked here is the Turanian specialization and the analytic `cor:ordinary`.

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
    """C_{m,f}(u,v), `eq:C-def` at the weights of `eq:w-from-f`."""
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
# section `sec:cubic-proof`: `eq:delta-C` and the imbalance arithmetic
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
            # `eq:delta-C` termwise
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
    print("PASS: `eq:delta-C` via direct convolution; shared sum, d_1 <= d_2, and "
          "C_{m,f}(u,v) = C_{m,f}(v,u)")


def check_degenerate_shifts(trials: int = 60, deg: int = 9,
                            seed: int = 20260728) -> None:
    """The two degenerate cases of the `thm:main` proof.

    "The coefficients of degrees 0 and 1 in `eq:schur-def` vanish" -- the series starts
    at n = 1, so the product starts at degree 2.  And at alpha = 0 or beta = 0 the
    two parameter pairs of `eq:delta-C` coincide, up to the exchange of arguments the
    proof's specialization uses, so the Turanian is identically zero -- the case
    d_1 = d_2 of the fixed-sum statement.  Both need alpha or beta pinned to 0 and
    m taken below 2, so they are driven here rather than left to the randomized
    parameter sweeps.
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
    """The endpoint d = s/2, which `cor:C-schur`'s CLOSED range includes.

    The beta route of `prop:kernel-exact` covers 0 <= d < s/2, because Beta(s,0) is
    not a law.  At d = s/2 the second argument is v = 0 and C_{m,f}(s,0) = 0,
    since (0)_{3(m-k)} = 0; that identity, not a continuity argument, is how the
    corollary reaches the top of its range, and it also gives `cor:strict` its
    strictness there, the subtracted term being exactly zero.  `cor:C-schur`
    states STRICT decrease on the whole of [0, s/2] when the weights are not all
    zero, so the drop from the last interior point to the endpoint is asserted
    strict; check_schur_concavity covers the interior comparisons.
    """
    f = {n: Fraction(n + 1) for n in range(1, deg + 1)}
    for n in range(2, deg):
        assert f[n] ** 2 >= f[n - 1] * f[n + 1], n
    supp = [n for n in f if f[n] > 0]
    for s in [Fraction(6), Fraction(15, 2)]:
        for m in range(2, deg + 1):
            # the weights of `eq:w-from-f` are not all zero exactly when m is in I+I
            has_pair = any(f.get(r, 0) and f.get(m - r, 0) for r in range(1, m))
            assert has_pair == (2 * supp[0] <= m <= 2 * supp[-1]), (m,)
            endpoint = C_coef(m, f, s, Fraction(0))
            assert endpoint == 0, (m, s)                          # v = 0 kills it
            interior = C_coef(m, f, s / 2 + s * Fraction(49, 100),
                              s / 2 - s * Fraction(49, 100))
            assert interior >= 0
            # the endpoint is reached by a STRICT drop, which is the closed-range
            # half of `cor:C-schur`; flat only where the weights all vanish
            if has_pair:
                assert endpoint < interior, (m, s, endpoint, interior)
            else:
                assert endpoint == interior == 0, (m, s, interior)
    print("PASS: `cor:C-schur` reaches d = s/2 with C_{m,f}(s,0) = 0, STRICTLY "
          "below every interior value where the weights are not all zero, and "
          "identically zero where they are")


def check_cor_strict_mu_zero(trials: int = 60, deg: int = 9,
                             seed: int = 20260730) -> None:
    """`cor:strict` at mu = 0, which is the endpoint d_2 = s/2.

    In the specialization s/2 - d_2 = mu, so mu = 0 is exactly the endpoint: the
    subtracted term C_{m,f}(s/2+d_2, s/2-d_2) = C_{m,f}(alpha+beta, 0) vanishes
    and the coefficient EQUALS C_{m,f}(alpha,beta), a sum of nonnegative terms
    with at least one strictly positive.  That identification is what is asserted
    here, alongside the strict classification at mu = 0.
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
    print("PASS: `cor:strict` at mu=0 -- the coefficient EQUALS C_{m,f}(alpha,beta), "
          "and is > 0 exactly when some f_k f_{m-k} > 0")


def check_hypothesis_and_ratio_monotonicity(deg: int = 10) -> None:
    """Two prose-level claims that reduce to computations.

    (i) `sec:introduction`'s stated hypothesis: (f_n) nonnegative, f_n^2 >= f_{n-1}f_{n+1}
        where the three terms are defined, and positive support an interval of
        integers.
    (ii) The first step of `cor:ordinary`'s proof, in section `sec:consequences`: log-concavity with
        no internal zeros makes f_{n+1}/f_n nonincreasing on the support, which is
        what gives R > 0 there.  This belongs to section `sec:consequences`, not to section `sec:introduction`,
        which states no radius claim.
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
        # (ii) f_{n+1}/f_n nonincreasing on the support, hence R > 0
        ratios = [f[n + 1] / f[n] for n in supp[:-1]]
        for a, b in zip(ratios, ratios[1:]):
            assert b <= a, ("ratio not nonincreasing", f)
        if ratios:
            # bounded ratios give a positive radius: limsup |f_n|^{1/n} < inf
            assert max(ratios) < Fraction(10 ** 9)
    print("PASS: `sec:introduction`'s hypothesis (nonnegative, interval support, "
          "log-concave), and `sec:consequences`'s f_{n+1}/f_n nonincreasing (hence R > 0)")


def check_internal_zeros_load_bearing() -> None:
    """`rem:internal-zeros`: the interval-support clause is necessary for the CONCLUSION.

    `sec:introduction` hypothesizes f_n^2 >= f_{n-1}f_{n+1} where defined AND positive
    support an interval of integers.  The second clause does not follow from the
    first: with f_1 = f_4 = 1 the two positive indices differ by 3, so the RIGHT
    side f_{n-1}f_{n+1} vanishes at every index (a nonzero product would need two
    positive indices exactly 2 apart) and the inequality holds throughout.  It is
    NOT an equality throughout -- at n = 4 it reads 1 >= 0 -- so the remark must
    not claim both sides vanish; the strict index is pinned below.  (A lone
    internal zero would fail: f_k = 0 with f_{k-1}, f_{k+1} > 0 gives
    0 >= f_{k-1}f_{k+1} > 0.)  On such a sequence the weights w_k = f_k f_{m-k}
    decrease toward the center, `eq:w-monotone` fails, and so does `thm:main`.  This
    crosses the boundary the other checks stay inside.
    """
    f = {1: Fraction(1), 4: Fraction(1)}                 # support {1,4}, zeros at 2,3

    # (i) the pointwise inequality holds at every index where it is defined, and
    #     the right side vanishes there -- which is WHY it holds.
    for n in range(2, 9):
        a, b, c = f.get(n - 1, Fraction(0)), f.get(n, Fraction(0)), f.get(n + 1, Fraction(0))
        assert a * c == 0, ("f_{n-1}f_{n+1} should vanish at every index", n)
        assert b * b >= a * c, ("pointwise log-concavity fails", n)
    # (i') it is strict exactly at n = 4.  `rem:internal-zeros`'s prose says "strictly at
    #      n = 4": f_4^2 = 1 while f_3 f_5 = 0, and both sides vanish elsewhere.
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

    # (iv) `eq:w-monotone` fails at m = 5: the weights decrease toward the center.
    m = 5
    w = [f.get(k, Fraction(0)) * f.get(m - k, Fraction(0)) for k in range(1, m)]
    assert w == [Fraction(1), Fraction(0), Fraction(0), Fraction(1)], w
    assert w[0] > w[1], "weights must decrease toward the center for this to bite"

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
    print("PASS: `rem:internal-zeros` -- interval support is load-bearing for `thm:main`, "
          "not just for its proof: f_1=f_4=1 gives [x^5] Turanian = -9360 at "
          "mu=2, a=b=1 (two routes agree), while f_n=1 gives > 0")


def check_extremal_log_concave(deg: int = 9) -> None:
    """The extremal side of the hypothesis: equality in log-concavity.

    Equality f_n^2 = f_{n-1} f_{n+1} means geometric (f_n), which gives CONSTANT
    weights w_k and so the degenerate side of `lem:weighting`.  That case and single-point
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
                    m, f, mu, mu + al + be), (name, m)       # `eq:delta-C`
                assert c >= 0, ("`thm:main`", name, m, c)
                has_pair = any(f.get(r, 0) and f.get(m - r, 0) for r in range(1, m))
                assert (c > 0) == has_pair, ("`cor:strict`", name, m, c, has_pair)
    print(f"PASS: `thm:main`, `eq:delta-C` and `cor:strict` on the extremal cases "
          f"({', '.join(cases)})")


# ===========================================================================
# section `sec:cubic-proof`: `cor:C-schur` (Schur-concavity of the convolution)
# ===========================================================================
def check_schur_concavity(trials: int = 300, seed: int = 20260722) -> None:
    rng = random.Random(seed)
    for _ in range(trials):
        lo = rng.randint(1, 2)
        hi = rng.randint(lo + 2, lo + 6)
        f = rand_logconcave(rng, lo, hi)
        s = Fraction(rng.randint(4, 14), rng.randint(1, 3))
        # the beta route of `prop:kernel-exact` covers 0 <= d < s/2, so draw strictly
        # inside it; the endpoint d = s/2, which `cor:C-schur` includes, is
        # reached by the identity C_{m,f}(s,0) = 0 in check_schur_boundary.
        ds = sorted(Fraction(rng.randint(0, 99), 100) * (s / 2) for _ in range(6))
        for m in range(2, 2 * hi):
            has_pair = any(f.get(r, 0) and f.get(m - r, 0) for r in range(1, m))
            vals = [C_coef(m, f, s / 2 + d, s / 2 - d) for d in ds]
            for (da, va), (db, vb) in zip(zip(ds, vals), zip(ds[1:], vals[1:])):
                assert va >= vb                                   # nonincreasing
                if has_pair and da < db:
                    assert va > vb                                # strict
    print("PASS: `cor:C-schur` (C_{m,f}(s/2+d,s/2-d) nonincreasing, strict)")


def check_cor_strict_support_descriptions(deg: int = 14) -> None:
    r"""`cor:strict`'s two descriptions of the positive degrees, as stated.

    The corollary says [x^m] S_f > 0 iff m is in I+I, and then reads that off in
    two shapes: I = {a,...,b} makes the positive degrees exactly 2a,...,2b, and
    I = {a,a+1,...} makes them exactly m >= 2a.  Both are asserted here against
    the coefficients themselves, at the file that states the corollary as its
    scope; `check_fixed_sum_schur.py` covers the same descriptions from the
    fixed-sum side.
    """
    finite = []
    for a in (1, 2, 4):
        for b in (a, a + 1, a + 3):
            finite.append((a, b, {n: Fraction(1) for n in range(a, b + 1)}))
    infinite = [(a, {n: Fraction(1, 2) ** n for n in range(a, deg + 3)}) for a in (1, 2, 5)]
    mu, al, be = Fraction(1, 2), Fraction(3, 2), Fraction(1)
    for a, b, f in finite:
        assert sorted(n for n in f if f[n] > 0) == list(range(a, b + 1))
        Fa, Fb = F_coeffs(f, mu + al, deg), F_coeffs(f, mu + be, deg)
        F0, Fs = F_coeffs(f, mu, deg), F_coeffs(f, mu + al + be, deg)
        pos = [m for m in range(2, deg + 1)
               if conv_coeff(Fa, Fb, m) - conv_coeff(F0, Fs, m) > 0]
        assert pos == [m for m in range(2 * a, 2 * b + 1) if m <= deg], (a, b, pos)
    for a, f in infinite:
        # a truncation of {a, a+1, ...}; the description is tested only up to a
        # degree the truncation cannot affect, namely m <= (top of support) + a
        top = max(n for n in f if f[n] > 0)
        Fa, Fb = F_coeffs(f, mu + al, deg), F_coeffs(f, mu + be, deg)
        F0, Fs = F_coeffs(f, mu, deg), F_coeffs(f, mu + al + be, deg)
        upto = min(deg, top + a)
        pos = [m for m in range(2, upto + 1)
               if conv_coeff(Fa, Fb, m) - conv_coeff(F0, Fs, m) > 0]
        assert pos == list(range(2 * a, upto + 1)), (a, pos)
    print(f"PASS: `cor:strict`'s descriptions -- I={{a..b}} gives exactly the "
          f"degrees 2a..2b ({len(finite)} supports) and I={{a,a+1,...}} exactly "
          f"m >= 2a ({len(infinite)} supports)")


# ===========================================================================
# `thm:main` and `cor:strict`
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
            assert c >= 0, (m, c)                                 # `thm:main`
            has_pair = any(f.get(r, 0) and f.get(m - r, 0) for r in range(1, m))
            if al > 0 and be > 0:
                assert (c > 0) == has_pair, (m, c, has_pair)      # `cor:strict`
    print("PASS: `thm:main` nonnegativity and `cor:strict` strict classification")


def check_mu_zero_boundary(trials: int = 80, deg: int = 10,
                           seed: int = 20260727) -> None:
    """`thm:main`'s boundary case mu = 0.

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
# `cor:ordinary` (Stirling ratio, radius, log-concavity in mu)
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
    """`cor:ordinary`'s radius claim for a NON-constant log-concave (f_n).

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
          "(`cor:ordinary`, general (f_n))")


def check_local_uniform_convergence_in_mu() -> None:
    """`cor:ordinary`'s local uniform convergence, on the paper's own range.

    The proof fixes M > 0 and works on 0 <= mu <= M -- the closed interval,
    endpoint mu = 0 included, where (mu)_{3n}/(3n-1)! vanishes identically --
    and dominates the coefficient factor by M e^M (3n)^M.  The majorant itself
    is asserted in `check_proof_steps.py`; what is added here is the consequence
    the corollary consumes and that file does not carry: the SUP over the whole
    of [0,M] of the series tail from N tends to 0, which is local uniform
    convergence rather than a pointwise statement.
    """
    for M in [mp.mpf(1), mp.mpf("2.5"), mp.mpf(4)]:
        mus = [M * mp.mpf(i) / 8 for i in range(9)]         # includes mu = 0
        assert mus[0] == 0 and mus[-1] == M
        assert coeff_ratio(mp.mpf(0), 5) == 0               # the endpoint is degenerate
        bound_c = M * mp.e ** M
        for n in [1, 2, 5, 20, 100, 500]:
            npow = mp.mpf(3 * n) ** M
            for mu in mus:
                assert coeff_ratio(mu, n) <= bound_c * npow, (M, mu, n)
        # for 0 < x < R = 1 (f_n = 1) the sup over [0,M] of the tail from N
        # decays, and the sup is attained away from the degenerate endpoint
        for xv in [mp.mpf("0.3"), mp.mpf("0.7")]:
            sup_tails = []
            for N in (40, 80, 160, 320):
                per_mu = [sum(coeff_ratio(mu, n) * xv ** n for n in range(N, N + 200))
                          for mu in mus]
                assert per_mu[0] == 0, (M, xv, N)           # mu = 0 contributes nothing
                sup_tails.append(max(per_mu))
            for hi, lo in zip(sup_tails, sup_tails[1:]):
                assert lo < hi, (M, xv, sup_tails)          # decreasing in N
            assert sup_tails[-1] < mp.mpf("1e-30"), (M, xv, sup_tails[-1])
    print("PASS: sup over the paper's own 0 <= mu <= M of the tail of F_f(mu;x) "
          "decays to zero under the majorant M e^M (3n)^M -- `cor:ordinary`'s "
          "local uniform convergence, endpoint mu = 0 included")


def check_continuity_in_mu() -> None:
    """mu -> F_f(mu;x) is finite, positive and CONTINUOUS on (0,inf).

    `cor:ordinary` needs continuity to upgrade midpoint concavity to concavity, and
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
    """`cor:ordinary`, in its strict form.

    `cor:ordinary` claims the STRICT four-point inequality and strict
    concavity, so the assertions below are strict inequalities with a margin
    rather than non-strict ones.  The
    strictness comes from `cor:strict`: the x^{2q} coefficient at the least
    supported index q is strictly positive while every other is nonnegative.
    Strict concavity then follows because a concave function with a strict
    midpoint inequality is affine on no subinterval.
    """
    worst = None
    for xv in [mp.mpf("0.2"), mp.mpf("0.5"), mp.mpf("0.8")]:
        # STRICT four-point inequality: F(mu+a)F(mu+b) > F(mu)F(mu+a+b)
        for mu in [mp.mpf("0.5"), mp.mpf("1.3"), mp.mpf("3")]:
            for al, be in [(mp.mpf("0.3"), mp.mpf("0.3")), (mp.mpf(1), mp.mpf(1)),
                           (mp.mpf("0.25"), mp.mpf(2))]:
                gap = (F_analytic(mu + al, xv) * F_analytic(mu + be, xv)
                       - F_analytic(mu, xv) * F_analytic(mu + al + be, xv))
                assert gap > mp.mpf("1e-25"), (xv, mu, al, be, gap)
        # STRICT concavity: the second difference of mu -> log F stays negative,
        # bounded away from 0, so no subinterval is affine
        mus = [mp.mpf(i) / 10 for i in range(3, 40)]
        logs = [mp.log(F_analytic(mu, xv)) for mu in mus]
        secs = [a - 2 * b + c for a, b, c in zip(logs, logs[1:], logs[2:])]
        assert max(secs) < -mp.mpf("1e-25"), (xv, max(secs))
        worst = max(secs) if worst is None else max(worst, max(secs))
    print("PASS: mu -> log F_f(mu;x) is STRICTLY midpoint-concave, hence strictly "
          f"concave (`cor:ordinary`; worst (least negative) second difference "
          f"{mp.nstr(worst, 6)}")


# ===========================================================================
# section `subsec:hypergeometric-specialization`: the f_n = 1 triplication identity
#   F_f(mu;x) = 3x d/dx 3F2(mu/3,(mu+1)/3,(mu+2)/3; 1/3,2/3; x)
# ===========================================================================
def check_triplication_3F2(deg: int = 12) -> None:
    """For f_n = 1 the Pochhammer triplication (mu)_{3n} = 3^{3n} (mu/3)_n
    ((mu+1)/3)_n ((mu+2)/3)_n together with (3n)! = 3^{3n} n! (1/3)_n (2/3)_n
    gives [x^n] F_f = (mu)_{3n}/(3n-1)! = 3n (mu/3)_n((mu+1)/3)_n((mu+2)/3)_n
    / (n! (1/3)_n (2/3)_n) = 3n [x^n] 3F2, i.e. F_f = 3x d/dx 3F2.  Both sides
    are compared exactly over Q: the left from the defining series (poch as in
    F_coeffs), the right from the 3F2 coefficient (a)_n(b)_n(c)_n/((d)_n(e)_n n!)
    scaled by the derivative factor 3n.  (Paper section `subsec:hypergeometric-specialization`.)"""
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
    check_hypothesis_and_ratio_monotonicity()
    check_internal_zeros_load_bearing()
    check_delta_C_and_imbalance()
    check_degenerate_shifts()
    check_schur_concavity()
    check_cor_strict_support_descriptions()
    check_schur_boundary()
    check_main_theorem()
    check_extremal_log_concave()
    check_mu_zero_boundary()
    check_cor_strict_mu_zero()
    check_triplication_3F2()
    check_stirling()
    check_radius_of_convergence()
    check_radius_matches_general_f()
    check_local_uniform_convergence_in_mu()
    check_continuity_in_mu()
    check_log_concavity_in_mu()
    print("ALL PASS: verify_theorem")


if __name__ == "__main__":
    main()
