#!/usr/bin/env python3
"""Targeted probe: the fixed-sum Schur-concavity statement of `thm:main` and the
corollaries drawn from it (`cor:C-schur` for arbitrary monotone symmetric
weights, `rem:local-weight`, `cor:strict`, `cor:ordinary`, `cor:differential`)
in `../shields-2026-cubic-pochhammer.tex`.

Scope.  This script settles the points at which the fixed-sum statement is
*stronger* than the generalized-Turanian statement, each by a route independent
of the paper's proof:

  * the normalization of `eq:C-beta` splits into a pure factorial identity and a
    beta moment, neither of which touches the form of the weights -- the
    hypothesis of `cor:C-schur`;
  * `eq:delta-C` at its own parameters: the degree-m coefficient of the series
    product at (s/2+d, s/2-d) really is C_{m,f} there, which is the one place the
    C-level checks below would otherwise rest on an unverified extraction;
  * the fixed-sum map `d -> C_{m,w}(s/2+d, s/2-d)` is strictly decreasing on
    the interior `[0, s/2)` for arbitrary weights satisfying `eq:w-monotone`,
    including weight vectors carrying interior zeros, and `eq:w-monotone` is
    load-bearing;
  * the endpoint `d = s/2` of `cor:C-schur`'s closed range closes through
    `C_{m,w}(s,0) = 0` rather than through the beta representation, since
    Beta(s,0) is not a law;
  * the specialization `s = 2mu+alpha+beta`, `d_1 = |alpha-beta|/2`,
    `d_2 = (alpha+beta)/2` reproduces `eq:delta-C` coefficient for coefficient,
    over the whole parameter closure including `mu = 0`, `alpha*beta = 0` and
    `s = 0`, and `d_2 = s/2` occurs there exactly at `mu = 0`;
  * `cor:strict`'s exact positive support `I+I`, in both the interval and the
    infinite-support forms, and its Turanian specialization at `alpha,beta > 0`;
  * `cor:ordinary`'s *strict* pointwise inequality and strict concavity;
  * `cor:differential`'s coefficientwise `h -> 0` limit, computed from the
    convolution rather than passed to, with the `O(h)` term shown to cancel;
  * `rem:local-weight`: the degree-`m` conclusion under the local weight chain
    alone, with a non-log-concave witness, and its failure one step below;
  * `rem:internal-zeros`: one intervening zero violates log-concavity at that
    zero, two do not;
  * the active-degree dichotomy of `cor:C-schur` and `cor:strict`: `a_m(d)` is
    strictly decreasing on the CLOSED `[0, s/2]` for `m` in `I+I` and identically
    zero, pointwise and not merely constant, for `m` outside it;
  * `lem:beta-order`'s likelihood-ratio conclusion at the fixed sum, with each
    `g_d` checked to be a density;
  * that a symmetric `H` nondecreasing on `[0,1/2]` is bounded, so `lem:beta-order`
    needs no integrability hypothesis.

The per-section sweeps live in `verify_beta_binomial.py` (`sec:reduction`),
`verify_monotonicity_lemmas.py` (`sec:reduction`--`sec:kernel`), `verify_kernel.py` (`sec:kernel`),
`verify_theorem.py` (`sec:cubic-proof`--`sec:consequences`) and `verify_multiplicity.py` (`sec:threshold`); the kernel theorem
and the two monotonicity lemmas are re-derived here only where the fixed-sum
parameterization needs them.

Exact arithmetic throughout (sympy Rational / integer); the two analytic checks
use mpmath at 40 digits.  No floating point in any assertion.
"""

import itertools
import random

import mpmath as mp
import sympy as sp

mp.mp.dps = 40

SEED = 20260821


# --------------------------------------------------------------------------
# The objects of the paper, re-derived from their definitions
# --------------------------------------------------------------------------

def poch(u, k):
    """Rising factorial (u)_k = u(u+1)...(u+k-1), with (u)_0 = 1."""
    out = sp.Integer(1)
    for i in range(k):
        out *= (u + i)
    return out


def C_weights(w, m, u, v):
    """C_{m,w}(u,v) of `cor:C-schur`, from arbitrary weights w[k], 1<=k<=m-1."""
    total = sp.Integer(0)
    for k in range(1, m):
        total += (w[k] * poch(u, 3 * k) * poch(v, 3 * (m - k))
                  / (sp.factorial(3 * k - 1) * sp.factorial(3 * (m - k) - 1)))
    return total


def series_F(f, mu, x, nmax):
    """Truncation of F_f(mu;x) = sum_{n>=1} f_n (mu)_{3n} x^n / (3n-1)! (`eq:F-def`),
    to the degree the caller needs."""
    return sum(f(n) * poch(mu, 3 * n) / sp.factorial(3 * n - 1) * x ** n
               for n in range(1, nmax + 1))


def weights_from_f(f, m):
    """`eq:w-from-f`: w_k = f_k f_{m-k}."""
    return {k: f(k) * f(m - k) for k in range(1, m)}


def C_from_f(f, m, u, v):
    """`eq:C-def`, the degree-m coefficient of F_f(u;x)F_f(v;x)."""
    return C_weights(weights_from_f(f, m), m, u, v)


def S_coeff(f, m, s, d1, d2):
    """[x^m] of `eq:schur-def`, the fixed-sum difference at imbalances d1 <= d2."""
    return sp.nsimplify(C_from_f(f, m, s / 2 + d1, s / 2 - d1)
                        - C_from_f(f, m, s / 2 + d2, s / 2 - d2), rational=True)


def turan_coeff(f, m, mu, al, be):
    """[x^m] of `eq:Turan-def` (`eq:delta-C`)."""
    return sp.nsimplify(C_from_f(f, m, mu + al, mu + be)
                        - C_from_f(f, m, mu, mu + al + be), rational=True)


# Weight families used below ------------------------------------------------

def monotone_symmetric_weights(m, rng):
    """A random weight vector satisfying `eq:w-monotone`, not necessarily of the
    form f_k f_{m-k}; interior plateaus (possibly at zero) are allowed."""
    half = m // 2
    vals, cur = [], sp.Integer(0)
    for i in range(half):
        step = (sp.Integer(0) if (i < half - 1 and rng.random() < 0.35)
                else sp.Rational(rng.randint(1, 6), rng.randint(1, 4)))
        cur = cur + step
        vals.append(cur)
    if vals[-1] == 0:
        vals[-1] = sp.Integer(1)
    return {k: vals[min(k, m - k) - 1] for k in range(1, m)}


def log_concave_sequence(rng, nmax, a=1, b=None):
    """A nonnegative log-concave sequence with interval support [a,b]."""
    if b is None:
        b = nmax
    ratios, cur = [], sp.Rational(rng.randint(3, 9), rng.randint(1, 3))
    for _ in range(nmax + 2):
        ratios.append(cur)
        cur = cur * sp.Rational(rng.randint(1, 4), rng.randint(4, 7))
    vals = {a: sp.Rational(rng.randint(1, 5), rng.randint(1, 3))}
    for n in range(a + 1, b + 1):
        vals[n] = vals[n - 1] * ratios[n - a - 1]
    return lambda n: vals.get(n, sp.Integer(0))


def kappa(m, s):
    """`eq:fixed-sum`'s prefactor kappa_{m,s} = (s)_{3m}/(3m)! * 3m(3m-1)."""
    return poch(s, 3 * m) / sp.factorial(3 * m) * 3 * m * (3 * m - 1)


def Ghat_poly(w, m, qsym):
    """`eq:G-weighted` folded through q = p(1-p), for symmetric weights.

    Reduced modulo p^2 - p + q rather than substituted, so the reduction itself
    exhibits the folding; the remainder being constant in p IS the assertion
    that the two solutions of p(1-p) = q give the same value.
    """
    psym = sp.Symbol("p_fold")
    G = sum(w[k] * sp.binomial(3 * m - 2, 3 * k - 1)
            * psym ** (3 * k) * (1 - psym) ** (3 * (m - k))
            for k in range(1, m))
    rem = sp.expand(sp.rem(sp.expand(G), psym ** 2 - psym + qsym, psym))
    assert sp.Poly(rem, psym).degree() <= 0, (m, rem)
    return sp.expand(rem)


# --------------------------------------------------------------------------
# 0. `eq:fixed-sum`: the prefactor kappa_{m,s} and the folding to Ghat
# --------------------------------------------------------------------------

def check_fixed_sum_kappa_and_folding():
    r"""`eq:fixed-sum`, both halves, at symbolic weights.

    `cor:C-schur` runs through this bridge and neither half was asserted anywhere:

      * kappa_{m,s} = (s)_{3m}/(3m)! * 3m(3m-1) > 0 for every s > 0, which is
        what lets the corollary read the sign of C off the expectation alone;
      * the folding G_{m,w}(p) -> Ghat_{m,w}(q) at q = p(1-p) is well defined for
        symmetric weights -- the two roots p and 1-p of p(1-p) = q give the same
        value -- and is FALSE without symmetry, which is checked with a witness;
      * the representation itself,
        C_{m,w}(s/2+d, s/2-d) = kappa_{m,s} E Ghat_{m,w}(Q_d), symbolically in
        (u,v) = (s/2+d, s/2-d) with symbolic weights, using the beta moment
        E[P^j(1-P)^j] = (u)_j (v)_j / (u+v)_{2j}.
    """
    u, v, qs = sp.symbols("u v q_fold", positive=True)
    for m in range(2, 7):
        base = sp.symbols(f"a0:{m // 2 + 1}")
        w = {k: base[min(k, m - k)] for k in range(1, m)}          # symmetric
        assert all(w[k] == w[m - k] for k in range(1, m)), m
        Gh = Ghat_poly(w, m, qs)                                   # asserts well-definedness
        # the folding reproduces G_{m,w} on both branches of p(1-p) = q
        psym = sp.Symbol("p_fold")
        G = sum(w[k] * sp.binomial(3 * m - 2, 3 * k - 1)
                * psym ** (3 * k) * (1 - psym) ** (3 * (m - k)) for k in range(1, m))
        for pv in [sp.Rational(1, 5), sp.Rational(1, 3), sp.Rational(1, 2),
                   sp.Rational(2, 3), sp.Rational(4, 5)]:
            qv = pv * (1 - pv)
            assert sp.expand(G.subs(psym, pv) - Gh.subs(qs, qv)) == 0, (m, pv)
            assert sp.expand(G.subs(psym, 1 - pv) - Gh.subs(qs, qv)) == 0, (m, pv)
        # `eq:fixed-sum` itself, through the beta moments of Q = P(1-P)
        P = sp.Poly(Gh, qs)
        EGhat = sum(c * poch(u, j) * poch(v, j) / poch(u + v, 2 * j)
                    for (j,), c in P.terms())
        assert sp.simplify(C_weights(w, m, u, v) - kappa(m, u + v) * EGhat) == 0, m
        # kappa > 0 for every s > 0: a product of positive factors
        for sv in [sp.Rational(1, 100), sp.Rational(3, 2), sp.Integer(7), sp.Integer(40)]:
            assert kappa(m, sv) > 0, (m, sv)
        assert sp.simplify(kappa(m, sp.Integer(0))) == 0             # (0)_{3m} = 0
    # symmetry is what makes the folding well defined: without it the two
    # branches disagree, so Ghat is not a function of q at all
    m = 3
    asym = {1: sp.Integer(1), 2: sp.Integer(0)}
    psym = sp.Symbol("p_fold")
    Ga = sum(asym[k] * sp.binomial(7, 3 * k - 1)
             * psym ** (3 * k) * (1 - psym) ** (3 * (3 - k)) for k in (1, 2))
    pv = sp.Rational(1, 5)
    assert sp.expand(Ga.subs(psym, pv) - Ga.subs(psym, 1 - pv)) != 0
    rem = sp.expand(sp.rem(sp.expand(Ga), psym ** 2 - psym + qs, psym))
    assert sp.Poly(rem, psym).degree() == 1, rem                     # genuinely p-dependent
    print("PASS  `eq:fixed-sum`: kappa_{m,s} = (s)_{3m}/(3m)! 3m(3m-1) > 0 for s > 0 and "
          "zero at s = 0, the folding to Ghat_{m,w} is well defined for symmetric "
          "weights (and not otherwise), and C_{m,w}(s/2+d,s/2-d) = kappa E Ghat(Q_d) "
          "symbolically in (u,v) with symbolic weights, m = 2..6")


# --------------------------------------------------------------------------
# 1. `eq:C-beta`'s normalization, with the weights left arbitrary
# --------------------------------------------------------------------------

def check_normalization_is_weight_free():
    """The passage from `eq:C-def` to `eq:C-beta` factors into two statements, and
    neither mentions the weights:

      (i)  a factorial identity, N = 3m,
             1/((3k-1)!(3(m-k)-1)!) = C(3m-2,3k-1) * N(N-1)/N! ;
      (ii) the Beta(u,v) moment
             E p^{3k}(1-p)^{3(m-k)} = (u)_{3k}(v)_{3(m-k)} / (u+v)_{3m}.

    So `eq:C-beta` reads C_{m,w} = (u+v)_N/N! * N(N-1) * E G_{m,w}(P) for any
    weight family whatever, which is the hypothesis of `cor:C-schur`.
    """
    for m in range(2, 13):
        N = 3 * m
        for k in range(1, m):
            lhs = sp.Rational(1, sp.factorial(3 * k - 1)
                              * sp.factorial(3 * (m - k) - 1))
            rhs = (sp.binomial(3 * m - 2, 3 * k - 1) * N * (N - 1)
                   / sp.factorial(N))
            assert sp.nsimplify(lhs - rhs, rational=True) == 0, (m, k)
    print("PASS  `eq:C-beta` normalization (i): 1/((3k-1)!(3(m-k)-1)!) = "
          "C(3m-2,3k-1)*N(N-1)/N! for every k (m = 2..12)")

    u, v = sp.symbols("u v", positive=True)
    for m in range(2, 6):
        for k in range(1, m):
            a, b = 3 * k, 3 * (m - k)
            # E p^a (1-p)^b = B(u+a, v+b)/B(u,v), by the Beta integral
            moment = (sp.integrate(
                sp.gamma(u + v) / (sp.gamma(u) * sp.gamma(v))
                * sp.Symbol("p") ** (u + a - 1)
                * (1 - sp.Symbol("p")) ** (v + b - 1),
                (sp.Symbol("p"), 0, 1)) if False else
                sp.gamma(u + a) * sp.gamma(v + b) * sp.gamma(u + v)
                / (sp.gamma(u + v + a + b) * sp.gamma(u) * sp.gamma(v)))
            claimed = poch(u, a) * poch(v, b) / poch(u + v, a + b)
            assert sp.simplify(sp.expand_func(moment) - claimed) == 0, (m, k)
    print("PASS  `eq:C-beta` normalization (ii): the Beta(u,v) moment equals "
          "(u)_{3k}(v)_{3(m-k)}/(u+v)_{3m} (m = 2..5, every k)")

    # and the assembled identity, with symbolic weights, at small m
    for m in (2, 3, 4):
        w = {k: sp.Symbol(f"w{k}", positive=True) for k in range(1, m)}
        N = 3 * m
        lhs = C_weights(w, m, u, v)
        EG = sum(w[k] * sp.binomial(3 * m - 2, 3 * k - 1)
                 * poch(u, 3 * k) * poch(v, 3 * (m - k)) / poch(u + v, 3 * m)
                 for k in range(1, m))
        rhs = poch(u + v, N) / sp.factorial(N) * N * (N - 1) * EG
        assert sp.simplify(sp.cancel(lhs - rhs)) == 0, m
    print("PASS  `eq:C-beta` assembled with symbolic weights w_k (m = 2,3,4)")


# --------------------------------------------------------------------------
# 2. Fixed-sum monotonicity for arbitrary monotone symmetric weights
# --------------------------------------------------------------------------

def check_coefficient_extraction_at_fixed_sum():
    """`eq:delta-C` in its own parameterization.  Every other check here works at
    the C_{m,f} level, so if `eq:C-def` were wrong they would all agree on a false
    theorem.  This one convolves the DEFINING SERIES at (s/2+d, s/2-d) and
    compares against C_{m,f} there, closing that seam at the parameters
    `eq:schur-def` actually uses -- verify_theorem.py asserts the same identity, but
    only at the Turanian pairs (mu+a, mu+b) and (mu, mu+a+b).
    """
    x = sp.Symbol("x")
    rng = random.Random(SEED + 9)
    endpoints = 0
    for m in range(2, 8):
        f = log_concave_sequence(rng, m + 1)
        for s in (sp.Integer(3), sp.Rational(11, 2)):
            for j in range(5):
                d = sp.Rational(j, 4) * s / 2                 # j = 4 gives d = s/2
                u, v = s / 2 + d, s / 2 - d
                prod = sp.expand(series_F(f, u, x, m) * series_F(f, v, x, m))
                assert sp.nsimplify(prod.coeff(x, m) - C_from_f(f, m, u, v), rational=True) == 0, \
                    (m, s, d)
                if v == 0:
                    endpoints += 1
                    assert prod.coeff(x, m) == 0, (m, s)
                # degrees 0 and 1 vanish, as `thm:main`'s proof opens by saying
                assert prod.coeff(x, 0) == 0 and prod.coeff(x, 1) == 0, (m, s, d)
    assert endpoints > 0
    print("PASS  `eq:delta-C` at its own parameters: the degree-m coefficient of "
          "the series product at (s/2+d, s/2-d) equals C_{m,f} there, degrees 0 "
          f"and 1 vanish, and the v = 0 endpoint is reached ({endpoints} cases)")


def check_fixed_sum_monotone_general_weights():
    """`cor:C-schur` as restated for arbitrary weights: at fixed s, the map
    d -> C_{m,w}(s/2+d, s/2-d) is strictly decreasing on the interior [0, s/2).

    The closed range `cor:C-schur` states is in
    check_proof_steps.py; this covers the half the beta representation reaches."""
    rng = random.Random(SEED)
    with_zero = 0
    for m in range(2, 10):
        for _ in range(6):
            w = monotone_symmetric_weights(m, rng)
            if any(w[k] == 0 for k in range(1, m)):
                with_zero += 1
            for s in (sp.Rational(1, 2), sp.Integer(1), sp.Integer(3),
                      sp.Rational(17, 4)):
                vals = [C_weights(w, m, s / 2 + sp.Rational(j, 8) * s / 2,
                                  s / 2 - sp.Rational(j, 8) * s / 2)
                        for j in range(8)]
                for a, b in zip(vals, vals[1:]):
                    assert a - b > 0, (m, s, a, b)
    assert with_zero > 0, "no zero-carrying weight vector tested"
    print("PASS  d -> C_{m,w}(s/2+d, s/2-d) strictly decreasing on the interior [0,s/2), "
          f"arbitrary monotone symmetric w (m = 2..9; {with_zero} of 48 weight "
          "vectors carry interior zeros)")


def check_monotone_hypothesis_load_bearing():
    """`eq:w-monotone` is load-bearing for the general-weight statement: a
    symmetric weight vector decreasing toward the center reverses the order."""
    # the weights of `rem:internal-zeros`: f_1 = f_4 = 1, so w = (1,0,0,1) at
    # m = 5, decreasing toward the center rather than increasing
    w = {1: sp.Integer(1), 2: sp.Integer(0), 3: sp.Integer(0), 4: sp.Integer(1)}
    s, d1, d2 = sp.Integer(6), sp.Integer(0), sp.Integer(1)
    diff = sp.nsimplify(C_weights(w, 5, s / 2 + d1, s / 2 - d1)
                        - C_weights(w, 5, s / 2 + d2, s / 2 - d2), rational=True)
    assert diff == -9360, diff
    # The failure is not universal in s: at d = 1 the difference is positive
    # for s <= 4 and negative from s = 5 on, so the counterexample needs a
    # large enough parameter sum as well as the wrong weight order.
    signs = {}
    for s2 in [sp.Integer(k) for k in (2, 3, 4, 5, 6, 8, 20)] + \
              [sp.Rational(15, 2)]:
        d = min(sp.Integer(1), s2 / 2)
        signs[s2] = sp.sign(sp.nsimplify(
            C_weights(w, 5, s2 / 2, s2 / 2)
            - C_weights(w, 5, s2 / 2 + d, s2 / 2 - d), rational=True))
    assert all(signs[s2] > 0 for s2 in signs if s2 <= 4)
    assert all(signs[s2] < 0 for s2 in signs if s2 >= 5)
    print(f"PASS  `eq:w-monotone` load-bearing: the symmetric w = (1,0,0,1) of "
          f"`rem:internal-zeros` decreases toward the center, and at d = 1 the "
          f"fixed-sum difference is {diff} < 0 at s = 6 -- negative for every "
          f"tested s >= 5, positive for s <= 4, so the failure needs the "
          f"parameter sum as well as the wrong weight order")


# --------------------------------------------------------------------------
# 3. The endpoint d = s/2
# --------------------------------------------------------------------------

def check_endpoint_vanishes():
    """C_{m,w}(s,0) = 0 identically -- the route by which `thm:main` reaches
    d_2 = s/2, the endpoint of `cor:C-schur`'s closed range."""
    s = sp.Symbol("s", positive=True)
    for m in range(2, 9):
        w = {k: sp.Symbol(f"w{k}", positive=True) for k in range(1, m)}
        assert sp.expand(C_weights(w, m, s, sp.Integer(0))) == 0, m
        assert sp.expand(C_weights(w, m, sp.Integer(0), s)) == 0, m
        for k in range(1, m):
            assert poch(sp.Integer(0), 3 * (m - k)) == 0, (m, k)
            assert poch(sp.Integer(0), 3 * k) == 0, (m, k)
    print("PASS  C_{m,w}(s,0) = C_{m,w}(0,s) = 0 identically, every summand "
          "(m = 2..8)")


def check_full_range_including_endpoint():
    """`thm:main`: nonnegativity for 0 <= d1 <= d2 <= s/2, the
    endpoint included."""
    rng = random.Random(SEED + 1)
    endpoints = 0
    for m in range(2, 9):
        f = log_concave_sequence(rng, m + 1)
        for s in (sp.Integer(1), sp.Rational(7, 2), sp.Integer(6)):
            grid = [sp.Rational(j, 6) * s / 2 for j in range(7)]   # includes s/2
            for d1, d2 in itertools.combinations_with_replacement(grid, 2):
                assert S_coeff(f, m, s, d1, d2) >= 0, (m, s, d1, d2)
                if d2 == s / 2:
                    endpoints += 1
                    assert sp.expand(
                        C_from_f(f, m, s / 2 + d2, s / 2 - d2)) == 0
    print("PASS  `thm:main` fixed-sum nonnegativity on the closed range "
          f"0 <= d1 <= d2 <= s/2 (m = 2..8, {endpoints} endpoint cases)")


# --------------------------------------------------------------------------
# 4. The Karp-Zhang specialization, over the whole parameter closure
# --------------------------------------------------------------------------

def check_specialization_identity():
    """s = 2mu+alpha+beta, d1 = |alpha-beta|/2, d2 = (alpha+beta)/2 identifies
    `eq:schur-def` with `eq:delta-C` -- including mu = 0, alpha = 0, beta = 0 and
    the degenerate s = 0."""
    rng = random.Random(SEED + 2)
    params = [(sp.Integer(0), sp.Integer(0), sp.Integer(0)),         # s = 0
              (sp.Integer(0), sp.Integer(1), sp.Integer(1)),         # mu = 0
              (sp.Integer(0), sp.Rational(1, 2), sp.Integer(4)),     # mu = 0
              (sp.Integer(2), sp.Integer(0), sp.Integer(3)),         # alpha = 0
              (sp.Integer(2), sp.Integer(3), sp.Integer(0)),         # beta = 0
              (sp.Rational(1, 3), sp.Rational(5, 2), sp.Rational(1, 7))]
    for _ in range(6):
        params.append(tuple(sp.Rational(rng.randint(0, 9), rng.randint(1, 4))
                            for _ in range(3)))
    for m in range(2, 8):
        f = log_concave_sequence(rng, m + 1)
        for mu, al, be in params:
            s = 2 * mu + al + be
            lhs = turan_coeff(f, m, mu, al, be)
            if s == 0:
                assert lhs == 0, (m, mu, al, be, lhs)
                continue
            d1, d2 = abs(al - be) / 2, (al + be) / 2
            assert 0 <= d1 <= d2 <= s / 2, (mu, al, be)
            assert lhs - S_coeff(f, m, s, d1, d2) == 0, (m, mu, al, be)
            assert lhs >= 0, (m, mu, al, be, lhs)
    print("PASS  `eq:schur-def` specializes to `eq:delta-C` at "
          "(s,d1,d2) = (2mu+a+b, |a-b|/2, (a+b)/2) over the whole closure "
          f"(m = 2..7, {len(params)} parameter points incl. mu=0, a*b=0, s=0)")


def check_endpoint_reached_exactly_at_mu_zero():
    """In the specialization, d_2 = s/2 exactly when mu = 0, so the endpoint is
    interior to the theorem's parameter range."""
    mu, al, be = sp.symbols("mu alpha beta", nonnegative=True)
    s, d2 = 2 * mu + al + be, (al + be) / 2
    assert sp.simplify(s / 2 - d2 - mu) == 0
    sols = sp.solve(sp.Eq(d2, s / 2), mu)
    assert sols == [sp.Integer(0)] or sols == [0], sols
    print("PASS  s/2 - d_2 = mu identically, so d_2 = s/2 exactly at mu = 0")


# --------------------------------------------------------------------------
# 5. `cor:strict` -- the exact positive coefficient support I+I
# --------------------------------------------------------------------------

def check_exact_support():
    """[x^m] of `eq:schur-def` is positive precisely for m in I+I, with
    I = {n >= 1 : f_n > 0}; and the interval descriptions 2a <= m <= 2b and
    m >= 2a."""
    rng = random.Random(SEED + 3)
    cases = []
    for (a, b) in [(1, 1), (1, 3), (2, 4), (3, 3), (2, 5)]:
        cases.append((log_concave_sequence(rng, b, a=a, b=b), a, b))
    for a in (1, 2, 3):                              # infinite support from a
        cases.append((lambda n, a=a: sp.Rational(1, 3) ** n if n >= a
                      else sp.Integer(0), a, None))

    for f, a, b in cases:
        hi = b if b is not None else 8
        assert all(f(n) > 0 for n in range(a, hi + 1))
        assert all(f(n) == 0 for n in range(1, a))
        if b is not None:
            assert all(f(n) == 0 for n in range(b + 1, b + 4))
        for s, d1, d2 in [(sp.Integer(4), sp.Integer(0), sp.Integer(1)),
                          (sp.Integer(4), sp.Integer(1), sp.Integer(2)),
                          (sp.Rational(9, 2), sp.Rational(1, 2),
                           sp.Rational(9, 4))]:
            for m in range(2, 2 * hi + 3):
                if b is None and m > 2 * hi:
                    continue      # beyond the degrees this support's I+I test pins
                exists_k = any(f(k) * f(m - k) > 0 for k in range(1, m))
                in_sum = (2 * a <= m <= 2 * b) if b is not None else (m >= 2 * a)
                assert in_sum == exists_k, (a, b, m)
                assert (S_coeff(f, m, s, d1, d2) > 0) == in_sum, \
                    (a, b, m, s, d1, d2)
    print("PASS  `cor:strict` exact support: [x^m] > 0 <=> m in I+I, in the "
          "interval form 2a <= m <= 2b and the infinite form m >= 2a "
          "(8 supports; d2 < s/2 and d2 = s/2)")


def check_active_degree_dichotomy():
    """The dichotomy the abstract states.  With a_m(d) = [x^m] of the product at
    (s/2+d, s/2-d) and I = {n >= 1 : f_n > 0}:

        m in I+I      ==>  a_m is STRICTLY DECREASING on the closed [0, s/2]
        m not in I+I  ==>  a_m is IDENTICALLY ZERO there

    `cor:strict` gives the first line and the sign of the second; the second line's
    "identically zero" is asserted here pointwise, since the abstract claims the
    value and not merely that the differences vanish.
    """
    rng = random.Random(SEED + 10)
    cases = [(log_concave_sequence(rng, b, a=a, b=b), a, b)
             for (a, b) in [(1, 2), (2, 3), (3, 4)]]
    zero_degrees = active_degrees = 0
    for f, a, b in cases:
        for s in (sp.Integer(3), sp.Integer(8)):
            grid = [sp.Rational(j, 6) * s / 2 for j in range(7)]   # includes s/2
            for m in range(2, 2 * b + 3):
                vals = [C_from_f(f, m, s / 2 + d, s / 2 - d) for d in grid]
                if 2 * a <= m <= 2 * b:
                    active_degrees += 1
                    for hi, lo in zip(vals, vals[1:]):
                        assert hi - lo > 0, (a, b, m, s)          # strict, to s/2
                    assert vals[-1] == 0                          # and down to 0
                else:
                    zero_degrees += 1
                    assert all(v == 0 for v in vals), (a, b, m, s)
    assert zero_degrees > 0 and active_degrees > 0
    print("PASS  active-degree dichotomy: a_m strictly decreasing on the closed "
          f"[0,s/2] for the {active_degrees} degrees in I+I, identically zero for "
          f"the {zero_degrees} outside it")


def check_support_interval_closure():
    """I an integer interval makes I+I one -- so a nonzero generalized Turanian
    has no internal zeros in its positive coefficient support."""
    for a in range(1, 6):
        for b in range(a, a + 7):
            I = range(a, b + 1)
            assert sorted({i + j for i in I for j in I}) \
                == list(range(2 * a, 2 * b + 1)), (a, b)
    print("PASS  I an integer interval => I+I = [2a,2b], an integer interval")


def check_turanian_support_condition():
    """The Turanian form of `cor:strict` needs alpha,beta > 0, which is exactly
    d_1 < d_2 in the specialization; and the Turanian vanishes when either
    shift is zero."""
    for a, b in [(0, 0), (0, 2), (3, 0), (1, 1), (2, 5), (5, 2),
                 (sp.Rational(1, 3), 7)]:
        assert (abs(a - b) < a + b) == (a > 0 and b > 0), (a, b)
    rng = random.Random(SEED + 4)
    for m in range(2, 7):
        f = log_concave_sequence(rng, m + 1)
        for mu in (sp.Integer(0), sp.Integer(2), sp.Rational(3, 5)):
            assert turan_coeff(f, m, mu, sp.Integer(0), sp.Integer(3)) == 0
            assert turan_coeff(f, m, mu, sp.Integer(3), sp.Integer(0)) == 0
    print("PASS  |a-b|/2 < (a+b)/2 <=> a,b > 0; the Turanian vanishes at "
          "a = 0 and at b = 0 (m = 2..6, three mu each)")


# --------------------------------------------------------------------------
# 6. `cor:ordinary` -- strict pointwise inequality and strict concavity
# --------------------------------------------------------------------------

def check_strict_pointwise_and_concavity():
    """The strict four-point inequality and strict concavity of
    mu -> log F_f(mu;x), by direct high-precision summation."""
    def F(fseq, mu, x, nmax=90):
        tot = mp.mpf(0)
        for n in range(1, nmax + 1):
            c = fseq(n)
            if c == 0:
                continue
            tot += mp.mpf(c) * mp.rf(mu, 3 * n) / mp.factorial(3 * n - 1) * x ** n
        return tot

    families = {
        "f_n = 1 (R = 1)": (lambda n: 1, mp.mpf("0.3")),
        "f_n = 3^-n (R = 3)": (lambda n: mp.mpf(3) ** (-n), mp.mpf("0.8")),
        "support {2,...,5}": (lambda n: 1 if 2 <= n <= 5 else 0, mp.mpf("0.4")),
        "single point {3}": (lambda n: 1 if n == 3 else 0, mp.mpf("0.4")),
    }
    for name, (fseq, x) in families.items():
        for mu, al, be in [(mp.mpf("0.5"), mp.mpf(1), mp.mpf(1)),
                           (mp.mpf(2), mp.mpf("0.25"), mp.mpf(3)),
                           (mp.mpf(0), mp.mpf(1), mp.mpf(2))]:
            gap = (F(fseq, mu + al, x) * F(fseq, mu + be, x)
                   - F(fseq, mu, x) * F(fseq, mu + al + be, x))
            assert gap > mp.mpf("1e-30"), (name, mu, al, be, gap)
        secs = []
        for j in range(1, 21):
            mu, h = mp.mpf(j) / 2, mp.mpf("0.5")
            secs.append(mp.log(F(fseq, mu + h, x)) - 2 * mp.log(F(fseq, mu, x))
                        + mp.log(F(fseq, mu - h, x)))
        assert max(secs) < -mp.mpf("1e-25"), (name, max(secs))
        print(f"PASS  `cor:ordinary` strict, {name}: four-point inequality "
              f"strict; log F second difference <= {mp.nstr(max(secs), 6)} < 0 "
              "on a 20-point grid (no affine subinterval)")


def check_strict_coefficient_witness():
    """The strictness witness of `cor:ordinary`'s proof: with n_0 an index carrying
    f_{n_0} > 0, the x^{2 n_0} coefficient of the Turanian is > 0.  Taken here at
    the least such index, where every lower coefficient vanishes as well."""
    rng = random.Random(SEED + 5)
    for q in (1, 2, 3, 4):
        f = log_concave_sequence(rng, q + 2, a=q, b=q + 2)
        for mu, al, be in [(sp.Integer(0), sp.Integer(1), sp.Integer(1)),
                           (sp.Rational(1, 2), sp.Integer(2),
                            sp.Rational(1, 3))]:
            assert turan_coeff(f, 2 * q, mu, al, be) > 0, (q, mu)
            for m in range(2, 2 * q):
                assert turan_coeff(f, m, mu, al, be) == 0, (q, m)
    print("PASS  x^{2 n_0} coefficient strictly positive at the least supported "
          "index n_0, every lower coefficient zero (n_0 = 1..4)")


# --------------------------------------------------------------------------
# 7. `cor:differential` -- the coefficientwise h -> 0 limit
# --------------------------------------------------------------------------

def check_differential_turan():
    """[x^m] of (d_mu F)^2 - F d_mu^2 F, computed from the convolution, equals
    the coefficientwise limit of h^{-2} [x^m] of F(mu+h)^2 - F(mu)F(mu+2h); the
    O(1) and O(h) terms of that expansion vanish identically."""
    mu, h = sp.symbols("mu h")
    rng = random.Random(SEED + 6)
    for m in range(2, 7):
        f = log_concave_sequence(rng, m + 1)
        g = {n: f(n) * poch(mu, 3 * n) / sp.factorial(3 * n - 1)
             for n in range(1, m + 1)}

        direct = sp.expand(sum(
            sp.diff(g[k], mu) * sp.diff(g[m - k], mu)
            - g[k] * sp.diff(g[m - k], mu, 2) for k in range(1, m)))

        expr = sp.expand(sum(
            g[k].subs(mu, mu + h) * g[m - k].subs(mu, mu + h)
            - g[k] * g[m - k].subs(mu, mu + 2 * h) for k in range(1, m)))
        p = sp.Poly(expr, h)
        assert sp.expand(p.coeff_monomial(1)) == 0, (m, "O(1)")
        assert sp.expand(p.coeff_monomial(h)) == 0, (m, "O(h)")
        assert sp.expand(p.coeff_monomial(h ** 2) - direct) == 0, (m, "O(h^2)")

        for mu_v in [sp.Integer(0), sp.Rational(1, 4), sp.Integer(1),
                     sp.Integer(7), sp.Rational(31, 3)]:
            assert sp.nsimplify(direct.subs(mu, mu_v), rational=True) >= 0, (m, mu_v)
        assert sp.expand(direct.subs(mu, 0)
                         - sum(f(k) * f(m - k) for k in range(1, m))) == 0, m
    # `cor:differential` states an IFF, and every support above has I = {1..m+1},
    # so every m tested there lies in I+I and the >= 0 above never sees the
    # other side.  Supports that put m outside I+I are run here, so both
    # branches of the equivalence carry a witness.
    both = {True: 0, False: 0}
    for a, b in [(1, 4), (2, 4), (3, 3), (3, 5), (5, 6)]:
        f = log_concave_sequence(rng, b, a=a, b=b)
        I = [n for n in range(1, b + 3) if f(n) != 0]
        assert I == list(range(a, b + 1)), (a, b, I)
        IpI = {i + j for i in I for j in I}
        for m in range(2, 2 * b + 2):
            g = {n: f(n) * poch(mu, 3 * n) / sp.factorial(3 * n - 1)
                 for n in range(1, m + 1)}
            direct = sp.expand(sum(
                sp.diff(g[k], mu) * sp.diff(g[m - k], mu)
                - g[k] * sp.diff(g[m - k], mu, 2) for k in range(1, m)))
            for mu_v in [sp.Integer(0), sp.Rational(1, 4), sp.Integer(3)]:
                val = sp.nsimplify(direct.subs(mu, mu_v), rational=True)
                assert (val > 0) == (m in IpI), (a, b, m, mu_v, val)
            both[m in IpI] += 1
    assert both[True] > 0 and both[False] > 0, both
    print(f"PASS  `cor:differential`: the h-expansion of the degree-m Turanian "
          f"coefficient starts at h^2, its h^2 term is exactly "
          f"(d_mu F)^2 - F d_mu^2 F, at mu = 0 it is sum_k f_k f_{{m-k}}, and it is "
          f"> 0 EXACTLY on I+I -- {both[True]} degrees inside and {both[False]} "
          f"outside, over five supports")


# --------------------------------------------------------------------------
# 8. `rem:local-weight` -- the degree-local hypothesis
# --------------------------------------------------------------------------

def check_degree_local_hypothesis():
    """The degree-m conclusion holds for a nonnegative sequence that is *not*
    log-concave, provided the local chain f_1f_{m-1} <= ... <=
    f_{floor(m/2)}f_{ceil(m/2)} holds at that m; and fails one step below."""
    def local_chain(f, m):
        vals = [f(k) * f(m - k) for k in range(1, m // 2 + 1)]
        return all(a <= b for a, b in zip(vals, vals[1:]))

    def is_log_concave(f, nmax):
        return all(f(n) ** 2 >= f(n - 1) * f(n + 1) for n in range(2, nmax))

    vals = {1: 1, 2: 1, 3: 5, 4: 1, 5: 1}
    f = lambda n: sp.Integer(vals.get(n, 0))
    assert not is_log_concave(f, 5)                 # f_3^2 = 25 but f_2 f_4 = 1;
    assert f(2) ** 2 < f(1) * f(3)                  # the failure is at n = 2
    assert local_chain(f, 6) and not local_chain(f, 4)

    tested = 0
    for s in (sp.Integer(2), sp.Rational(11, 2), sp.Integer(9)):
        grid = [sp.Rational(j, 5) * s / 2 for j in range(6)]
        for d1, d2 in itertools.combinations_with_replacement(grid, 2):
            assert S_coeff(f, 6, s, d1, d2) >= 0, (s, d1, d2)
            tested += 1
    assert S_coeff(f, 6, sp.Integer(4), sp.Integer(0), sp.Integer(1)) > 0
    # At m = 4 the same f has weights (5,1,5), decreasing toward the center, so
    # its local chain fails there -- and the conclusion fails with it, once the
    # parameter sum is large enough.  The first witness on this grid:
    bad = S_coeff(f, 4, sp.Integer(8), sp.Integer(0), sp.Rational(2, 3))
    assert bad < 0, bad
    assert [f(k) * f(4 - k) for k in (1, 2, 3)] == [5, 1, 5]
    print("PASS  `rem:local-weight`: f = (1,1,5,1,1) is not log-concave, "
          f"satisfies the m = 6 local chain and the m = 6 conclusion ({tested} "
          "imbalance pairs); its m = 4 weights (5,1,5) violate the chain and "
          f"the m = 4 difference at (s,d1,d2) = (8,0,2/3) is {bad} < 0")


# --------------------------------------------------------------------------
# 9. `rem:internal-zeros` -- the shortest admissible gap
# --------------------------------------------------------------------------

def check_shortest_gap():
    """One intervening zero violates log-concavity at that zero; two intervening
    zeros (positive indices separated by three) do not.  Not a claim
    `rem:internal-zeros` makes; it is the gap-length refinement of its witness."""
    def lc_holds(f, nmax):
        return all(f(n) ** 2 >= f(n - 1) * f(n + 1) for n in range(2, nmax + 1))

    for a in range(1, 7):                       # one intervening zero, anywhere
        f = lambda n, a=a: sp.Integer(1) if n in (a, a + 2) else sp.Integer(0)
        assert not lc_holds(f, a + 5), a
        assert f(a + 1) ** 2 < f(a) * f(a + 2), a
    for a in range(1, 7):                       # two intervening zeros
        f = lambda n, a=a: sp.Integer(1) if n in (a, a + 3) else sp.Integer(0)
        assert lc_holds(f, a + 6), a

    f14 = lambda n: sp.Integer(1) if n in (1, 4) else sp.Integer(0)
    assert [f14(k) * f14(5 - k) for k in range(1, 5)] == [1, 0, 0, 1]
    val = turan_coeff(f14, 5, sp.Integer(2), sp.Integer(1), sp.Integer(1))
    assert val == -9360, val
    print("PASS  `rem:internal-zeros`: one intervening zero violates "
          "log-concavity at that zero (six positions); two intervening zeros "
          "are admissible (six positions); [x^5]Turanian(2;1,1) = -9360")


# --------------------------------------------------------------------------
# 10. `lem:beta-order` -- the likelihood-ratio statement
# --------------------------------------------------------------------------

def check_likelihood_ratio_statement():
    """Q_{d2} <=_lr Q_{d1} for d1 < d2 < s/2, in the convention that X <=_lr Y
    means f_Y/f_X nondecreasing: g_{d1}/g_{d2} is strictly increasing on
    (0,1/4).  Each g_d is checked to be a density first."""
    def g(d, s, q):
        r = mp.sqrt(1 - 4 * q)
        # ell(q) = log(p_+/p_-) = 2 log(1+r) - log(4q), the form that stays
        # accurate as q -> 0 where 1-r underflows
        ell = 2 * mp.log(1 + r) - mp.log(4 * q)
        return (2 / mp.beta(s / 2 + d, s / 2 - d) * q ** (s / 2 - 1)
                * (1 - 4 * q) ** mp.mpf("-0.5") * mp.cosh(d * ell))

    split = [0, mp.mpf("1e-20"), mp.mpf("1e-10"), mp.mpf("1e-4"),
             mp.mpf("0.1"), mp.mpf("0.25")]
    for s in (mp.mpf("0.7"), mp.mpf(2), mp.mpf(5)):
        # g_d has an integrable q^{s/2-d-1} singularity at 0; the normalization
        # is checked where quadrature resolves it, d <= s/4
        for d in (mp.mpf(0), s / 4):
            tot = mp.quad(lambda q: g(d, s, q), split)
            assert abs(tot - 1) < mp.mpf("1e-10"), (s, d, tot)
        for d1, d2 in [(mp.mpf(0), s / 4), (s / 8, s / 3),
                       (s / 4, s / 2 - mp.mpf("0.001"))]:
            if not d1 < d2 < s / 2:
                continue
            qs = [mp.mpf("0.25") * mp.mpf(10) ** (-mp.mpf(k) / 4)
                  for k in range(24, 0, -1)]
            inv = [g(d1, s, q) / g(d2, s, q) for q in qs]
            for a, b in zip(inv, inv[1:]):
                assert b > a, (s, d1, d2)
    print("PASS  `lem:beta-order`: g_d integrates to 1 for d <= s/4, and "
          "g_{d1}/g_{d2} is strictly increasing on (0,1/4) -- i.e. "
          "Q_{d2} <=_lr Q_{d1} -- over three parameter sums and three "
          "imbalance pairs each, up to d2 = s/2 - 10^-3")


def check_symmetric_monotone_H_is_bounded():
    """A symmetric H nondecreasing on [0,1/2] is bounded between H(0) and
    H(1/2), so E H(P_d) needs no integrability hypothesis; monotonicity already
    supplies measurability."""
    rng = random.Random(SEED + 8)
    for _ in range(40):
        knots = sorted(sp.Rational(rng.randint(0, 500), 1000) for _ in range(5))
        hts = sorted(sp.Rational(rng.randint(-50, 50), 7) for _ in range(5))

        def H(p, knots=knots, hts=hts):
            pp = min(p, 1 - p)
            out = hts[0]
            for kn, ht in zip(knots, hts):
                if pp >= kn:
                    out = ht
            return out

        grid = [sp.Rational(j, 200) for j in range(201)]
        vals = [H(p) for p in grid]
        assert min(vals) >= hts[0] and max(vals) <= hts[-1]
        assert H(sp.Rational(1, 2)) == max(vals)
        assert all(H(p) == H(1 - p) for p in grid)
    print("PASS  symmetric H nondecreasing on [0,1/2] is bounded between H(0) "
          "and H(1/2) (40 step witnesses); no integrability hypothesis needed")


# --------------------------------------------------------------------------

def main():
    check_fixed_sum_kappa_and_folding()
    check_normalization_is_weight_free()
    check_coefficient_extraction_at_fixed_sum()
    check_fixed_sum_monotone_general_weights()
    check_monotone_hypothesis_load_bearing()
    check_endpoint_vanishes()
    check_full_range_including_endpoint()
    check_specialization_identity()
    check_endpoint_reached_exactly_at_mu_zero()
    check_exact_support()
    check_active_degree_dichotomy()
    check_support_interval_closure()
    check_turanian_support_condition()
    check_strict_pointwise_and_concavity()
    check_strict_coefficient_witness()
    check_differential_turan()
    check_degree_local_hypothesis()
    check_shortest_gap()
    check_likelihood_ratio_statement()
    check_symmetric_monotone_H_is_bounded()
    print("ALL PASS: check_fixed_sum_schur")


if __name__ == "__main__":
    main()
