#!/usr/bin/env python3
r"""Paper section `sec:reduction` (Exact reduction to a residue kernel) and section `sec:kernel` (The
cubic residue kernel): the two monotonicity lemmas.

The two lemmas sit in different sections, each beside the argument that consumes
it: `lem:weighting` (monotone-weight duality) opens the weighted-kernel subsection of
section `sec:kernel`, and `lem:beta-order` (fixed-sum likelihood-ratio order) sits with the
beta-binomial representation in section `sec:reduction`.

`lem:weighting` (Abel weighting and its dual cone).  With T_sigma = sum_{k>=sigma} A_k
and 0 <= w_1 <= ... <= w_L, w_0 = 0:

  * the summation-by-parts identity `eq:abel-weight`,
    sum_k w_k A_k = sum_sigma (w_sigma - w_{sigma-1}) T_sigma, symbolically;
  * the cone equivalence in BOTH directions -- sum_k w_k A_k >= 0 for every such
    w if and only if every T_sigma >= 0 -- the reverse direction carried by the
    step weight 1_{k >= sigma}, which is what recovers an individual tail;
  * the strict cone clause: all T_sigma > 0 forces sum_k w_k A_k > 0 for every
    nonzero such w;
  * the one-sign-change corollary: at most one sign change, nonpositive then
    nonnegative, with sum_k A_k >= 0, gives every T_sigma >= 0; and with
    sum_k A_k > 0 and A_L > 0, every T_sigma > 0.

Each hypothesis is given a negative control: two sign changes, a single change in
the wrong direction, and weights that are not nondecreasing all break the
conclusion, and each of the strict clause's three added hypotheses admits an
admissible pair with weighted sum zero when dropped.  This file owns the lemma
as stated; the exhaustive enumeration of the dual cone at small L, with the
central-window indicator as the failing witness, is in `check_structural.py`.

`lem:beta-order` (symmetric beta imbalance ordering).  For P_d ~ Beta(s/2+d, s/2-d)
and Q_d = P_d(1-P_d) in (0,1/4), with p_pm(q) = (1 +- sqrt(1-4q))/2 and
ell(q) = log(p_+/p_-):

  * the density of Q_d is  g_d(q) = 2/B(s/2+d,s/2-d) q^{s/2-1}(1-4q)^{-1/2}
    cosh(d ell(q))  (checked by unit mass and by matching E phi(Q_d));
  * ell is strictly decreasing on (0,1/4);
  * for d_2 > d_1, cosh(d_2 ell)/cosh(d_1 ell) is strictly increasing in ell,
    because d -> d tanh(d ell) is strictly increasing;
  * hence g_{d_2}/g_{d_1} is strictly decreasing in q, so g_{d_1}-g_{d_2} has a
    single sign change (negative near 0, positive near 1/4): the LR order;
  * the proof's integrand (phi(q) - phi(q*))(g_{d_1}(q) - g_{d_2}(q)) is
    nonnegative THROUGHOUT (0,1/4), not merely in the integral, where q* is the
    crossing point;
  * therefore E H(P_{d_1}) >= E H(P_{d_2}), `eq:beta-order`, for every symmetric H
    nondecreasing on [0,1/2], strictly when H is strictly increasing.

Two of `lem:beta-order`'s hypotheses on H are given negative controls as well:
H(p) = p is nondecreasing but not symmetric and reverses `eq:beta-order`, and
H(p) = max(p,1-p) is symmetric but decreasing on [0,1/2] and reverses it too.

The crossing of g_{d_1} - g_{d_2} can sit at q ~ 1e-5 (it does at s = 0.6,
d_1 = 0.05, d_2 = 0.28, because g_d(q) ~ q^{s/2-1-d}/B near 0), so the
single-crossing sweep uses a log-refined grid reaching that scale.

The weighting `lem:weighting` uses exact rational arithmetic (fractions); the beta
imbalance ordering `eq:C-beta-binomial` uses mpmath at arbitrary precision.
"""
from __future__ import annotations

import random
from fractions import Fraction

import mpmath as mp
import sympy as sp

mp.mp.dps = 40


# ===========================================================================
# `lem:weighting`  One-sign-change weighting
# ===========================================================================
def _rand_frac(rng: random.Random, hi: int, den: int = 10 ** 6) -> Fraction:
    """A uniform rational in [0, hi), exact (no float)."""
    return Fraction(rng.randint(0, den - 1), den) * hi


def tails(A):
    """T_sigma = sum_{k >= sigma} A_k, sigma = 1..L, as a 0-indexed list."""
    out = []
    run = Fraction(0)
    for a in reversed(A):
        run += a
        out.append(run)
    out.reverse()
    return out


def check_abel_identity(trials: int = 400, seed: int = 20260801) -> None:
    """`eq:abel-weight`: sum_k w_k A_k = sum_sigma (w_sigma - w_{sigma-1}) T_sigma.

    An identity in (w, A) with no hypothesis on either, so it is checked
    symbolically per L rather than on admissible draws, and then on random exact
    rationals that include decreasing and negative weights -- data `eq:abel-weight`
    covers and the cone statements below do not.
    """
    for L in range(1, 9):
        wsym = sp.symbols(f"w1:{L + 1}")
        Asym = sp.symbols(f"A1:{L + 1}")
        T = [sum(Asym[k] for k in range(sig, L)) for sig in range(L)]
        lhs = sum(wsym[k] * Asym[k] for k in range(L))
        rhs = sum((wsym[sig] - (wsym[sig - 1] if sig else 0)) * T[sig]
                  for sig in range(L))
        assert sp.expand(lhs - rhs) == 0, L
    rng = random.Random(seed)
    for _ in range(trials):
        L = rng.randint(1, 10)
        w = [_rand_frac(rng, 4) - 2 for _ in range(L)]        # no ordering, no sign
        A = [_rand_frac(rng, 6) - 3 for _ in range(L)]
        T = tails(A)
        rhs = sum((w[sig] - (w[sig - 1] if sig else Fraction(0))) * T[sig]
                  for sig in range(L))
        assert sum(wi * ai for wi, ai in zip(w, A)) == rhs, (w, A)
    print(f"PASS: `eq:abel-weight` symbolically for L = 1..8 and on {trials} unrestricted "
          f"rational draws (`lem:weighting`)")


def check_cone_equivalence(trials: int = 2000, seed: int = 20260802) -> None:
    """Both directions of `lem:weighting`'s cone equivalence, and its strict clause.

    Forward: every T_sigma >= 0 makes sum_k w_k A_k >= 0, because `eq:abel-weight`
    expresses it as a nonnegative combination of the tails.  Reverse: the step
    weight w_k = 1_{k >= sigma} is itself admissible and evaluates to T_sigma
    exactly, so nonnegativity against every admissible w forces every tail
    nonnegative -- and a sequence with one negative tail is exhibited being
    broken by that weight.  Strict: all T_sigma > 0 forces sum_k w_k A_k > 0 for
    every NONZERO admissible w (the all-zero w gives 0, which is why "nonzero"
    is in the statement).
    """
    rng = random.Random(seed)
    pos_tails = neg_tails = strict = zero_w = 0
    for _ in range(trials):
        L = rng.randint(1, 10)
        A = [_rand_frac(rng, 6) - 3 for _ in range(L)]
        T = tails(A)
        if rng.randrange(6) == 0:
            w = [Fraction(0)] * L          # admissible, and the excluded case
        else:
            w = []
            cur = Fraction(0)
            for _k in range(L):
                cur += _rand_frac(rng, 2)
                w.append(cur)
        wsum = sum(wi * ai for wi, ai in zip(w, A))
        if all(x >= 0 for x in T):
            pos_tails += 1
            assert wsum >= 0, (w, A, T)
            if all(x > 0 for x in T):
                if any(x > 0 for x in w):
                    assert wsum > 0, ("strict cone clause", w, A, T)
                    strict += 1
                else:
                    # every tail positive but w = 0: the sum is 0, which is why
                    # the strict clause says "for every NONZERO such w"
                    assert wsum == 0, (w, A, T)
                    zero_w += 1
        else:
            neg_tails += 1
            # the reverse direction: the step weight at a negative tail is
            # admissible and detects it, so the cone condition really is dual
            sig = min(i for i, x in enumerate(T) if x < 0)
            step = [Fraction(0)] * sig + [Fraction(1)] * (L - sig)
            assert all(step[i] <= step[i + 1] for i in range(L - 1))
            assert sum(si * ai for si, ai in zip(step, A)) == T[sig] < 0
    assert pos_tails > 0 and neg_tails > 0 and strict > 0 and zero_w > 0, \
        (pos_tails, neg_tails, strict, zero_w)
    print(f"PASS: `lem:weighting`'s cone equivalence both ways and its strict clause "
          f"({pos_tails} draws with all tails >= 0 of which {strict} strict and "
          f"{zero_w} with the excluded zero weight, {neg_tails} with a negative "
          f"tail, each detected by its own step weight)")


def check_one_sign_change_gives_positive_tails(trials: int = 3000,
                                               seed: int = 20260803) -> None:
    """`lem:weighting`'s corollary: one sign change makes every tail nonnegative, strictly.

    At most one change from nonpositive to nonnegative with sum_k A_k >= 0 gives
    T_sigma >= 0 for every sigma; with sum_k A_k > 0 and A_L > 0 it gives
    T_sigma > 0.  This is the half `thm:kernel` consumes, and it is what makes the
    central-window tails of `verify_kernel.py` positive.
    """
    # the two boundary shapes the random draws essentially never produce, where
    # the corollary is nonstrict and the strict clause's hypotheses fail
    flat = [Fraction(-2), Fraction(-1), Fraction(3)]              # sum = 0
    assert sum(flat) == 0 and tails(flat)[0] == 0
    assert all(x >= 0 for x in tails(flat)) and not all(x > 0 for x in tails(flat))
    ends = [Fraction(-1), Fraction(3), Fraction(0)]               # A_L = 0
    assert sum(ends) > 0 and ends[-1] == 0
    assert all(x >= 0 for x in tails(ends)) and tails(ends)[-1] == 0
    rng = random.Random(seed)
    strict = 0
    for _ in range(trials):
        L = rng.randint(1, 12)
        q = rng.randint(0, L)                          # last nonpositive index
        A = ([-_rand_frac(rng, 3) for _ in range(q)]
             + [_rand_frac(rng, 3) for _ in range(L - q)])
        if sum(A) < 0:
            A[-1] += -sum(A) + _rand_frac(rng, 1)
        assert sum(A) >= 0
        T = tails(A)
        assert all(x >= 0 for x in T), (A, T)
        if sum(A) > 0 and A[-1] > 0:
            assert all(x > 0 for x in T), ("strict corollary", A, T)
            strict += 1
    assert strict > trials // 4, strict
    print(f"PASS: one sign change with sum >= 0 makes every tail >= 0, and > 0 "
          f"when the total is positive and A_L > 0 ({strict}/{trials} strict draws)")


def check_weighting(trials: int = 5000, seed: int = 20260721) -> None:
    rng = random.Random(seed)
    strict_cases = 0
    for _ in range(trials):
        L = rng.randint(1, 12)
        # nondecreasing nonnegative weights (exact rationals)
        w = []
        cur = Fraction(0)
        for _k in range(L):
            cur += _rand_frac(rng, 2)
            w.append(cur)
        # A with a single sign change from nonpositive to nonnegative
        q = rng.randint(0, L)                         # last nonpositive index
        A = [-_rand_frac(rng, 3) for _ in range(q)] + [_rand_frac(rng, 3) for _ in range(L - q)]
        # force sum >= 0 by padding the positive tail
        if sum(A) < 0:
            A[-1] += -sum(A) + _rand_frac(rng, 1)
        assert sum(A) >= 0                            # exact, no tolerance
        wsum = sum(wi * ai for wi, ai in zip(w, A))
        assert wsum >= 0, (w, A, wsum)
        # and it is `eq:abel-weight` that delivers it: the same value written as a
        # nonnegative combination of the tails, each of which is >= 0 here
        T = tails(A)
        assert all(x >= 0 for x in T), (A, T)
        assert wsum == sum((w[sig] - (w[sig - 1] if sig else Fraction(0))) * T[sig]
                           for sig in range(L)), (w, A)
        # the strict clause, on every draw that satisfies its three hypotheses
        if sum(A) > 0 and w[-1] > 0 and A[-1] > 0:
            assert wsum > 0, ("strict clause fails", w, A, wsum)
            strict_cases += 1
    assert strict_cases > trials // 4, strict_cases
    print(f"PASS: one-sign-change weighting through `eq:abel-weight`, and the strict "
          f"clause ({strict_cases}/{trials} draws reach it) (`lem:weighting`)")


def check_weighting_strict_hypotheses_load_bearing() -> None:
    """Each of the strict clause's three added hypotheses is load-bearing.

    The strict clause reads: if additionally sum A_k > 0, w_L > 0 and A_L > 0,
    then sum w_k A_k > 0.  Dropping any one of the three admits an admissible
    (w, A) with sum w_k A_k = 0, so none is ornamental.  These are exactly the
    three inputs the strict half of `thm:kernel` supplies (sum_k B_{m,k} = J_m > 0
    by `lem:bernstein`; w_L > 0 from "not all zero" with `eq:w-monotone`; B_{m,L} > 0 by
    `lem:block-sign`, so the clause is what carries strictness into `cor:strict`.
    """
    # drop sum A_k > 0  (keep w_L > 0, A_L > 0): sum A_k = 0 gives equality
    w = [Fraction(1), Fraction(1)]
    A = [Fraction(-1), Fraction(1)]
    assert sum(A) == 0 and w[-1] > 0 and A[-1] > 0
    assert sum(wi * ai for wi, ai in zip(w, A)) == 0

    # drop w_L > 0  (keep sum A_k > 0, A_L > 0): all-zero weights give equality
    w = [Fraction(0), Fraction(0)]
    A = [Fraction(-1), Fraction(2)]
    assert sum(A) > 0 and w[-1] == 0 and A[-1] > 0
    assert sum(wi * ai for wi, ai in zip(w, A)) == 0

    # drop A_L > 0  (keep sum A_k > 0, w_L > 0): a zero final term, with the
    # positive mass sitting where the weight vanishes
    w = [Fraction(0), Fraction(3)]
    A = [Fraction(1), Fraction(0)]
    assert sum(A) > 0 and w[-1] > 0 and A[-1] == 0
    assert sum(wi * ai for wi, ai in zip(w, A)) == 0
    print("PASS: each of the strict clause's three hypotheses is load-bearing")


def check_weighting_needs_nondecreasing_nonnegative_weights() -> None:
    """`lem:weighting`'s hypothesis on w is load-bearing in both of its halves.

    `eq:abel-weight` is an identity and holds for any w at all; what the cone
    statement needs is that every increment w_sigma - w_{sigma-1} be
    nonnegative, which is exactly 0 <= w_1 <= ... <= w_L.  Two controls:

      * DECREASING weights.  w = (5,1), A = (-1, 11/10): sum A = 1/10 > 0 and
        both tails are positive, yet sum w_k A_k = -39/10 < 0.  The increment
        w_2 - w_1 = -4 is what breaks it, and `eq:abel-weight` still holds.
      * a NEGATIVE weight.  w = (-1, 1) is nondecreasing but not nonnegative;
        with A = (2, 0) the increments are 1 and 2 while w_0 = 0 is not below
        w_1, and the weighted sum is -2 < 0 against a positive total.
    """
    w = [Fraction(5), Fraction(1)]
    A = [Fraction(-1), Fraction(11, 10)]
    T = tails(A)
    assert sum(A) == Fraction(1, 10) > 0 and all(x > 0 for x in T), T
    assert all(x >= 0 for x in w) and w[0] > w[1]            # nonnegative, DEcreasing
    wsum = sum(wi * ai for wi, ai in zip(w, A))
    assert wsum == Fraction(-39, 10) < 0, wsum
    # `eq:abel-weight` is untouched by the ordering; it is the increment that goes negative
    inc = [w[0] - Fraction(0), w[1] - w[0]]
    assert wsum == sum(i * t for i, t in zip(inc, T)) and inc[1] < 0, (inc, T)
    # and the same A with the weights put back in order gives a positive sum
    w_ok = [Fraction(1), Fraction(5)]
    assert sum(wi * ai for wi, ai in zip(w_ok, A)) == Fraction(9, 2) > 0

    w = [Fraction(-1), Fraction(1)]
    A = [Fraction(2), Fraction(0)]
    T = tails(A)
    assert all(w[i] <= w[i + 1] for i in range(len(w) - 1))  # nondecreasing
    assert w[0] < 0 and all(x >= 0 for x in T) and sum(A) > 0
    assert sum(wi * ai for wi, ai in zip(w, A)) == Fraction(-2) < 0
    print("PASS: `lem:weighting` needs its weights nondecreasing AND nonnegative -- "
          "w=(5,1) gives -39/10 and w=(-1,1) gives -2, both against positive tails")


def check_weighting_needs_one_sign_change() -> None:
    """Two sign changes can break the conclusion: the hypothesis is load-bearing."""
    w = [Fraction(0), Fraction(1), Fraction(5)]          # nondecreasing, nonnegative
    A = [Fraction(1), Fraction(-1), Fraction(1, 10)]     # sum = 1/10 >= 0, TWO sign changes
    assert sum(A) >= 0
    assert sum(wi * ai for wi, ai in zip(w, A)) < 0      # weighted sum = -1/2 < 0
    print("PASS: two sign changes break the conclusion (hypothesis is sharp)")


def check_weighting_direction_is_a_hypothesis() -> None:
    """The DIRECTION of the single sign change is a hypothesis, not a consequence.

    A single change running nonnegative -> nonpositive satisfies every other
    hypothesis of `lem:weighting` and breaks the conclusion.  The proof consumes the
    stated direction at "let k_0 be the largest index for which A_{k_0} < 0 ...
    for k <= k_0 we have w_k <= c and A_k <= 0".
    """
    w = [Fraction(1), Fraction(10)]                      # nondecreasing, nonnegative
    A = [Fraction(3), Fraction(-1)]                      # ONE change, wrong direction
    changes = sum(1 for a, b in zip(A, A[1:]) if (a < 0) != (b < 0))
    assert changes == 1 and A[0] > 0 > A[-1]
    assert sum(A) > 0                                    # sum = 2 > 0
    assert sum(wi * ai for wi, ai in zip(w, A)) < 0      # weighted sum = -7 < 0
    print("PASS: the sign-change DIRECTION is load-bearing, not automatic")


# ===========================================================================
# `lem:beta-order`  Symmetric beta imbalance ordering
# ===========================================================================
def beta_pdf(alpha, beta_, p):
    return p ** (alpha - 1) * (1 - p) ** (beta_ - 1) / mp.beta(alpha, beta_)


def E_H_beta(H, s, d):
    """E H(P_d), P_d ~ Beta(s/2+d, s/2-d), by quadrature."""
    alpha, beta_ = s / 2 + d, s / 2 - d
    return mp.quad(lambda p: H(p) * beta_pdf(alpha, beta_, p), [0, mp.mpf("0.5"), 1])


def ell(q):
    root = mp.sqrt(1 - 4 * q)
    p_plus = (1 + root) / 2
    p_minus = (1 - root) / 2
    return mp.log(p_plus / p_minus)


def g_density(s, d, q):
    """Closed-form density of Q_d = P_d(1-P_d), q in (0,1/4)."""
    alpha, beta_ = s / 2 + d, s / 2 - d
    return (
        2 / mp.beta(alpha, beta_)
        * q ** (s / 2 - 1)
        * (1 - 4 * q) ** mp.mpf("-0.5")
        * mp.cosh(d * ell(q))
    )


def check_density_closed_form() -> None:
    """Unit mass of g_d and agreement of E phi(Q_d) via Beta(P) and via g_d."""
    for s, d in [(mp.mpf(3), mp.mpf("0.4")), (mp.mpf(4), mp.mpf("1.3")),
                 (mp.mpf("2.5"), mp.mpf("0.9")), (mp.mpf(6), mp.mpf("2.2"))]:
        # tanh-sinh quadrature across the integrable (1-4q)^{-1/2} endpoint;
        # the endpoint singularity caps the achievable precision near 1e-15.
        mass = mp.quad(lambda q: g_density(s, d, q), [0, mp.mpf("0.25")])
        assert abs(mass - 1) < mp.mpf("1e-15"), (s, d, mass)
        for phi in (lambda q: q, lambda q: q ** 2, lambda q: mp.sqrt(q),
                    lambda q: mp.e ** q):
            via_beta = E_H_beta(lambda p: phi(p * (1 - p)), s, d)
            via_g = mp.quad(lambda q: phi(q) * g_density(s, d, q), [0, mp.mpf("0.25")])
            assert abs(via_beta - via_g) < mp.mpf("1e-15"), (s, d, via_beta, via_g)
    print("PASS: closed-form density g_d integrates to 1 and reproduces E phi(Q_d)")


def check_ell_decreasing() -> None:
    """ell strictly decreasing on (0,1/4), down to the scale the crossing uses.

    A sweep stopping at q = 1e-3 leaves ell unchecked exactly where the LR
    crossing sits (q ~ 2e-5 at s = 0.6, d_1 = 0.05, d_2 = 0.28), so the grid runs
    on down to 1e-10.
    """
    qs = ([mp.mpf(10) ** (-mp.mpf(i) / 4) for i in range(40, 4, -1)]
          + [mp.mpf(i) / 1000 for i in range(1, 250)])
    qs = sorted(q for q in set(qs) if 0 < q < mp.mpf("0.25"))
    vals = [ell(q) for q in qs]
    for a, b in zip(vals, vals[1:]):
        assert a > b, (a, b)
    assert vals[-1] > 0 and ell(mp.mpf("0.2499")) < vals[-1]
    assert qs[0] < mp.mpf(10) ** (-9), qs[0]
    # the load-bearing scale itself, named rather than left implicit
    assert mp.mpf("10.8") < ell(mp.mpf(2) * mp.mpf(10) ** (-5)) < mp.mpf("10.9")
    print(f"PASS: ell(q) strictly decreasing on (0,1/4), swept from q = {mp.nstr(qs[0], 3)} "
          f"up, with ell(2e-5) = {mp.nstr(ell(mp.mpf(2) * mp.mpf(10) ** (-5)), 4)}")


def check_cosh_ratio_monotone() -> None:
    """d tanh(d ell) increasing in d, and cosh(d2 ell)/cosh(d1 ell) in ell.

    The range matters: this file's own load-bearing LR case sits at
    ell(2e-5) = 10.82, so a sweep stopping at ell = 4 would leave the step the
    argument actually uses untested.  Both sweeps run past 12.
    """
    top = ell(mp.mpf(10) ** (-6))                 # ~ 13.8, past every case here
    assert top > 12, top
    for L in [mp.mpf("0.1"), mp.mpf("1"), mp.mpf("4"), mp.mpf("10.82"), top]:
        ds = [mp.mpf(i) / 10 for i in range(1, 60)]
        vals = [d * mp.tanh(d * L) for d in ds]
        for a, b in zip(vals, vals[1:]):
            assert b > a, (L, a, b)
    # for d2>d1, cosh(d2 ell)/cosh(d1 ell) strictly increasing in ell
    for d1, d2 in [(mp.mpf("0.5"), mp.mpf("1.7")),
                   (mp.mpf("0.05"), mp.mpf("0.28")),      # the s = 0.6 LR case
                   (mp.mpf(0), mp.mpf("2.2"))]:
        Ls = [mp.mpf(i) / 100 for i in range(1, 1401)]    # ell up to 14
        ratio = [mp.cosh(d2 * L) / mp.cosh(d1 * L) for L in Ls]
        for a, b in zip(ratio, ratio[1:]):
            assert b > a, (d1, d2, a, b)
        assert Ls[-1] > top
    print(f"PASS: d tanh(d ell) increasing and the cosh-ratio increasing in ell, "
          f"swept to ell = 14 (the case in hand needs ell = "
          f"{mp.nstr(ell(mp.mpf(2) * mp.mpf(10) ** (-5)), 4)})")


# The trailing flag is whether Berenhaut-Bergen Thm 3 reaches the case.  Their
# hypothesis is beta - alpha >= 1 or beta = alpha, of BOTH compared pairs; here
# beta - alpha = 2d, so it reads 2d in {0} u [1,oo).  The paper states the
# comparison for every 0 <= d_1 < d_2 < s/2, and the cases below are what makes
# that wider range a tested claim rather than an asserted one -- see
# `check_cases_reach_past_the_gap_restriction`.
LR_CASES = [
    (mp.mpf(3), mp.mpf("0.3"), mp.mpf("1.1")),          # 2d_1 = 0.6: outside
    (mp.mpf(5), mp.mpf("0.7"), mp.mpf("2.2")),          # 1.4, 4.4: inside
    # small s with a small second Beta parameter: b_2 = s/2 - d_2 = 0.02, so the
    # crossing sits near q = 2e-5.  A linear grid starting at q = 0.02 reports
    # diffs[0] > 0 here and the "negative near 0" assertion would fail on a true
    # claim -- this is the case that makes the log refinement load-bearing.
    # It is also the only case with BOTH gaps below 1, so it is the one that
    # exercises the wider range on both sides at once.
    (mp.mpf("0.6"), mp.mpf("0.05"), mp.mpf("0.28")),    # 0.1, 0.56: outside, both
    (mp.mpf(2), mp.mpf("0.25"), mp.mpf("0.9")),         # 2d_1 = 0.5: outside
]


def _reaches_past_gap_restriction(d1, d2):
    """True when (d_1, d_2) lies outside Berenhaut-Bergen Thm 3's hypotheses.

    At a fixed parameter sum their gap condition is 2d in {0} u [1,oo), required
    of both pairs; a case fails it as soon as either gap lies strictly in (0,1).
    """
    admits = lambda gap: gap == 0 or gap >= 1
    return not (admits(2 * d1) and admits(2 * d2))


def check_cases_reach_past_the_gap_restriction() -> None:
    """The swept cases must exercise gaps the cited comparison cannot reach.

    Guards the manuscript's own scope claim.  Without this the sweep could be
    narrowed to gaps of 1 or more by an ordinary edit, every assertion in the
    file would still pass, and the wider range would silently stop being tested.
    """
    outside = [(s, d1, d2) for s, d1, d2 in LR_CASES
               if _reaches_past_gap_restriction(d1, d2)]
    assert outside, "no swept case exercises a gap below 1"
    both = [(s, d1, d2) for s, d1, d2 in outside
            if 0 < 2 * d1 < 1 and 0 < 2 * d2 < 1]
    assert both, "no swept case has both gaps below 1"
    s, d1, d2 = both[0]
    assert 0 <= d1 < d2 < s / 2                       # inside the lemma's range
    print(f"PASS: {len(outside)} of {len(LR_CASES)} swept cases lie outside the "
          f"gap restriction 2d in {{0}} u [1,oo), and s = {mp.nstr(s, 3)}, "
          f"d_1 = {mp.nstr(d1, 3)}, d_2 = {mp.nstr(d2, 3)} has both gaps below 1 "
          f"(2d_1 = {mp.nstr(2 * d1, 3)}, 2d_2 = {mp.nstr(2 * d2, 3)})")


def _lr_grid():
    """Log-refined grid on (0,1/4): resolves crossings down to q ~ 1e-11."""
    log_part = [mp.mpf(10) ** (-mp.mpf(i) / 4) for i in range(4, 45)]
    lin_part = [mp.mpf(i) / 1000 for i in range(20, 246)]
    return sorted(q for q in set(log_part + lin_part) if 0 < q < mp.mpf("0.25"))


def check_likelihood_ratio_single_crossing() -> None:
    """g_{d2}/g_{d1} strictly decreasing in q; g_{d1}-g_{d2} crosses sign once."""
    qs = _lr_grid()
    for s, d1, d2 in LR_CASES:
        ratio = [g_density(s, d2, q) / g_density(s, d1, q) for q in qs]
        for a, b in zip(ratio, ratio[1:]):
            assert b < a, (s, d1, d2)                       # strictly decreasing
        diffs = [g_density(s, d1, q) - g_density(s, d2, q) for q in qs]
        assert diffs[0] < 0 < diffs[-1]                     # neg near 0, pos near 1/4
        sign_changes = sum(1 for a, b in zip(diffs, diffs[1:]) if a < 0 <= b or a >= 0 > b)
        assert sign_changes == 1, (s, d1, d2, sign_changes)
    print(f"PASS: LR order (single crossing of g_{{d1}}-g_{{d2}}, neg->pos), "
          f"{len(LR_CASES)} cases on a log-refined grid")


def check_lr_grid_refinement_is_load_bearing() -> None:
    """The crossing sits below q = 1/50, so the grid must resolve small q.

    At s = 0.6, d_1 = 0.05, d_2 = 0.28 the difference g_{d_1} - g_{d_2} is still
    POSITIVE at q = 1/50 and turns negative only near q = 2e-5.  A grid whose
    smallest point is 1/50 therefore sees the wrong sign near 0, while the paper's
    claim -- negative near 0 -- is asymptotic and correct.  This fixes the scale the
    log refinement has to reach.
    """
    s, d1, d2 = mp.mpf("0.6"), mp.mpf("0.05"), mp.mpf("0.28")
    coarse_min = mp.mpf(20) / 1000
    assert g_density(s, d1, coarse_min) - g_density(s, d2, coarse_min) > 0
    # far enough left the sign is the negative one the paper asserts
    deep = mp.mpf(10) ** (-8)
    assert g_density(s, d1, deep) - g_density(s, d2, deep) < 0
    # the true crossing, bracketed and bisected
    lo, hi = deep, coarse_min
    for _ in range(200):
        mid = (lo + hi) / 2
        if g_density(s, d1, mid) - g_density(s, d2, mid) < 0:
            lo = mid
        else:
            hi = mid
    qstar = (lo + hi) / 2
    assert mp.mpf(10) ** (-6) < qstar < mp.mpf(10) ** (-4), qstar
    print("PASS: the crossing sits at q ~ 2e-5 for s=0.6, so a grid reaching only "
          "q=1/50 would read the sign near 0 backwards")


def check_crossing_integrand_nonnegative() -> None:
    """The proof's integrand is nonnegative THROUGHOUT (0,1/4), not just on average.

    `lem:beta-order`'s proof writes
        E phi(Q_{d1}) - E phi(Q_{d2})
          = int_0^{1/4} (phi(q) - phi(q*)) (g_{d1}(q) - g_{d2}(q)) dq >= 0,
    asserting the integrand is nonnegative pointwise.  That needs phi - phi(q*)
    and g_{d1} - g_{d2} to change sign at the same q*, and the identity itself
    needs both densities to carry unit mass, so the phi(q*) term integrates out.
    Both hold for nondecreasing phi, including a discontinuous step.
    """
    qs = _lr_grid()
    phis = [
        ("q", lambda q: q),
        ("q^3", lambda q: q ** 3),
        ("log(1+q)", lambda q: mp.log(1 + q)),
        ("step at 1/12", lambda q: mp.mpf(0) if q < mp.mpf(1) / 12 else mp.mpf(1)),
    ]
    for s, d1, d2 in LR_CASES:
        diffs = [g_density(s, d1, q) - g_density(s, d2, q) for q in qs]
        lo = max(q for q, v in zip(qs, diffs) if v < 0)
        hi = min(q for q, v in zip(qs, diffs) if v > 0)
        for _ in range(200):
            mid = (lo + hi) / 2
            if g_density(s, d1, mid) - g_density(s, d2, mid) < 0:
                lo = mid
            else:
                hi = mid
        qstar = (lo + hi) / 2
        assert 0 < qstar < mp.mpf("0.25"), (s, d1, d2, qstar)
        for name, phi in phis:
            for q, dv in zip(qs, diffs):
                integrand = (phi(q) - phi(qstar)) * dv
                assert integrand >= -mp.mpf("1e-30"), (name, s, d1, d2, q, integrand)
    print("PASS: (phi(q)-phi(q*))(g_{d1}(q)-g_{d2}(q)) >= 0 throughout (0,1/4)")


def check_imbalance_ordering() -> None:
    """E H(P_{d1}) >= E H(P_{d2}) for symmetric H nondecreasing on [0,1/2]."""
    Hs_strict = [
        ("p(1-p)", lambda p: p * (1 - p)),
        ("(p(1-p))^2", lambda p: (p * (1 - p)) ** 2),
        ("sin(pi p)", lambda p: mp.sin(mp.pi * p)),
        ("min(p,1-p)", lambda p: min(p, 1 - p)),
    ]
    cases = [(mp.mpf(3), mp.mpf("0.2"), mp.mpf("1.0")),
             (mp.mpf(4), mp.mpf("0.5"), mp.mpf("1.6")),
             (mp.mpf("2.5"), mp.mpf("0"), mp.mpf("1.0")),
             (mp.mpf(7), mp.mpf("1.0"), mp.mpf("3.0"))]
    for name, H in Hs_strict:
        for s, d1, d2 in cases:
            e1, e2 = E_H_beta(H, s, d1), E_H_beta(H, s, d2)
            assert e1 - e2 > mp.mpf("1e-15"), (name, s, d1, d2, e1, e2)  # strict
    # a constant H (symmetric, nondecreasing but not strictly) gives equality
    e1 = E_H_beta(lambda p: mp.mpf(1), mp.mpf(3), mp.mpf("0.2"))
    e2 = E_H_beta(lambda p: mp.mpf(1), mp.mpf(3), mp.mpf("1.0"))
    assert abs(e1 - e2) < mp.mpf("1e-20")
    print("PASS: E H(P_{d1}) >= E H(P_{d2}), strict for strictly increasing H (`eq:beta-order`)")


def check_beta_order_hypotheses_on_H() -> None:
    r"""`lem:beta-order`'s two hypotheses on H each have a counterexample when dropped.

    `eq:beta-order` needs H symmetric AND nondecreasing on [0,1/2]; the LR order it is
    derived from is a statement about Q_d = P_d(1-P_d), so an H that does not
    factor through p(1-p) is not covered at all.

      * NOT symmetric.  H(p) = p is nondecreasing on [0,1/2] and
        E P_d = (s/2+d)/s is INcreasing in d, so `eq:beta-order` reverses:
        at s = 3, d_1 = 0.2, d_2 = 1.0 the difference is -4/15.
      * NOT nondecreasing.  H(p) = max(p,1-p) is symmetric and strictly
        DEcreasing on [0,1/2]; it is 1 - min(p,1-p), so it reverses the strict
        instance already asserted above.
    """
    s, d1, d2 = mp.mpf(3), mp.mpf("0.2"), mp.mpf(1)
    # E P_d = (s/2+d)/s, so the exact gap is -(d2-d1)/s = -4/15; the quadrature
    # carries an endpoint singularity at both ends, hence the 1e-18 margin
    gap = E_H_beta(lambda p: p, s, d1) - E_H_beta(lambda p: p, s, d2)
    assert abs(gap - (-(d2 - d1) / s)) < mp.mpf("1e-18"), gap
    assert gap < -mp.mpf("0.26"), gap
    # H(p) = p fails symmetry at every p off 1/2, which is the hypothesis dropped
    assert mp.mpf("0.3") != 1 - mp.mpf("0.3")

    H = lambda p: max(p, 1 - p)
    Hmin = lambda p: min(p, 1 - p)
    for ss, a, b in [(mp.mpf(3), mp.mpf("0.2"), mp.mpf(1)),
                     (mp.mpf(4), mp.mpf("0.5"), mp.mpf("1.6")),
                     (mp.mpf("2.5"), mp.mpf(0), mp.mpf(1)),
                     (mp.mpf(7), mp.mpf(1), mp.mpf(3))]:
        assert H(mp.mpf("0.1")) > H(mp.mpf("0.4")), "not decreasing on [0,1/2]"
        assert abs(H(mp.mpf("0.3")) - H(mp.mpf("0.7"))) < mp.mpf("1e-30")  # symmetric
        rev = E_H_beta(H, ss, a) - E_H_beta(H, ss, b)
        assert rev < -mp.mpf("1e-10"), (ss, a, b, rev)
        # max(p,1-p) = 1 - min(p,1-p) and both densities carry unit mass, so the
        # reversal is exactly the negative of the gap the increasing min(p,1-p)
        # produces -- asserted as that identity rather than as two numbers.  Each
        # side is a separate quadrature against a density with endpoint
        # singularities, so the residual is quadrature error and the comparison
        # has to be relative: it runs from 6e-22 to 5e-11 of the gap across these
        # parameters, worst at d_1 = 0, while breaking the identity moves the
        # residual to twice the gap.
        keep = E_H_beta(Hmin, ss, a) - E_H_beta(Hmin, ss, b)
        assert keep > mp.mpf("1e-10"), (ss, a, b, keep)
        assert abs(rev + keep) < mp.mpf("1e-9") * keep, (ss, a, b, rev, keep)
    # the value at the parameters this file states, pinned
    gap_min = (E_H_beta(Hmin, mp.mpf(3), mp.mpf("0.2"))
               - E_H_beta(Hmin, mp.mpf(3), mp.mpf(1)))
    assert abs(gap_min - mp.mpf("0.1353056825")) < mp.mpf("1e-9"), gap_min
    print(f"PASS: `eq:beta-order` needs both hypotheses on H -- H(p)=p (nondecreasing, not "
          f"symmetric) reverses it by {mp.nstr(gap, 4)}, and H(p)=max(p,1-p) "
          f"(symmetric, decreasing) reverses it too")


def main() -> None:
    check_abel_identity()
    check_cone_equivalence()
    check_one_sign_change_gives_positive_tails()
    check_weighting()
    check_weighting_strict_hypotheses_load_bearing()
    check_weighting_needs_nondecreasing_nonnegative_weights()
    check_weighting_needs_one_sign_change()
    check_weighting_direction_is_a_hypothesis()
    check_density_closed_form()
    check_ell_decreasing()
    check_cosh_ratio_monotone()
    check_cases_reach_past_the_gap_restriction()
    check_likelihood_ratio_single_crossing()
    check_lr_grid_refinement_is_load_bearing()
    check_crossing_integrand_nonnegative()
    check_imbalance_ordering()
    check_beta_order_hypotheses_on_H()
    print("ALL PASS: verify_monotonicity_lemmas")


if __name__ == "__main__":
    main()
