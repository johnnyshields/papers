#!/usr/bin/env python3
r"""Paper section 3 (Two monotonicity lemmas).

Lemma 3.1 (one-sign-change weighting).  For 0 <= w_1 <= ... <= w_L and a real
sequence A with at most one sign change (nonpositive then nonnegative) and
sum A_k >= 0, one has sum w_k A_k >= 0.  Verified on random admissible data,
including the proof's pivot inequality sum w_k A_k >= w_{k_0} sum A_k and its
c = 0 branch (w_k = 0 for k <= k_0, so the sum collapses to the tail).  The
strict clause -- sum A_k > 0, w_L > 0, A_L > 0 imply sum w_k A_k > 0 -- is the
form the strict half of Theorem 4.1 consumes, and each of its three added
hypotheses is shown load-bearing by dropping it and exhibiting a counterexample.
Both the single-sign-change hypothesis and its direction (nonpositive before
nonnegative, which is a hypothesis and not a consequence) are stress-tested by
sequences for which the conclusion fails.

Lemma 3.2 (symmetric beta imbalance ordering).  For P_d ~ Beta(s/2+d, s/2-d)
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
  * therefore E H(P_{d_1}) >= E H(P_{d_2}), eq. (3.1), for every symmetric H
    nondecreasing on [0,1/2], strictly when H is strictly increasing.

The crossing of g_{d_1} - g_{d_2} can sit at q ~ 1e-5 (it does at s = 0.6,
d_1 = 0.05, d_2 = 0.28, because g_d(q) ~ q^{s/2-1-d}/B near 0), so the
single-crossing sweep uses a log-refined grid reaching that scale.

The weighting lemma (3.1) uses exact rational arithmetic (fractions); the beta
imbalance ordering (3.2) uses mpmath at arbitrary precision.
"""
from __future__ import annotations

import random
from fractions import Fraction

import mpmath as mp

mp.mp.dps = 40


# ===========================================================================
# Lemma 3.1  One-sign-change weighting
# ===========================================================================
def _rand_frac(rng: random.Random, hi: int, den: int = 10 ** 6) -> Fraction:
    """A uniform rational in [0, hi), exact (no float)."""
    return Fraction(rng.randint(0, den - 1), den) * hi


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
        # proof pivot: sum w_k A_k >= c * sum A_k with c = w at the last neg index
        neg = [i for i, a in enumerate(A) if a < 0]
        if neg:
            c = w[neg[-1]]
            assert wsum >= c * sum(A)
        # the strict clause, on every draw that satisfies its three hypotheses
        if sum(A) > 0 and w[-1] > 0 and A[-1] > 0:
            assert wsum > 0, ("strict clause fails", w, A, wsum)
            strict_cases += 1
    # these draws have w_1 > 0, so c > 0 throughout; the c = 0 branch is
    # check_weighting_c_zero_branch
    assert strict_cases > trials // 4, strict_cases
    print(f"PASS: one-sign-change weighting, pivot bound, and the strict clause "
          f"({strict_cases}/{trials} draws reach it) (Lemma 3.1)")


def check_weighting_c_zero_branch(trials: int = 400, seed: int = 20260729) -> None:
    """The c = 0 branch of Lemma 3.1's proof, driven explicitly.

    The proof splits on c = w_{k_0}, with k_0 the largest index carrying A_{k_0} < 0.
    When c = 0 the pivot bound sum w_k A_k >= c sum A_k carries no information, so
    the proof argues separately: w_k <= c = 0 forces w_k = 0 for every k <= k_0, the
    head of the sum drops out, and what remains is the tail
    sum_{k > k_0} w_k A_k >= w_L A_L.  These draws pin w_1 = ... = w_{k_0} = 0 by
    construction, since c = 0 requires it.
    """
    rng = random.Random(seed)
    reached = 0
    for _ in range(trials):
        L = rng.randint(2, 12)
        k0 = rng.randint(0, L - 2)              # last nonpositive index, k0 < L-1
        # weights: zero through k0, then strictly increasing
        w = [Fraction(0)] * (k0 + 1)
        cur = Fraction(0)
        for _k in range(k0 + 1, L):
            cur += _rand_frac(rng, 2) + Fraction(1, 100)
            w.append(cur)
        assert all(w[i] <= w[i + 1] for i in range(L - 1))     # nondecreasing
        A = [-_rand_frac(rng, 3) - Fraction(1, 100) for _ in range(k0 + 1)] \
            + [_rand_frac(rng, 3) for _ in range(L - k0 - 1)]
        A[-1] += max(Fraction(0), -sum(A)) + Fraction(1, 10)   # force sum > 0
        assert sum(A) > 0 and A[-1] > 0 and w[-1] > 0
        neg = [i for i, a in enumerate(A) if a < 0]
        assert neg and neg[-1] == k0, (A, k0)
        c = w[k0]
        assert c == 0                                          # the branch of interest
        wsum = sum(wi * ai for wi, ai in zip(w, A))
        # the head vanishes and the sum collapses onto the tail
        tail = sum(w[i] * A[i] for i in range(k0 + 1, L))
        assert wsum == tail, (w, A, wsum, tail)
        assert sum(w[i] * A[i] for i in range(k0 + 1)) == 0
        # and the strict conclusion still holds, via w_L A_L
        assert wsum >= w[-1] * A[-1] > 0, (w, A, wsum)
        reached += 1
    assert reached == trials
    print(f"PASS: the c=0 branch of Lemma 3.1's proof, {reached} constructed draws")


def check_weighting_strict_hypotheses_load_bearing() -> None:
    """Each of the strict clause's three added hypotheses is load-bearing.

    The strict clause reads: if additionally sum A_k > 0, w_L > 0 and A_L > 0,
    then sum w_k A_k > 0.  Dropping any one of the three admits an admissible
    (w, A) with sum w_k A_k = 0, so none is ornamental.  These are exactly the
    three inputs the strict half of Theorem 4.1 supplies (sum_k B_{m,k} = J_m > 0
    by Lemma 4.2; w_L > 0 from "not all zero" with eq. (4.1); B_{m,L} > 0 by
    Lemma 4.3), so the clause is what carries strictness into Corollary 5.2.
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
    hypothesis of Lemma 3.1 and breaks the conclusion.  The proof consumes the
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
# Lemma 3.2  Symmetric beta imbalance ordering
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
    qs = [mp.mpf(i) / 1000 for i in range(1, 250)]
    vals = [ell(q) for q in qs]
    for a, b in zip(vals, vals[1:]):
        assert a > b, (a, b)
    assert vals[-1] > 0 and ell(mp.mpf("0.2499")) < vals[-1]
    print("PASS: ell(q) strictly decreasing on (0,1/4)")


def check_cosh_ratio_monotone() -> None:
    # d -> d tanh(d ell) strictly increasing in d (for ell>0)
    for L in [mp.mpf("0.1"), mp.mpf("1"), mp.mpf("4")]:
        ds = [mp.mpf(i) / 10 for i in range(1, 60)]
        vals = [d * mp.tanh(d * L) for d in ds]
        for a, b in zip(vals, vals[1:]):
            assert b > a
    # for d2>d1, cosh(d2 ell)/cosh(d1 ell) strictly increasing in ell
    d1, d2 = mp.mpf("0.5"), mp.mpf("1.7")
    Ls = [mp.mpf(i) / 100 for i in range(1, 400)]
    ratio = [mp.cosh(d2 * L) / mp.cosh(d1 * L) for L in Ls]
    for a, b in zip(ratio, ratio[1:]):
        assert b > a
    print("PASS: d tanh(d ell) increasing; cosh-ratio increasing in ell (d2>d1)")


LR_CASES = [
    (mp.mpf(3), mp.mpf("0.3"), mp.mpf("1.1")),
    (mp.mpf(5), mp.mpf("0.7"), mp.mpf("2.2")),
    # small s with a small second Beta parameter: b_2 = s/2 - d_2 = 0.02, so the
    # crossing sits near q = 2e-5.  A linear grid starting at q = 0.02 reports
    # diffs[0] > 0 here and the "negative near 0" assertion would fail on a true
    # claim -- this is the case that makes the log refinement load-bearing.
    (mp.mpf("0.6"), mp.mpf("0.05"), mp.mpf("0.28")),
    (mp.mpf(2), mp.mpf("0.25"), mp.mpf("0.9")),
]


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

    Lemma 3.2's proof writes
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
    print("PASS: E H(P_{d1}) >= E H(P_{d2}), strict for strictly increasing H (eq. 3.1)")


def main() -> None:
    check_weighting()
    check_weighting_c_zero_branch()
    check_weighting_strict_hypotheses_load_bearing()
    check_weighting_needs_one_sign_change()
    check_weighting_direction_is_a_hypothesis()
    check_density_closed_form()
    check_ell_decreasing()
    check_cosh_ratio_monotone()
    check_likelihood_ratio_single_crossing()
    check_lr_grid_refinement_is_load_bearing()
    check_crossing_integrand_nonnegative()
    check_imbalance_ordering()
    print("ALL PASS: verify_monotonicity_lemmas")


if __name__ == "__main__":
    main()
