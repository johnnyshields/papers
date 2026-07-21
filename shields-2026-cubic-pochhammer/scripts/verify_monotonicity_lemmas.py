#!/usr/bin/env python3
r"""Paper section 3 (Two monotonicity lemmas).

Lemma 3.1 (one-sign-change weighting).  For 0 <= w_1 <= ... <= w_L and a real
sequence A with at most one sign change (nonpositive then nonnegative) and
sum A_k >= 0, one has sum w_k A_k >= 0.  Verified on random admissible data,
including the proof's pivot inequality sum w_k A_k >= w_q sum A_k; the
single-sign-change hypothesis is stress-tested by exhibiting a two-sign-change
sequence for which the conclusion fails.

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
  * therefore E H(P_{d_1}) >= E H(P_{d_2}), eq. (3.1), for every symmetric H
    nondecreasing on [0,1/2], strictly when H is strictly increasing.

Numerical work uses mpmath at arbitrary precision.
"""
from __future__ import annotations

import random

import mpmath as mp

mp.mp.dps = 40


# ===========================================================================
# Lemma 3.1  One-sign-change weighting
# ===========================================================================
def check_weighting(trials: int = 5000, seed: int = 20260721) -> None:
    rng = random.Random(seed)
    for _ in range(trials):
        L = rng.randint(1, 12)
        # nondecreasing nonnegative weights
        w = []
        cur = 0.0
        for _k in range(L):
            cur += rng.random() * 2
            w.append(cur)
        # A with a single sign change from nonpositive to nonnegative
        q = rng.randint(0, L)                         # last nonpositive index
        A = [-rng.random() * 3 for _ in range(q)] + [rng.random() * 3 for _ in range(L - q)]
        # force sum >= 0 by padding the positive tail
        if sum(A) < 0:
            A[-1] += -sum(A) + rng.random()
        assert sum(A) >= -1e-12
        wsum = sum(wi * ai for wi, ai in zip(w, A))
        assert wsum >= -1e-9, (w, A, wsum)
        # proof pivot: sum w_k A_k >= c * sum A_k with c = w at the last neg index
        neg = [i for i, a in enumerate(A) if a < 0]
        if neg:
            c = w[neg[-1]]
            assert wsum + 1e-9 >= c * sum(A)
    print("PASS: one-sign-change weighting and pivot bound (Lemma 3.1)")


def check_weighting_needs_one_sign_change() -> None:
    """Two sign changes can break the conclusion: the hypothesis is load-bearing."""
    w = [0.0, 1.0, 5.0]                # nondecreasing, nonnegative
    A = [1.0, -1.0, 0.1]               # sum = 0.1 >= 0, TWO sign changes
    assert sum(A) >= 0
    assert sum(wi * ai for wi, ai in zip(w, A)) < 0     # weighted sum negative
    print("PASS: two sign changes break the conclusion (hypothesis is sharp)")


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


def check_likelihood_ratio_single_crossing() -> None:
    """g_{d2}/g_{d1} strictly decreasing in q; g_{d1}-g_{d2} crosses sign once."""
    for s, d1, d2 in [(mp.mpf(3), mp.mpf("0.3"), mp.mpf("1.1")),
                      (mp.mpf(5), mp.mpf("0.7"), mp.mpf("2.2"))]:
        qs = [mp.mpf(i) / 1000 for i in range(20, 246)]
        ratio = [g_density(s, d2, q) / g_density(s, d1, q) for q in qs]
        for a, b in zip(ratio, ratio[1:]):
            assert b < a, (s, d1, d2)                       # strictly decreasing
        diffs = [g_density(s, d1, q) - g_density(s, d2, q) for q in qs]
        assert diffs[0] < 0 < diffs[-1]                     # neg near 0, pos near 1/4
        sign_changes = sum(1 for a, b in zip(diffs, diffs[1:]) if a < 0 <= b or a >= 0 > b)
        assert sign_changes == 1, (s, d1, d2, sign_changes)
    print("PASS: LR order (single crossing of g_{d1}-g_{d2}, neg->pos)")


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
    check_weighting_needs_one_sign_change()
    check_density_closed_form()
    check_ell_decreasing()
    check_cosh_ratio_monotone()
    check_likelihood_ratio_single_crossing()
    check_imbalance_ordering()
    print("ALL PASS: verify_monotonicity_lemmas")


if __name__ == "__main__":
    main()
