#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `lem:amplitude-divisor`,
`eq:W-endpoint-form`, `eq:phase-derivative-bound`.

The two constants of the endpoint cofactor bound, pinned before they are
asserted in Lean.

`check_endpoint_branch_lipschitz.py` settles that `gamma'` is Lipschitz at the
endpoint and that the surviving term of `Im(W'/W)` is `-m * Im(u'/u)` with
`u(theta) = (gamma(theta) - t_a)/theta`.  What it does NOT fix is the pair of
constants the Lean proof has to name, and a guessed constant is exactly where a
sharp bound trips.  Both are derived here from the same two-term decomposition
the Lean proof uses, then measured against families chosen to make each one
tight in turn.

Write `g(theta) = gamma(theta) - t_a`, so `g(0) = 0`, and let `L` be a Lipschitz
constant for `g'` on `[0,b]`.  The Lean proof runs on exactly two estimates:

  (C1) THE TAYLOR BOUND.  `f(theta) = g(theta) - theta*g'(0)` has `f(0) = 0` and
       `||f'(theta)|| = ||g'(theta) - g'(0)|| <= L*theta`, so Mathlib's
       `image_norm_le_of_norm_deriv_right_le_deriv_boundary` against the
       boundary `B(theta) = L*theta^2/2` gives

           ||g(theta) - theta*g'(0)|| <= L*theta^2/2.

       The constant `1/2` is the one an integral route would give and it is
       attained, not slack.

  (C2) THE COFACTOR-DERIVATIVE BOUND.  `u'` has numerator
       `g'(theta)*theta - g(theta)`, which the Lean proof splits as

           theta*(g'(theta) - g'(0))  -  (g(theta) - theta*g'(0)),

       bounding the two pieces by `L*theta^2` and `L*theta^2/2` for a total of

           ||g'(theta)*theta - g(theta)|| <= (3/2)*L*theta^2,   so  ||u'|| <= 3L/2.

       The split is what avoids a second application of the boundary lemma; the
       price is that `3/2` is NOT sharp -- the sharp constant is `1/2`.  What
       has to be true is that `3/2` is an upper bound at every family, including
       the one that makes `1/2` an equality, and that is what is asserted.

Below `b' = min(b, ||g'(0)||/(L+1))` the cofactor stays off zero:
`||u(theta) - g'(0)|| <= L*theta/2` by (C1), so `||u|| >= ||g'(0)||/2`, whence

  (C3) `|Im(u'/u)| <= ||u'||/||u|| <= (3L/2)/(||g'(0)||/2) = 3L/||g'(0)||`.

The `L+1` rather than `L` in `b'` is deliberate: at `L = 0` the branch is affine
and `||g'(0)||/L` is `x/0 = 0` in Lean's arithmetic, which would hand back an
EMPTY collar while every bound above holds on all of `[0,b]`.  That is the
`x / 0 = 0` trap, and (C4) instantiates at `L = 0` to keep it closed.

Asserted, each as a failing test:

  (C1) holds, and is ATTAINED in the limit by `g(theta) = theta + L*theta^2/2`
       -- so no constant below `1/2` is available.
  (C2) holds at five families, including the `theta^{3/2}`-perturbed one whose
       derivative is Lipschitz only after the exponent is raised, and including
       the family that attains `1/2`; and the observed ratio never exceeds
       `3/2`.
  (C3) holds at the same families, and the collar `b'` is where it starts to.
  (C4) at `L = 0` the collar is NONEMPTY and equals `b` -- the `x/0` guard.
  (C5) the two-term split is not vacuous: at the family attaining (C1) the
       numerator really is order `theta^2` and not smaller, so `u'` is bounded
       away from `0` and a bound is genuinely needed rather than trivial.
"""

from mpmath import mp, mpf, mpc, sqrt, fabs, im, re

mp.dps = 40


def taylor_defect(g, dg, theta):
    """||g(theta) - theta*g'(0)||."""
    return abs(g(theta) - theta * dg(mpf(0)))


def cofactor_numerator(g, dg, theta):
    """||g'(theta)*theta - g(theta)||, the numerator of u'."""
    return abs(dg(theta) * theta - g(theta))


def cofactor(g, theta):
    return g(theta) / theta


def cofactor_deriv(g, dg, theta):
    return (dg(theta) * theta - g(theta)) / theta ** 2


# Four families.  Each is (name, g, g', L on [0, b], b).  `L` is a genuine
# Lipschitz constant for `g'` on `[0, b]`, verified in (C0) below.
def families():
    b = mpf('0.5')

    # (a) the (C1)-extremal family: g' is exactly L-Lipschitz, affinely.
    L_a = mpf('2')
    fam_a = ("g = t + t^2  (g' exactly L-Lipschitz)",
             lambda t: t + t ** 2, lambda t: 1 + 2 * t, L_a, b)

    # (b) complex, rotated -- the endpoint coefficient is not real.
    L_b = mpf('3')
    w = mpc(0, 1)
    fam_b = ("g = (i)t + (3/2)t^2  (complex leading coefficient)",
             lambda t: w * t + mpf('1.5') * t ** 2,
             lambda t: w + 3 * t, L_b, b)

    # (c) g' Lipschitz but g not a polynomial: g = t + t^{5/2}, g' = 1+(5/2)t^{3/2},
    #     which IS Lipschitz on [0,b] (exponent 3/2 > 1) with constant
    #     (15/4)*sqrt(b).
    L_c = mpf('15') / 4 * sqrt(b)
    fam_c = ("g = t + t^{5/2}  (g' Lipschitz, g not C^2 at 0... but g'' bounded)",
             lambda t: t + t ** mpf('2.5'),
             lambda t: 1 + mpf('2.5') * t ** mpf('1.5'), L_c, b)

    # (d) the FT shape: g = c*t*(1 + a t + ...) with c the endpoint slope.
    c = mpc(mpf('0.3'), mpf('-0.7'))
    L_d = mpf('4')
    fam_d = ("g = c t (1 - t/2 + t^2/3)  (Forgacs-Tran endpoint shape)",
             lambda t: c * t * (1 - t / 2 + t ** 2 / 3),
             lambda t: c * (1 - t + t ** 2), L_d, b)

    # (e) leading and quadratic coefficients NOT parallel, so `u'/u` is
    #     genuinely nonreal and (C3) tests the imaginary part rather than
    #     passing on `Im = 0`.  In (a), (c) and (d) the endpoint slope factors
    #     out of `u'/u` entirely and the quotient is real; without this family
    #     the `Im` in (C3) would be untested at four families out of five.
    L_e = mpf('5')
    fam_e = ("g = t + (i/2)t^2 + (1+i)t^3/3  (u'/u genuinely nonreal)",
             lambda t: t + mpc(0, mpf('0.5')) * t ** 2 + mpc(1, 1) * t ** 3 / 3,
             lambda t: 1 + mpc(0, 1) * t + mpc(1, 1) * t ** 2, L_e, b)

    return [fam_a, fam_b, fam_c, fam_d, fam_e]


def sample_grid(b, n=400):
    return [b * mpf(i) / n for i in range(1, n + 1)]


def main():
    print("check_endpoint_cofactor_bound.py")
    print("Paper: `sec:geometry`, `eq:W-endpoint-form`, `eq:phase-derivative-bound`")
    print()

    fams = families()

    # ---- (C0) the declared L really is a Lipschitz constant for g' ----------
    print("  (C0) the declared L bounds ||g'(s) - g'(t)|| / |s - t| on [0,b]:")
    for name, g, dg, L, b in fams:
        grid = sample_grid(b, 120)
        worst = mpf(0)
        for i, s in enumerate(grid):
            for t in grid[::17]:
                if s == t:
                    continue
                worst = max(worst, abs(dg(s) - dg(t)) / fabs(s - t))
        assert worst <= L * (1 + mpf('1e-20')), \
            "declared L is not a Lipschitz constant for %s: %s > %s" % (name, worst, L)
        print("       %-58s  sup ratio %s <= L = %s"
              % (name, mp.nstr(worst, 6), mp.nstr(L, 6)))
    print()

    # ---- (C1) the Taylor bound, with 1/2 attained --------------------------
    print("  (C1) ||g(t) - t g'(0)|| <= L t^2 / 2:")
    for name, g, dg, L, b in fams:
        worst_ratio = mpf(0)
        for t in sample_grid(b):
            lhs = taylor_defect(g, dg, t)
            rhs = L * t ** 2 / 2
            assert lhs <= rhs * (1 + mpf('1e-25')), \
                "(C1) failed at %s, theta=%s: %s > %s" % (name, t, lhs, rhs)
            worst_ratio = max(worst_ratio, lhs / rhs)
        print("       %-58s  worst lhs/rhs = %s" % (name, mp.nstr(worst_ratio, 8)))

    # family (a) attains it exactly: g - t g'(0) = t^2 and L t^2/2 = t^2.
    name, g, dg, L, b = fams[0]
    for t in sample_grid(b, 20):
        ratio = taylor_defect(g, dg, t) / (L * t ** 2 / 2)
        assert fabs(ratio - 1) < mpf('1e-30'), \
            "(C1) is not attained at the extremal family: ratio %s" % ratio
    print("       ATTAINED at family (a): lhs/rhs == 1 identically, so no")
    print("       constant below 1/2 is available.")
    print()

    # ---- (C2) the cofactor-derivative bound at 3/2 -------------------------
    print("  (C2) ||g'(t) t - g(t)|| <= (3/2) L t^2,  i.e.  ||u'|| <= 3L/2:")
    overall = mpf(0)
    for name, g, dg, L, b in fams:
        worst_ratio = mpf(0)
        worst_u = mpf(0)
        for t in sample_grid(b):
            lhs = cofactor_numerator(g, dg, t)
            rhs = mpf('1.5') * L * t ** 2
            assert lhs <= rhs * (1 + mpf('1e-25')), \
                "(C2) failed at %s, theta=%s: %s > %s" % (name, t, lhs, rhs)
            worst_ratio = max(worst_ratio, lhs / rhs)
            worst_u = max(worst_u, abs(cofactor_deriv(g, dg, t)))
        overall = max(overall, worst_ratio)
        print("       %-58s  worst lhs/rhs = %s, sup||u'|| = %s <= %s"
              % (name, mp.nstr(worst_ratio, 8), mp.nstr(worst_u, 6),
                 mp.nstr(mpf('1.5') * L, 6)))
    assert overall <= 1, \
        "the 3/2 split is tighter than measurement: observed ratio %s" % overall
    print("       Every observed ratio is <= 1, so 3/2 is an upper bound with")
    print("       room; the sharp constant is 1/2 and the split pays 3x for")
    print("       avoiding a second boundary-lemma application.")
    print()

    # ---- (C3) the collar and the quotient bound ----------------------------
    print("  (C3) on (0, b'] with b' = min(b, ||g'(0)||/(L+1)):")
    exercised = []
    for name, g, dg, L, b in fams:
        g0 = abs(dg(mpf(0)))
        bp = min(b, g0 / (L + 1))
        assert bp > 0, "(C3) empty collar at %s" % name
        K = 3 * L / g0
        worst_q = mpf(0)
        worst_lower = None
        for t in sample_grid(bp):
            u = cofactor(g, t)
            assert abs(u) >= g0 / 2 * (1 - mpf('1e-25')), \
                "(C3) cofactor lower bound failed at %s: |u| = %s < %s" \
                % (name, abs(u), g0 / 2)
            q = fabs(im(cofactor_deriv(g, dg, t) / u))
            assert q <= K * (1 + mpf('1e-25')), \
                "(C3) failed at %s, theta=%s: |Im(u'/u)| = %s > K = %s" \
                % (name, t, q, K)
            worst_q = max(worst_q, q)
            lo = abs(u) / g0
            worst_lower = lo if worst_lower is None else min(worst_lower, lo)
        print("       %-58s  b' = %s, sup|Im(u'/u)| = %s <= K = %s"
              % (name, mp.nstr(bp, 6), mp.nstr(worst_q, 6), mp.nstr(K, 6)))
        print("       %-58s  inf|u| / ||g'(0)|| = %s >= 1/2"
              % ("", mp.nstr(worst_lower, 6)))
        exercised.append((name, worst_q))
    live = [n for n, q in exercised if q > mpf('1e-3')]
    assert len(live) >= 2, \
        "(C3) is near-vacuous: only %d of %d families have a nonzero Im(u'/u), " \
        "so the bound is passing on Im = 0 rather than on the estimate" \
        % (len(live), len(exercised))
    print("       %d of %d families have |Im(u'/u)| bounded away from 0, so the"
          % (len(live), len(exercised)))
    print("       imaginary part is exercised rather than passing on Im = 0.")
    print()

    # ---- (C4) the x/0 guard at L = 0 ---------------------------------------
    print("  (C4) the `x / 0 = 0` guard at L = 0:")
    c0 = mpc(mpf('0.6'), mpf('0.8'))
    b0 = mpf('0.5')
    g_aff, dg_aff = (lambda t: c0 * t), (lambda t: c0)
    L0 = mpf(0)
    bp_guarded = min(b0, abs(dg_aff(mpf(0))) / (L0 + 1))
    assert bp_guarded > 0, "the guarded collar is empty at L = 0"
    assert bp_guarded == b0, \
        "at L = 0 the collar should be all of [0,b], got %s vs %s" % (bp_guarded, b0)
    # what the unguarded form would give, with Lean's `x / 0 = 0`
    unguarded_lean = min(b0, mpf(0))
    assert unguarded_lean == 0, "the unguarded control did not reproduce x/0 = 0"
    print("       guarded b' = %s = b (nonempty); unguarded, with Lean's"
          % mp.nstr(bp_guarded, 6))
    print("       `x / 0 = 0`, b' would be %s -- an EMPTY collar on a branch"
          % mp.nstr(unguarded_lean, 6))
    print("       whose every bound holds on all of [0,b].")
    for t in sample_grid(b0, 50):
        assert fabs(im(cofactor_deriv(g_aff, dg_aff, t) / cofactor(g_aff, t))) \
            < mpf('1e-30'), "affine control has nonzero Im(u'/u)"
    print("       and on it |Im(u'/u)| == 0 <= K = 0, as 3L/||g'(0)|| gives.")
    print()

    # ---- (C5) the bound is not vacuous -------------------------------------
    print("  (C5) a bound is genuinely needed -- u' does not vanish:")
    name, g, dg, L, b = fams[0]
    vals = [abs(cofactor_deriv(g, dg, t)) for t in sample_grid(b, 50)]
    assert min(vals) > mpf('0.5'), \
        "u' came out near zero at the extremal family: min %s" % min(vals)
    print("       at family (a), inf||u'|| = %s > 0 over (0,b], so the numerator"
          % mp.nstr(min(vals), 8))
    print("       is order theta^2 exactly and not smaller.")
    print()

    print("  SCOPE: five families spanning a real and a complex endpoint slope,")
    print("  a non-polynomial g with Lipschitz g', and the Forgacs-Tran endpoint")
    print("  shape, and one whose cofactor quotient is genuinely nonreal.  What")
    print("  is pinned is the pair of constants (1/2 in the Taylor bound, 3/2")
    print("  after the split, hence K = 3L/||g'(0)||) and the collar")
    print("  b' = min(b, ||g'(0)||/(L+1)); the Lean proof asserts exactly these.")
    print()
    print("ALL PASS")


if __name__ == "__main__":
    main()
