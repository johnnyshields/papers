#!/usr/bin/env python3
r"""Paper section `sec:geometry` (`lem:viewing-angle`, `cor:linear-phase-variation`), the
geometric hypothesis the formalization's crossing-set finiteness rests on.

`ForgacsTran/PhaseTangency.lean` reduces `hstate` -- the finite set containing every
parameter where the tangent angle and the viewing angle differ by an integer multiple of
`pi` -- to ONE condition on the arc: the signed curvature

    wedge(gamma''(theta), gamma'(theta)) = Im( gamma'' conj(gamma') )

does not vanish.  This script measures that condition at the pencil's own principal branch,
checks the polar identity Lean proves for it, and exhibits the two cases the hypothesis has
to exclude.

  (X1) The polar identity.  `gamma = tau e^{i theta}` gives
       `Im(gamma'' conj gamma') = tau^2 + 2 tau'^2 - tau tau''`, which is
       `wedge_ftGammaDeriv2_ftGammaDeriv`.  Checked against `gamma'` and `gamma''` formed
       from `ftTau`, `ftTauDeriv` and `ftTauDeriv2` as the Lean tree defines them, and
       independently against finite differences of `gamma` itself, so the identity is
       tested rather than assumed on both sides.

  (X2) The curvature is POSITIVE on the principal branch, for every admissible pencil
       sampled -- fourteen of them, spanning repeated and separated zeros, spreads of four
       orders of magnitude, and `r` from 1 to 4.  This is the statement `PhaseTangency`
       still carries as a hypothesis; nothing here proves it.

  (X3) **The branch equation is doing the work.**  The curvature has an equivalent
       polynomial form: with `E = t Q' - r Q` and `m = t Q / E`, the branch's curvature is a
       positive multiple of `Im(m'(t))`, and `m' = (sum w_k^2 - r)/(sum w_k - r)^2` with
       `w_k = t/(t - a_k)`.  That quantity is NOT positive throughout the upper half plane,
       so the positivity in (X2) is a fact about the level set `Im(Q/t^r) = 0` and not a
       pointwise fact about the sector.  A finiteness argument that did not use the branch
       equation would therefore be proving something false.

  (X4) The degenerate case the hypothesis excludes: a straight arc through `beta` has a
       tangency function identically zero, so the crossing set is the whole interval.  This
       is `not_finite_tangency_zeros_of_line`.

  (X5) At a parameter where the arc meets `beta` the tangency function has a DOUBLE zero --
       value and derivative both vanish -- with leading coefficient half the curvature.  This
       is why `PhaseTangency` reaches that parameter by two mean values rather than by a
       simple-zero argument, and the measured coefficient confirms the factorization
       `tangency(x) = (x - m)(x - xi) wedge(gamma''(eta), gamma'(xi))`.

mpmath only.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 40

I = mp.mpc(0, 1)


def wedge(u, w):
    """`Im(u conj w)`, the signed area of the parallelogram on `u` and `w`."""
    return mp.im(u * mp.conj(w))


# --------------------------------------------------------------------------
# The general branch, transcribed from `lean/ForgacsTran/FTBranchAngle.lean`,
# `FTBranchFunction.lean`, `FTBranchRegularity.lean` and `BranchCurvature.lean`.
# --------------------------------------------------------------------------

def ft_arccot(x):
    return mp.pi / 2 - mp.atan(x)


def ft_angle(a, tau, s):
    return ft_arccot(mp.cos(s) / mp.sin(s) - a / (tau * mp.sin(s)))


class Branch:
    """The principal branch of one admissible pencil: `Q = prod (t - a_k)`, index `r`,
    `l = n - 1`."""

    def __init__(self, a, r):
        self.a = [mp.mpf(x) for x in a]
        self.r = r
        self.n = len(a)
        self.l = self.n - 1

    # --- the radius, by bisection on the angle sum (`ftAngleSum` is decreasing in tau) ---
    def tau(self, s):
        target = self.r * s + self.l * mp.pi

        def h(x):
            return sum(ft_angle(a, x, s) for a in self.a) - target

        lo, hi = mp.mpf('1e-12'), mp.mpf('1e12')
        assert h(lo) > 0 > h(hi), f"the branch is not bracketed at theta = {mp.nstr(s, 8)}"
        for _ in range(4 * mp.mp.dps):
            mid = (lo + hi) / 2
            if h(mid) > 0:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2

    # --- the first partials and `ftTauDeriv` ---
    def _dtau(self, tau, s):
        return sum(-(mp.sin(ft_angle(a, tau, s)) ** 2 * a / (tau ** 2 * mp.sin(s)))
                   for a in self.a)

    def _dangle(self, tau, s):
        return sum(mp.sin(ft_angle(a, tau, s)) * mp.cos(ft_angle(a, tau, s) - s) / mp.sin(s)
                   for a in self.a)

    def tau_deriv(self, s, tau=None):
        tau = self.tau(s) if tau is None else tau
        return -(self._dangle(tau, s) - self.r) / self._dtau(tau, s)

    # --- the four second partials and `ftTauDeriv2` ---
    @staticmethod
    def _d2_tau(a, tau, s):
        y = ft_angle(a, tau, s)
        return (a * mp.sin(y) ** 2 * (2 * tau * mp.sin(s) + 2 * a * mp.sin(y) * mp.cos(y))
                / (tau ** 4 * mp.sin(s) ** 2))

    @staticmethod
    def _d2_angle_tau(a, tau, s):
        y = ft_angle(a, tau, s)
        return -(mp.sin(y) ** 2 * a / (tau ** 2 * mp.sin(s))) * mp.cos(2 * y - s) / mp.sin(s)

    @staticmethod
    def _d2_tau_angle(a, tau, s):
        y = ft_angle(a, tau, s)
        return -(a / tau ** 2) * ((2 * mp.sin(y) * mp.cos(y)
                                   * (mp.sin(y) * mp.cos(y - s) / mp.sin(s)) * mp.sin(s)
                                   - mp.sin(y) ** 2 * mp.cos(s)) / mp.sin(s) ** 2)

    @staticmethod
    def _d2_angle(a, tau, s):
        y = ft_angle(a, tau, s)
        q = mp.sin(y) * mp.cos(y - s) / mp.sin(s)
        return ((mp.cos(y) * q * mp.cos(y - s) + mp.sin(y) * (-mp.sin(y - s) * (q - 1)))
                * mp.sin(s) - mp.sin(y) * mp.cos(y - s) * mp.cos(s)) / mp.sin(s) ** 2

    def tau_deriv2(self, s, tau=None, td=None):
        tau = self.tau(s) if tau is None else tau
        td = self.tau_deriv(s, tau) if td is None else td
        H = self._dtau(tau, s)
        G = self._dangle(tau, s)
        sdat = sum(self._d2_angle_tau(a, tau, s) for a in self.a)
        sda = sum(self._d2_angle(a, tau, s) for a in self.a)
        sdt = sum(self._d2_tau(a, tau, s) for a in self.a)
        sdta = sum(self._d2_tau_angle(a, tau, s) for a in self.a)
        return (-(sdat * td + sda) * H - -(G - self.r) * (sdt * td + sdta)) / H ** 2

    # --- the branch point and its two derivatives (`ftGammaDeriv`, `ftGammaDeriv2`) ---
    def gamma(self, s):
        return self.tau(s) * mp.expj(s)

    def gamma_deriv(self, s, tau=None, td=None):
        tau = self.tau(s) if tau is None else tau
        td = self.tau_deriv(s, tau) if td is None else td
        return mp.expj(s) * (td + tau * I)

    def gamma_deriv2(self, s, tau=None, td=None, td2=None):
        tau = self.tau(s) if tau is None else tau
        td = self.tau_deriv(s, tau) if td is None else td
        td2 = self.tau_deriv2(s, tau, td) if td2 is None else td2
        return mp.expj(s) * (td2 + 2 * td * I - tau)

    # --- the polynomial route: E = t Q' - r Q, m = t Q / E ---
    def Q(self, t):
        return mp.fprod([t - a for a in self.a])

    def m_prime(self, t):
        w = [t / (t - a) for a in self.a]
        S = sum(w) - self.r
        T = sum(x * x for x in w) - self.r
        return T / (S * S)


PENCILS = [
    ([1, 1, 1], 1, "witness cubic a=(1,1,1), r=1"),
    ([1, 2, 3], 1, "separated a=(1,2,3), r=1"),
    ([1, 1], 1, "double a=(1,1), r=1"),
    ([1, 2], 1, "a=(1,2), r=1"),
    ([1], 2, "a=(1), r=2"),
    ([1, 2, 3], 2, "a=(1,2,3), r=2"),
    ([1, 2, 3, 4], 3, "a=(1,2,3,4), r=3"),
    ([mp.mpf('0.01'), 100], 1, "spread a=(0.01,100), r=1"),
    ([mp.mpf('0.01'), 100, 1], 1, "spread a=(0.01,100,1), r=1"),
    ([1, 1, 1, 1, 1], 4, "a=1^5, r=4"),
    ([1, mp.mpf('1.0001'), 50], 1, "near-double a=(1,1.0001,50), r=1"),
    ([1, 2, 4, 8, 16], 1, "geometric, r=1"),
    ([1, 2, 4, 8, 16], 2, "geometric, r=2"),
    ([1, 2, 4, 8, 16], 4, "geometric, r=4"),
]

SAMPLES = 24


def block1_polar_identity():
    """(X1) `Im(gamma'' conj gamma') = tau^2 + 2 tau'^2 - tau tau''`, both sides built
    independently, and `gamma''` cross-checked against a finite difference of `gamma'`."""
    worst_id = mp.mpf(0)
    worst_fd = mp.mpf(0)
    for a, r, label in PENCILS:
        br = Branch(a, r)
        for k in range(1, SAMPLES):
            s = mp.pi / r * mp.mpf(k) / SAMPLES
            tau = br.tau(s)
            td = br.tau_deriv(s, tau)
            td2 = br.tau_deriv2(s, tau, td)
            lhs = wedge(br.gamma_deriv2(s, tau, td, td2), br.gamma_deriv(s, tau, td))
            rhs = tau ** 2 + 2 * td ** 2 - tau * td2
            worst_id = max(worst_id, abs(lhs - rhs) / abs(rhs))
            # gamma' and gamma'' against finite differences of the branch point itself
            h = mp.mpf('1e-8')
            if h < s < mp.pi / r - h:
                fd1 = (br.gamma(s + h) - br.gamma(s - h)) / (2 * h)
                fd2 = (br.gamma_deriv(s + h) - br.gamma_deriv(s - h)) / (2 * h)
                worst_fd = max(worst_fd,
                               abs(fd1 - br.gamma_deriv(s, tau, td)) / abs(fd1),
                               abs(fd2 - br.gamma_deriv2(s, tau, td, td2)) / abs(fd2))
    assert worst_id < mp.mpf('1e-25'), f"polar curvature identity off by {worst_id}"
    assert worst_fd < mp.mpf('1e-6'), f"gamma' or gamma'' off a finite difference by {worst_fd}"
    print(f"(X1) polar identity          max relative error {mp.nstr(worst_id, 4)}; "
          f"finite-difference check {mp.nstr(worst_fd, 4)}")


def block2_curvature_positive():
    """(X2) The signed curvature is positive on the principal branch of every pencil
    sampled.  This is the hypothesis `PhaseTangency` still carries."""
    overall = None
    for a, r, label in PENCILS:
        br = Branch(a, r)
        vals = []
        for k in range(1, SAMPLES):
            s = mp.pi / r * mp.mpf(k) / SAMPLES
            tau = br.tau(s)
            td = br.tau_deriv(s, tau)
            td2 = br.tau_deriv2(s, tau, td)
            vals.append(tau ** 2 + 2 * td ** 2 - tau * td2)
        lo = min(vals)
        assert lo > 0, f"curvature not positive on {label}: min {mp.nstr(lo, 8)}"
        overall = lo if overall is None or lo < overall else overall
    print(f"(X2) curvature positive      {len(PENCILS)} pencils x {SAMPLES - 1} parameters; "
          f"global minimum {mp.nstr(overall, 6)}")


def block3_branch_equation_is_used():
    """(X3) The curvature is a positive multiple of `Im(m'(t))` along the branch, and
    `Im(m')` changes sign in the upper half plane.  So the positivity of (X2) is a property
    of the level set, not of the sector."""
    # on the branch, the two agree in sign
    mismatch = 0
    for a, r, label in PENCILS:
        br = Branch(a, r)
        for k in range(1, SAMPLES):
            s = mp.pi / r * mp.mpf(k) / SAMPLES
            tau = br.tau(s)
            td = br.tau_deriv(s, tau)
            td2 = br.tau_deriv2(s, tau, td)
            curv = tau ** 2 + 2 * td ** 2 - tau * td2
            mp_val = mp.im(br.m_prime(tau * mp.expj(s)))
            if mp.sign(curv) != mp.sign(mp_val):
                mismatch += 1
    assert mismatch == 0, f"curvature and Im(m') disagree in sign at {mismatch} parameters"
    # off the branch, Im(m') takes both signs inside the upper half plane
    negatives = 0
    br = Branch([1, 1, 1], 1)
    for i in range(1, 60):
        for j in range(1, 60):
            t = mp.mpc(mp.mpf(-6) + mp.mpf(18) * i / 60, mp.mpf(12) * j / 60)
            if any(abs(t - a) < mp.mpf('1e-3') for a in br.a) or abs(t) < mp.mpf('1e-3'):
                continue
            if mp.im(br.m_prime(t)) <= 0:
                negatives += 1
    assert negatives > 0, ("Im(m') never negative on the sampled half plane -- the branch "
                           "equation would then be unnecessary, and the reduction is wrong")
    print(f"(X3) branch equation used    sign agreement on branch at all "
          f"{len(PENCILS) * (SAMPLES - 1)} parameters; "
          f"Im(m') <= 0 at {negatives} sampled points off the branch")


def block4_line_is_degenerate():
    """(X4) A straight arc through `beta` has tangency identically zero."""
    beta = mp.mpc('0.3', '0.7')
    direction = mp.mpc('0.6', '-0.8')
    worst = mp.mpf(0)
    for k in range(-20, 21):
        x = mp.mpf(k) / 7
        gamma = beta + x * direction
        worst = max(worst, abs(wedge(direction, gamma - beta)))
    assert worst < mp.mpf('1e-30'), f"the straight arc has nonzero tangency: {worst}"
    print(f"(X4) straight arc degenerate max |tangency| {mp.nstr(worst, 4)} over 41 parameters")


def block5_double_zero_at_meet():
    """(X5) At a meeting parameter the tangency function has a double zero whose leading
    coefficient is half the curvature; and the two-mean-value factorization reproduces the
    value with both linear factors of one sign."""
    # the unit circle viewed from a point on itself: gamma(x) = e^{ix}, beta = gamma(0) = 1
    def gamma(x):
        return mp.expj(x)

    def dgamma(x):
        return I * mp.expj(x)

    def d2gamma(x):
        return -mp.expj(x)

    beta = mp.mpc(1, 0)
    curv = wedge(d2gamma(mp.mpf(0)), dgamma(mp.mpf(0)))
    assert abs(curv - 1) < mp.mpf('1e-30')

    def tangency(x):
        return wedge(dgamma(x), gamma(x) - beta)

    assert abs(tangency(mp.mpf(0))) < mp.mpf('1e-30'), "the meeting parameter is not a zero"
    h = mp.mpf('1e-10')
    slope = (tangency(h) - tangency(-h)) / (2 * h)
    assert abs(slope) < mp.mpf('1e-9'), f"the meeting zero is simple after all: {slope}"
    worst = mp.mpf(0)
    for k in list(range(-8, 0)) + list(range(1, 9)):
        x = mp.mpf(k) / 40
        worst = max(worst, abs(tangency(x) / (x ** 2) - curv / 2))
    assert worst < mp.mpf('1e-2'), f"leading coefficient is not half the curvature: {worst}"
    # the factorization, with xi and eta produced by the two mean values
    for k in list(range(-8, 0)) + list(range(1, 9)):
        x = mp.mpf(k) / 40
        xi = mp.findroot(lambda u: wedge(dgamma(x), dgamma(u)) - tangency(x) / x,
                         x / 2)
        assert 0 < (x - 0) * (x - xi), "the two linear factors do not share a sign"
    print("(X5) double zero at meeting  value and derivative both vanish; leading "
          f"coefficient within {mp.nstr(worst, 4)} of curvature/2; factorization signs agree")


def block6_trigonometric_normal_form():
    """(X6) The curvature positivity in a form with no complex analysis in it, for whoever
    proves it.  With `phi_k = pi - arg(gamma - a_k)` and `psi = arg(gamma')`, the branch
    equation is `sum_k phi_k = pi - r theta`, the tangent direction is pinned by
    `sum_k sin(phi_k) sin(psi + phi_k) = -r sin(theta) sin(psi - theta)`, and the curvature
    has the sign of

        sum_k sin(phi_k) sin(theta + phi_k) sin(psi + phi_k) cos(psi + phi_k - theta).

    Both constraints and the sign agreement are asserted.  The summands are NOT individually
    positive -- measured negative at 15 of 87 slots on `a = (1,2,3)`, `r = 1` -- so no
    per-root argument reaches it and the inequality is global in `k`."""
    mismatches = 0
    negative_summands = 0
    total_summands = 0
    total = 0
    for a, r, label in PENCILS:
        br = Branch(a, r)
        for k in range(1, SAMPLES):
            s = mp.pi / r * mp.mpf(k) / SAMPLES
            tau = br.tau(s)
            td = br.tau_deriv(s, tau)
            td2 = br.tau_deriv2(s, tau, td)
            curv = tau ** 2 + 2 * td ** 2 - tau * td2
            psi = s + mp.atan2(tau, td)
            phis = [mp.pi - ft_angle(x, tau, s) for x in br.a]
            total += 1
            assert abs(sum(phis) - (mp.pi - r * s)) < mp.mpf('1e-25'), \
                f"the branch equation sum phi_k = pi - r theta fails on {label}"
            pin = (sum(mp.sin(p) * mp.sin(psi + p) for p in phis)
                   + r * mp.sin(s) * mp.sin(psi - s))
            assert abs(pin) < mp.mpf('1e-20'), \
                f"the tangent direction is not pinned as stated on {label}: {pin}"
            terms = [mp.sin(p) * mp.sin(s + p) * mp.sin(psi + p) * mp.cos(psi + p - s)
                     for p in phis]
            total_summands += len(terms)
            negative_summands += sum(1 for t in terms if t <= 0)
            if mp.sign(sum(terms)) != mp.sign(curv) or sum(terms) <= 0:
                mismatches += 1
    assert mismatches == 0, f"normal form disagrees with the curvature at {mismatches} parameters"
    assert negative_summands > 0, ("every summand positive on the sample -- a per-root "
                                   "argument would then suffice and this note is wrong")
    print(f"(X6) trigonometric form      both constraints and the sign agree at all {total} "
          f"parameters; {negative_summands}/{total_summands} summands are negative, so the "
          f"inequality is global in k")


def block7_two_moment_reduction():
    """(X7) The curvature as a two-moment statement, which is what a proof has to attack.

    Put `z_k = gamma'/(gamma - a_k)` for the zeros of `Q` and `z_0 = gamma'/gamma` for the
    pole.  All `n+1` of them lie on ONE circle through the origin, `{gamma'/(gamma - x) :
    x real}`.  Two facts then carry everything:

        constraint   sum_k Im z_k = r Im z_0        (the branch equation)
        goal         sum_k Im z_k (Re z_k - Re z_0) > 0   (the curvature)

    and `Im z_k` is `d theta_k / d theta`, the rate at which the zero `a_k` sees `gamma`
    turn.  Asserted here: the constraint, the sign agreement of the goal with the curvature,
    and `Re z_k > Re z_0` for every zero -- the sub-lemma that would finish the proof if the
    weights `Im z_k` were positive.  **They are not**, and that is asserted too, because it
    is what rules out the convex-combination argument the shape invites."""
    neg_weight = 0
    total_slots = 0
    total = 0
    for a, r, label in PENCILS:
        br = Branch(a, r)
        for k in range(1, SAMPLES):
            s = mp.pi / r * mp.mpf(k) / SAMPLES
            tau = br.tau(s)
            td = br.tau_deriv(s, tau)
            td2 = br.tau_deriv2(s, tau, td)
            curv = tau ** 2 + 2 * td ** 2 - tau * td2
            gamma = tau * mp.expj(s)
            dgamma = br.gamma_deriv(s, tau, td)
            z = [dgamma / (gamma - x) for x in br.a]
            z0 = dgamma / gamma
            total += 1
            assert abs(mp.im(z0) - 1) < mp.mpf('1e-25'), \
                f"the parametrization is not by arg gamma on {label}"
            c = sum(mp.im(w) for w in z) - r * mp.im(z0)
            assert abs(c) < mp.mpf('1e-20'), \
                f"the branch/tangent constraint fails on {label}: {mp.nstr(c, 8)}"
            goal = sum(mp.im(w) * (mp.re(w) - mp.re(z0)) for w in z)
            assert mp.sign(goal) == mp.sign(curv), \
                f"the two-moment goal disagrees with the curvature on {label}"
            for w in z:
                total_slots += 1
                assert mp.re(w) > mp.re(z0), \
                    f"Re z_k <= Re z_0 on {label} -- the sub-lemma is false"
                if mp.im(w) <= 0:
                    neg_weight += 1
    assert neg_weight > 0, ("every weight Im z_k positive on the sample -- the goal would "
                            "then be a convex combination and this note is wrong")
    print(f"(X7) two-moment reduction    constraint and sign agree at all {total} parameters; "
          f"Re z_k > Re z_0 at all {total_slots} slots; Im z_k <= 0 at {neg_weight} of them, "
          f"so the goal is not a convex combination")


def block8_radius_antitone():
    """(X8) `tau' <= 0`, the half of the curvature that IS proved.

    `ForgacsTran/BranchRadiusMonotone.lean` proves `ftTauDeriv <= 0` for `n <= 2r` by an
    inscribed polygon: with `phi_k = pi - theta_k`, the `n` arcs `theta + 2 phi_k` and
    `2r - n` copies of `theta` are nonnegative and sum to exactly `2 pi`, so their sine sum
    is twice the area of the polygon they cut out.  Three assertions: the partition is a
    partition, the polygon lemma holds on random exact partitions, and `tau' <= 0` on the
    branch itself -- measured directly, since the reduction from `tau'` to the angle sum is
    what a slip would hide."""
    import random
    random.seed(17)
    # the polygon lemma, on exact partitions of 2 pi
    worst_poly = None
    for _ in range(4000):
        N = random.randint(1, 9)
        w = [mp.mpf(random.randint(1, 10 ** 6)) for _ in range(N)]
        sw = sum(w)
        arcs = [2 * mp.pi * x / sw for x in w]
        v = sum(mp.sin(x) for x in arcs)
        if worst_poly is None or v < worst_poly:
            worst_poly = v
    assert worst_poly > -mp.mpf('1e-30'), f"polygon lemma violated: {worst_poly}"
    # the partition the branch equation produces, and tau' <= 0, on the branch
    worst_tau = None
    worst_part = mp.mpf(0)
    checked = 0
    for a, r, label in PENCILS:
        br = Branch(a, r)
        n = br.n
        for k in range(1, SAMPLES):
            s = mp.pi / r * mp.mpf(k) / SAMPLES
            tau = br.tau(s)
            td = br.tau_deriv(s, tau)
            assert td <= mp.mpf('1e-25'), \
                f"tau' > 0 on {label} at theta = {mp.nstr(s, 8)}: {mp.nstr(td, 8)}"
            if worst_tau is None or td > worst_tau:
                worst_tau = td
            if n <= 2 * r:
                phis = [mp.pi - ft_angle(x, tau, s) for x in br.a]
                arcs = [s + 2 * p for p in phis] + [s] * (2 * r - n)
                worst_part = max(worst_part, abs(sum(arcs) - 2 * mp.pi))
                assert all(x >= 0 for x in arcs), f"a reflected arc is negative on {label}"
                assert sum(mp.sin(x) for x in arcs) > -mp.mpf('1e-25'), \
                    f"the reflected arcs have negative sine sum on {label}"
                checked += 1
    print(f"(X8) radius antitone         tau' <= 0 at every branch parameter, max "
          f"{mp.nstr(worst_tau, 4)}; polygon lemma min {mp.nstr(worst_poly, 4)} over 4000 "
          f"exact partitions; the n <= 2r arcs sum to 2pi to {mp.nstr(worst_part, 4)} at "
          f"{checked} parameters")


def block9_cotangent_chart():
    """(X9) The curvature as a CONVEXITY, and the elementary inequality both routes reach.

    `check_curvature_reduction.py` reduces `K` to `(c' sin^2 theta)' != 0` with
    `c = cot beta` for a root `beta`.  That reduction goes one step further and becomes a
    genuine convexity statement, which is asserted here:

      * `c' sin^2(theta) = a_k G - 1` with `G = Im(gamma')/tau^2`, **for every root a_k** --
        so the per-root condition does not depend on which root is chosen, and the root
        drops out entirely.  Asserted for all roots, since a reduction stated at one
        distinguished root invites the reader to think the choice matters.
      * `G = dR/ds` where `s = cot(theta)` and `R = 1/Im(gamma) = 1/(tau sin theta)`, and
        `d^2 R/ds^2 = K sin^3(theta)/tau^3`.  So on the arc

            K > 0   <=>   R is STRICTLY CONVEX as a function of s = cot(theta).

        That is the convexity the curvature is; convexity of `1/tau` in `theta` is a
        different and false statement, and this block asserts the two disagree.
      * Implicit second differentiation of the branch equation in the chart -- where it
        reads `cot(theta_k) = s - a_k R` -- turns that convexity into

            sum_k (theta_k')^2 cot(theta_k)  <  r cot(theta),   given  sum_k theta_k' = r.

        The same inequality is reached independently through the circle geometry of block
        X7, by a route sharing no step with this one.  Both are asserted against the sign
        of `K`.

    Also measured, because they kill the two cheap ways to finish: `theta_k'` is **not**
    bounded by 1, and `sum_k (theta_k')^2` **exceeds** `r`.  Either would close the
    inequality against `cot(theta_k) < cot(theta)`; neither holds."""
    max_tk = None
    sq_over = 0
    total = 0
    worst_conv = None
    for a, r, label in PENCILS:
        br = Branch(a, r)
        for j in range(1, SAMPLES):
            th = mp.pi / r * mp.mpf(j) / SAMPLES
            tau = br.tau(th)
            td = br.tau_deriv(th, tau)
            td2 = br.tau_deriv2(th, tau, td)
            K = tau ** 2 + 2 * td ** 2 - tau * td2
            gamma = tau * mp.expj(th)
            dgamma = br.gamma_deriv(th, tau, td)
            G = mp.im(dgamma) / tau ** 2
            total += 1
            # the per-root condition is root-independent
            for x in br.a:
                # a plain central difference: `mp.diff` raises the working precision, and
                # every evaluation here runs a bisection, so the adaptive version is far
                # slower than the accuracy this identity needs
                c_of = lambda t: (mp.cos(t) - x / br.tau(t)) / mp.sin(t)
                hh = mp.mpf('1e-8')
                cp = (c_of(th + hh) - c_of(th - hh)) / (2 * hh)
                lhs = cp * mp.sin(th) ** 2
                assert abs(lhs - (x * G - 1)) < mp.mpf('1e-8') * max(1, abs(lhs)), \
                    f"c' sin^2(theta) != a_k G - 1 on {label} at root {x}"
            # G is dR/ds, and R is convex in s exactly where K > 0
            R_of_s = lambda sv: 1 / (br.tau(mp.pi / 2 - mp.atan(sv)) * mp.sin(mp.pi / 2 - mp.atan(sv)))
            sv = mp.cos(th) / mp.sin(th)
            h = mp.mpf('1e-6') * max(1, abs(sv))
            R1 = (R_of_s(sv + h) - R_of_s(sv - h)) / (2 * h)
            R2 = (R_of_s(sv + h) - 2 * R_of_s(sv) + R_of_s(sv - h)) / h ** 2
            assert abs(R1 - G) < mp.mpf('1e-6') * max(1, abs(G)), \
                f"dR/ds != Im(gamma')/tau^2 on {label}"
            pred = K * mp.sin(th) ** 3 / tau ** 3
            rel = abs(R2 - pred) / max(1, abs(pred))
            assert rel < mp.mpf('1e-4'), f"d2R/ds2 != K sin^3/tau^3 on {label}: {rel}"
            assert R2 > 0, f"R is not convex in s on {label}, where K = {mp.nstr(K, 8)}"
            if worst_conv is None or R2 < worst_conv:
                worst_conv = R2
            # the elementary inequality, against the sign of K
            tk = [mp.im(dgamma / (gamma - x)) for x in br.a]
            assert abs(sum(tk) - r) < mp.mpf('1e-20'), f"sum theta_k' != r on {label}"
            lhs = sum(t * t * mp.cos(ang) / mp.sin(ang)
                      for t, ang in zip(tk, [ft_angle(x, tau, th) for x in br.a]))
            rhs = r * mp.cos(th) / mp.sin(th)
            assert mp.sign(rhs - lhs) == mp.sign(K), \
                f"the elementary inequality disagrees with K on {label}"
            m = max(tk)
            if max_tk is None or m > max_tk:
                max_tk = m
            if sum(t * t for t in tk) > r:
                sq_over += 1
    assert max_tk > 1, "theta_k' <= 1 throughout -- then the inequality closes cheaply"
    assert sq_over > 0, "sum (theta_k')^2 <= r throughout -- then it closes cheaply"
    print(f"(X9) cotangent chart         root-independent at every root; R convex in "
          f"s = cot(theta) at all {total} parameters, min d2R/ds2 = "
          f"{mp.nstr(worst_conv, 4)}; elementary inequality agrees with K everywhere; "
          f"max theta_k' = {mp.nstr(max_tk, 5)} > 1 and sum(theta_k')^2 > r at {sq_over} "
          f"parameters, so neither cheap closure is available")


def block10_weights_are_samples():
    """(X10) How much smaller the feasible set is than `{sum_k w_k = r}` -- and that the
    coupling alone is still not enough.

    In the cotangent chart of X9, write `s = cot(theta)`, `c_k = cot(theta_k)`, and
    `g = R'/R`.  Then the weights are **not free**: every one of them is a sample of ONE
    rational function,

        w_k = W(c_k),    W(c) = (1 + s^2)(1 - (s - c) g)/(1 + c^2),    W(s) = 1,

    linear over quadratic, fixed by the two scalars `s` and `g`.  So all `n+1` pairs
    `(c_k, w_k)` lie on a single curve, where every refuted approach treated `w` as an
    arbitrary point of the hyperplane `sum_k w_k = r` at given `c`.  Asserted at every
    branch parameter and every root.

    **But the coupling is not the missing ingredient.**  Sampling `s` and `c_k < s` freely,
    fixing `g` by `sum_k W(c_k) = r` -- so the functional form and the linear constraint both
    hold -- the target inequality FAILS.  Only the branch equation
    `sum_k arccot(c_k) = r arccot(s) + (n-1) pi` excludes those configurations, and this
    block asserts that failures exist, so the point cannot be lost."""
    import random
    total_slots = 0
    worst = mp.mpf(0)
    for a, r, label in PENCILS:
        br = Branch(a, r)
        for j in range(1, SAMPLES):
            th = mp.pi / r * mp.mpf(j) / SAMPLES
            tau = br.tau(th)
            td = br.tau_deriv(th, tau)
            gamma = tau * mp.expj(th)
            dgamma = br.gamma_deriv(th, tau, td)
            sv = mp.cos(th) / mp.sin(th)
            Rv = 1 / (tau * mp.sin(th))
            g = (mp.im(dgamma) / tau ** 2) / Rv
            W = lambda c: (1 + sv ** 2) * (1 - (sv - c) * g) / (1 + c ** 2)
            for x in br.a:
                ang = ft_angle(x, tau, th)
                c = mp.cos(ang) / mp.sin(ang)
                w = mp.im(dgamma / (gamma - x))
                total_slots += 1
                worst = max(worst, abs(W(c) - w) / max(1, abs(w)))
            worst = max(worst, abs(W(sv) - 1))
    assert worst < mp.mpf('1e-20'), f"the weights are not samples of W: {mp.nstr(worst, 6)}"
    # the same functional form plus the linear constraint, but OFF the branch
    random.seed(29)
    off_fail = 0
    off_tot = 0
    for _ in range(20000):
        n = random.randint(2, 5)
        r = random.randint(1, 4)
        sv = mp.mpf(random.uniform(-4, 4))
        c = [mp.mpf(sv - random.uniform(0.05, 8)) for _ in range(n)]
        S = [1 / (1 + x ** 2) for x in c]
        S0 = 1 / (1 + sv ** 2)
        den = sum((sv - x) * y for x, y in zip(c, S))
        if abs(den) < mp.mpf('1e-6'):
            continue
        g = (sum(S) - r * S0) / den
        W = lambda x: (1 + sv ** 2) * (1 - (sv - x) * g) / (1 + x ** 2)
        if abs(sum(W(x) for x in c) - r) > mp.mpf('1e-12'):
            continue
        off_tot += 1
        if sum(W(x) ** 2 * x for x in c) >= r * sv:
            off_fail += 1
    assert off_fail > 0, ("the inequality survives the functional coupling alone -- then the "
                          "branch equation would be unnecessary and this note is wrong")
    print(f"(X10) weights are samples    w_k = W(c_k) to {mp.nstr(worst, 4)} at all "
          f"{total_slots} slots, W(s) = 1; with the coupling but WITHOUT the branch "
          f"equation the inequality fails at {off_fail} of {off_tot} sampled configurations")


def block11_critical_value_split():
    """(X11) The target splits into a free trigonometric inequality and a deviation term.

    Extremizing `sum_k w_k^2 cot(theta_k)` over `{sum_k w_k = r}` with the positions held
    fixed gives `w_k = (r/S) tan(theta_k)` with `S = sum_k tan(theta_k)`, and critical value
    `r^2/S`.  Writing the true weights as that critical point plus a deviation
    `delta_k = w_k - (r/S) tan(theta_k)`, which sums to zero, the cross term cancels
    identically (`tan^2 cot = tan` and `tan cot = 1`) and

        sum_k w_k^2 cot(theta_k)  =  r^2/S  +  sum_k delta_k^2 cot(theta_k).

    So the target `sum_k w_k^2 cot(theta_k) < r cot(theta)` splits as

        (i)   sum_k delta_k^2 cot(theta_k) <= 0     -- about the deviation
        (ii)  r/S < cot(theta)                      -- a SCALAR inequality, no sum in it

    and (ii) carries **no derivatives at all**: it is a statement about the angles alone,
    under `sum_k theta_k = r theta + (n-1) pi`.  Asserted here on the branch, together with
    the identity, the split, and the structural fact that **at most one `theta_k` lies below
    `pi/2`** -- if two did, `sum_k theta_k < (n-1) pi`, contradicting the branch equation.
    So at most one `cot(theta_k)` is positive, which is what gives (i) a chance.

    `delta = 0` exactly when `w_k cot(theta_k)` is constant in `k`, which is the Lagrange
    condition; it holds at `n = 2` and when all roots coincide, and fails otherwise -- so
    (i) is an equality in those cases and the whole target is (ii) there.

    **(ii) is proved**, in `ForgacsTran/BranchTangentSum.lean`, as
    `T (T cot(theta) + r) > 0` for `T = sum_k tan(phi_k) = -S`; the two forms are asserted
    equal here, since that translation is where a slip would sit."""
    worst_i = None
    worst_ii = None
    worst_id = mp.mpf(0)
    max_below = 0
    zero_dev = 0
    total = 0
    lean_checked = 0
    for a, r, label in PENCILS:
        br = Branch(a, r)
        for j in range(1, SAMPLES):
            th = mp.pi / r * mp.mpf(j) / SAMPLES
            tau = br.tau(th)
            td = br.tau_deriv(th, tau)
            gamma = tau * mp.expj(th)
            dgamma = br.gamma_deriv(th, tau, td)
            angs = [ft_angle(x, tau, th) for x in br.a]
            w = [mp.im(dgamma / (gamma - x)) for x in br.a]
            cot = [mp.cos(x) / mp.sin(x) for x in angs]
            tanv = [mp.sin(x) / mp.cos(x) for x in angs]
            S = sum(tanv)
            total += 1
            max_below = max(max_below, sum(1 for x in angs if x < mp.pi / 2))
            lhs = sum(wi * wi * c for wi, c in zip(w, cot))
            dev = [wi - (r / S) * t for wi, t in zip(w, tanv)]
            assert abs(sum(dev)) < mp.mpf('1e-18'), f"the deviation does not sum to zero on {label}"
            quad = sum(d * d * c for d, c in zip(dev, cot))
            worst_id = max(worst_id, abs(lhs - (r * r / S + quad)) / max(1, abs(lhs)))
            if max(abs(d) for d in dev) < mp.mpf('1e-18'):
                zero_dev += 1
            assert quad <= mp.mpf('1e-20'), f"(i) fails on {label}: {mp.nstr(quad, 8)}"
            d2 = r / S - mp.cos(th) / mp.sin(th)
            assert d2 < 0, f"(ii) fails on {label}: {mp.nstr(d2, 8)}"
            # the Lean form, in the reflected angles phi_k = pi - theta_k.  Recomputing
            # the sum through `tan(pi - theta_k)` is ill-conditioned when a branch angle
            # sits near pi/2, where both tangents blow up, so that comparison is made only
            # where it means anything; the sign check is made everywhere.
            if max(abs(t) for t in tanv) < mp.mpf('1e10'):
                Tt = sum(mp.tan(mp.pi - x) for x in angs)
                assert abs(Tt + S) < mp.mpf('1e-18') * max(1, abs(S)), f"T != -S on {label}"
                lean_checked += 1
            Tt = -S
            assert Tt * (Tt * (mp.cos(th) / mp.sin(th)) + r) > 0, (
                f"the Lean form of (ii) disagrees on {label}")
            if worst_i is None or quad > worst_i:
                worst_i = quad
            if worst_ii is None or d2 > worst_ii:
                worst_ii = d2
    assert max_below <= 1, "two branch angles below pi/2 -- the branch equation forbids it"
    assert zero_dev > 0 and zero_dev < total, \
        "the deviation is everywhere zero or nowhere zero -- neither matches the n = 2 split"
    print(f"(X11) critical-value split   identity to {mp.nstr(worst_id, 4)}; (i) holds with "
          f"max {mp.nstr(worst_i, 4)}, (ii) with max {mp.nstr(worst_ii, 4)}, at all {total} "
          f"parameters; at most {max_below} angle below pi/2; deviation vanishes at "
          f"{zero_dev} of {total} (the n = 2 and repeated-root cases); the Lean form "
          f"T = -S cross-checked at {lean_checked} well-conditioned parameters")


def block12_deviation_term():
    """(X12) (i) closes, and the curvature inequality with it.

    (i) asks `sum_k delta_k^2 cot(theta_k) <= 0` for the deviation `delta` of the true
    weights from the critical point, which sums to zero.  It follows from the POSITIONS
    alone -- the weights never enter:

      * at most one `theta_k` lies below `pi/2`, so at most one `cot(theta_k)` is positive;
      * when one does, `S = sum_k tan(theta_k) > 0`, which is case B of
        `ForgacsTran/BranchTangentSum.lean`;
      * and `c_j * sum_{k != j} 1/|c_k| = cot(theta_j) * sum_{k != j} (-tan theta_k) <= 1`
        is **equivalent** to `S >= 0`, which is exactly the Cauchy-Schwarz condition:
        with `delta_j = -sum_{k != j} delta_k`,
            `delta_j^2 <= (sum_{k != j} |c_k| delta_k^2)(sum_{k != j} 1/|c_k|)`,
        so `c_j delta_j^2 <= sum_{k != j} |c_k| delta_k^2` and the form is nonpositive.

    So the form is negative semidefinite on `{sum delta = 0}` for EVERY zero-sum deviation,
    not merely the one the branch produces.  Asserted three ways: the two cases occur, the
    Cauchy-Schwarz condition holds, and the exact maximum of the form over `{sum delta = 0}`
    is nonpositive -- computed over all two-index directions, which is where the maximum
    sits when at most one weight is positive, plus random directions.

    With (ii) proved this closes `sum_k w_k^2 cot(theta_k) < r cot(theta)`, hence `K > 0`.
    What is not yet formalized is the ASSEMBLY: the reduction of `wedge(gamma'', gamma')` to
    `sum_k w_k^2 cot(theta_k)` through the chart, which blocks X7, X9 and X11 assert but no
    Lean theorem yet carries."""
    import random
    random.seed(2024)
    case1 = case2 = 0
    worst_cond = None
    worst_form = None
    total = 0
    for a, r, label in PENCILS:
        br = Branch(a, r)
        for jj in range(1, SAMPLES):
            th = mp.pi / r * mp.mpf(jj) / SAMPLES
            tau = br.tau(th)
            td = br.tau_deriv(th, tau)
            gamma = tau * mp.expj(th)
            dgamma = br.gamma_deriv(th, tau, td)
            angs = [ft_angle(x, tau, th) for x in br.a]
            w = [mp.im(dgamma / (gamma - x)) for x in br.a]
            cot = [mp.cos(x) / mp.sin(x) for x in angs]
            tanv = [mp.sin(x) / mp.cos(x) for x in angs]
            S = sum(tanv)
            n = br.n
            total += 1
            pos = [i for i, c in enumerate(cot) if c > 0]
            assert len(pos) <= 1, f"two positive cotangents on {label}"
            if not pos:
                case1 += 1
            else:
                case2 += 1
                j = pos[0]
                assert S > 0, f"a positive cotangent without S > 0 on {label}"
                cond = cot[j] * sum(-tanv[i] for i in range(n) if i != j)
                assert cond <= 1 + mp.mpf('1e-25'), \
                    f"the Cauchy-Schwarz condition fails on {label}: {mp.nstr(cond, 8)}"
                if worst_cond is None or cond > worst_cond:
                    worst_cond = cond
            # the exact maximum of the form on {sum delta = 0}
            best = mp.mpf(0)
            for i1 in range(n):
                for i2 in range(i1 + 1, n):
                    best = max(best, cot[i1] + cot[i2])
            for _ in range(12):
                d = [mp.mpf(random.gauss(0, 1)) for _ in range(n)]
                m = sum(d) / n
                d = [x - m for x in d]
                nrm = sum(x * x for x in d)
                if nrm > 0:
                    best = max(best, sum(x * x * c for x, c in zip(d, cot)) / nrm)
            assert best <= mp.mpf('1e-25'), \
                f"the deviation form is positive in some direction on {label}"
            if worst_form is None or best > worst_form:
                worst_form = best
            # and the target itself, which (i) and (ii) now give
            lhs = sum(wi * wi * c for wi, c in zip(w, cot))
            assert lhs < r * mp.cos(th) / mp.sin(th), f"the target fails on {label}"
    assert case1 > 0 and case2 > 0, "only one of the two cases occurs on the sample"
    print(f"(X12) deviation term         both cases occur ({case1} with every cotangent "
          f"nonpositive, {case2} with one positive); Cauchy-Schwarz condition max "
          f"{mp.nstr(worst_cond, 4)} <= 1; the form's exact maximum over zero-sum directions "
          f"is {mp.nstr(worst_form, 4)} <= 0 at all {total} parameters")


def block13_second_derivative_bounds():
    """(X13) What the curvature says about `tau''`, and the one half that is missing.

    `K > 0` divided by `tau > 0` is `tau'' < tau + 2 tau'^2/tau` -- an upper bound on the
    second derivative, general and free, formalized as `ftTauDeriv2_lt`.

    The matching LOWER bound is equivalent to `vartheta' = K/(tau^2 + tau'^2) < r + 1`, which
    in the tangent-angle reading is `sum_j psi_j' > 0` over the REAL roots of
    `E = t Q' - r Q`.  Asserted here and **not proved**: `ftTauDeriv2_gt_of_curvature_lt`
    carries it as a hypothesis.

    Also measured, because it is the finding that would matter more than the bound: `tau''`
    does **not** run to `-infinity` at either end.  It converges to a finite limit -- at the
    witness cubic to `7/9` as `theta -> 0`, which is what the cluster expansion gives by an
    independent route, and is NOT `ftTauDeriv2 a r l 0`, a vanishing-denominator artifact
    equal to `0`.  That convergence is now a theorem at a repeated smallest zero,
    `EndpointTauDeriv2.exists_tendsto_ftTauDeriv2`; the assertion here is written so that an
    unbounded `tau''` would FAIL it."""
    worst_vth = None
    worst_slack = None
    total = 0
    for a, r, label in PENCILS:
        br = Branch(a, r)
        for j in range(1, SAMPLES):
            th = mp.pi / r * mp.mpf(j) / SAMPLES
            tau = br.tau(th)
            td = br.tau_deriv(th, tau)
            td2 = br.tau_deriv2(th, tau, td)
            K = tau ** 2 + 2 * td ** 2 - tau * td2
            total += 1
            # the free upper bound
            assert td2 < tau + 2 * td ** 2 / tau, f"the curvature's upper bound fails on {label}"
            # the conjectured ceiling on the tangent-angle derivative
            vth = K / (tau ** 2 + td ** 2)
            assert vth < r + 1, f"vartheta' >= r+1 on {label}: {mp.nstr(vth, 8)}"
            if worst_vth is None or (r + 1) - vth < worst_vth[0]:
                worst_vth = ((r + 1) - vth, label)
            # and the lower bound it would give
            lb = -r * tau - (r - 1) * td ** 2 / tau
            assert lb < td2, f"the derived lower bound fails on {label}"
            if worst_slack is None or td2 - lb < worst_slack:
                worst_slack = td2 - lb
    # tau'' has a finite limit at the collision end, not a pole
    for a, r, label in PENCILS[:6]:
        br = Branch(a, r)
        vals = []
        for e in ['1e-3', '1e-4', '1e-5', '1e-6']:
            th = mp.pi / r * mp.mpf(e)
            tau = br.tau(th)
            td = br.tau_deriv(th, tau)
            vals.append(br.tau_deriv2(th, tau, td))
        # the approach is linear in theta, so the test is that consecutive values are
        # SETTLING -- comparing the whole range would only measure the coarsest point
        step = abs(vals[-1] - vals[-2])
        assert step < mp.mpf('1e-3') * max(1, abs(vals[-1])), (
            f"tau'' is not settling to a limit at the collision on {label}: "
            f"{[mp.nstr(v, 6) for v in vals]}")
    print(f"(X13) second derivative      upper bound holds at all {total} parameters; "
          f"vartheta' < r+1 with least slack {mp.nstr(worst_vth[0], 4)} ({worst_vth[1]}); "
          f"derived lower bound holds with least slack {mp.nstr(worst_slack, 4)}; "
          f"tau'' settles to a finite limit at the collision on 6 pencils")


def main():
    print("check_branch_convexity.py -- the curvature hypothesis of "
          "ForgacsTran/PhaseTangency.lean")
    block1_polar_identity()
    block2_curvature_positive()
    block3_branch_equation_is_used()
    block4_line_is_degenerate()
    block5_double_zero_at_meet()
    block6_trigonometric_normal_form()
    block7_two_moment_reduction()
    block8_radius_antitone()
    block9_cotangent_chart()
    block10_weights_are_samples()
    block11_critical_value_split()
    block12_deviation_term()
    block13_second_derivative_bounds()
    print("ALL PASS")


if __name__ == "__main__":
    main()
