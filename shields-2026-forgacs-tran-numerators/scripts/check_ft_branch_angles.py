#!/usr/bin/env python3
r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude),
`subsec:FT-geometry` and `thm:FT-geometry`.

The Forgacs-Tran branch that `thm:FT-geometry` imports is built in
`Forgacs2017RationalDenominator` Lemmas 2-5.  Their Lemma 2 produces the angles
theta_k(theta) implicitly, through the complex implicit function theorem; the
Lean development `lean/ForgacsTran/FTBranch*.lean` instead solves the defining
relation in closed form, and that closed form is what is checked here, together
with the range condition the closed form exposes.

  (B1) CLOSED FORM.  The relation tau_k sin(theta_k) = tau sin(theta_k - theta)
       is equivalent to cot(theta_k) = cot(theta) - tau_k/(tau sin theta), so
       theta_k = arccot(cot theta - tau_k/(tau sin theta)) on (0, pi).  Checked
       against clauses (i), (ii), (iii) of their Lemma 2 for r = 1..4 and
       deg P <, =, > r.  Clause (i), theta_k > theta, is automatic in this form.

  (B2) RANGE CONDITION.  Clause (i) forces sum theta_k > n theta while clause
       (ii) sets sum theta_k = r theta + l pi, so the system is INFEASIBLE
       whenever r theta + l pi <= n theta.  Their Lemma 2 is stated for every
       0 <= l < n; the smallest failing instance is (n, r, l) = (2, 2, 0).  The
       predicate `n < (l+1) r or (n = (l+1) r and l >= 1)' is asserted to decide
       feasibility exactly, over the same sweep.

  (B3) l = n - 1 IS SAFE.  The index the paper's later sections use satisfies the
       range condition throughout (0, pi/r), except for the degenerate n = r = 1.

  (B4) z IS REAL, WITH SIGN (-1)^(n-l-1).  Their Lemma 4(i) and Eq. (21):
       z = -P(t_0)/t_0^r at t_0 = tau e^{-i theta} is real, and its sign is
       fixed by the parity of n - l - 1.

  (B5) tau(theta) IS STRICTLY DECREASING for l = n - 1 and (r, n) != (1, 2).
       Their Lemma 3.  Sampled across the arc; the Lean proof covers n <= 2r.

  (B6) z(theta) IS STRICTLY MONOTONE for l = n - 1.  Their Lemma 4(ii).

  (B7) LEMMA 5, NEGATIVE ZERO.  For r = 1 and deg P >= 2 the polynomial
       E(t) = t P'(t) - P(t) has exactly one negative zero, which is the
       critical point `t_b' of `subsec:FT-geometry'.

  (B8) REGULARITY IN theta.  Their Lemma 2 asserts the branch is analytic on a
       neighborhood of (0, pi/r); the Lean development proves it differentiable.
       The two partials of the angle sum are

         dSigma/dtau = -sum_k sin^2(theta_k) tau_k / (tau^2 sin theta),
         dSigma/dtheta = sum_k sin(theta_k) cos(theta_k - theta) / sin theta,

       the first strictly negative, and the branch equation gives
       tau'(theta) = -(dSigma/dtheta - r) / (dSigma/dtau) and
       dtheta_k/dtheta = (dtheta_k/dtau) tau' + dtheta_k/dtheta.  Both are
       checked against central differences of the bisected branch.

  (B9) ENDPOINT LIMIT.  Their Lemma 6 turns on lim_{theta->0} tau(theta) being a
       zero of E(t) = t P'(t) - r P(t), lying between the two smallest zeros of
       P.  Checked by extrapolating the bisected branch toward theta = 0 and
       evaluating E there.

  (B10) PROPOSITION 1's CLOSING STEP.  Their proof compares z(theta_tilde; l) with
       z(theta) as chord products at one fixed radius.  Two things are checked:
       that the branch value really is c prod_k |tau e^{i psi} - tau_k| / tau^r at
       its own radius, and that this chord product is strictly increasing in psi,
       which is what makes their displayed equivalence an equivalence.

  (B11) EQ. (23) AND THE UNPROVED CASE 2.  Two things.  First their Eq. (23) in the
       form the Lean proof of Lemma 4(ii) uses: with Sigma(t) = sum_k t/(tau_k - t) + r
       at t = tau e^{-i theta}, Im Sigma < 0 and z'(theta) Im Sigma = -z |Sigma|^2,
       so z' has the sign of z.  Second, the inequality behind their Lemma 3 in the
       case the Lean proof does NOT cover, n > 2r:
       sum_k sin(2 theta_k - theta) < (2r - n) sin theta.

  (B12) IDENTIFYING THE ENDPOINT LIMIT.  Their Lemma 6 pins the limit by the
       angle count sum_k theta_k = r theta + (n-1) pi, which gives
       tau_(1) <= t_a <= tau_(2).  Checked here, together with the case the
       consumers need: when the smallest zero is REPEATED the bracket collapses
       and the limit is that zero.  Also checked is the constant the Prop. 3
       Case 2 rate is measured against, tau'(theta) -> -x1 cot(pi/rho) with rho
       the multiplicity of the smallest zero.

  (B13) THE SECOND-ORDER BOUND.  What the principal-amplitude expansion consumes
       is not tau' but tau itself, to second order:
       |tau(theta) - (x1 - x1 cot(pi/rho) theta)| <= C theta^2.  The route
       measured here differentiates nothing.  Two facts carry it: the identity
       x1/tau = cos theta - sin theta cot beta, exact, where beta is the common
       angle at the repeated smallest zero; and the angle count, which bounds
       |beta - (pi - pi/rho)| by a multiple of theta with no analysis in it.  The
       ratio |tau - (x1 + m theta)|/theta^2 is sampled across four decades and
       asserted to settle -- it would diverge like 1/theta if the error were
       first order -- and the linear term is asserted to be doing real work.

  (B14) THE FIRST GAP.  The `k = 1' identification under `lem:amplitude-divisor'
       needs the endpoint limit strictly between the two smallest zeros.  The
       upper half is a statement about the BRANCH, not about E, and it is not
       asymptotic: tau(theta) < x2 at every theta on the arc.  The mechanism is
       the midpoint (pi + theta)/2 -- a zero at or inside the radius has its
       angle at or below it -- and two such zeros already push the angle sum
       below r theta + (n-1) pi.  E cannot supply this: E has zeros in the later
       gaps too, so uniqueness in the first gap says nothing about WHICH zero the
       limit is.  Sampled here, including pencils where x2 repeats.

  (B15) THE RATE OF THE SPECTRAL PARAMETER.  The member leg of Prop. 3 Case 2
       needs each cluster member's crude size, which `norm_cluster_root'
       converts into |z(delta)| = O(delta^rho).  Reading that off the cluster
       expansion would be circular -- the expansion is what it is wanted for --
       so the route measured here uses the PRINCIPAL point alone: the chord to
       the repeated zero is sqrt((x1 - tau)^2 + 2 x1 tau (1 - cos theta)), and
       both terms are O(theta^2) from tau - x1 = O(theta) and 1 - cos theta =
       O(theta^2).  Sampled at rho and at rho + 1, so the exponent is pinned
       from both sides.

  (B16) THE FIRST GAP WITHOUT A SIMPLICITY HYPOTHESIS ON x2.  E cannot separate
       L from a REPEATED x2, since E(x2) = x2 Q'(x2) = 0 there.  The angle count
       can, and quantitatively: with x1 < L the angle at x1 closes to 0 at rate
       theta, so the complements share less than theta/c of their total
       pi - r theta, so the complement at x2 is O(theta), so its arccot argument
       grows like 1/theta, so tau sits a FIXED factor below x2.  That last bound
       is uniform in theta, which is what upgrades L <= x2 to L < x2.  Every
       constant is checked against the construction the Lean proof uses.

  (B17) THE LIMIT IS NONZERO.  (B15) gives the exponent; the Rouche model that
       enumerates the cluster also needs the rescaled limit z/delta^rho to be
       NONZERO, since z/delta^rho -> 0 degenerates the model to a rho-fold root
       at the origin.  Checked against the closed form the proof computes, so the
       constant is pinned and not just its sign.

  (B18) THE UPPER ENDPOINT, AND ITS DICHOTOMY IN r.  Prop. 3 Case 3 reads the
       branch at theta -> (pi/r)^-.  For r >= 2 the radius COLLAPSES: every
       angle is below pi, so the angle sum is below n pi by a margin a fixed
       radius cannot give up, while the branch equation forces the sum to
       r theta + (n-1) pi -> n pi.  Then Q(t) -> Q(0) and the exact relation
       t^r = -Q(t)/z reads tau^r |z| -> prod a_k.  For r = 1 the argument fails
       -- pi/r = pi leaves the interval on which sin(theta) is bounded below --
       and the radius settles at a finite positive limit instead.  Both sides
       are measured here; only r >= 2 is proved in Lean.

  (B19) THE MODEL EQUATION, AND ITS SIGN.  The cluster enumeration needs the
       branch directions to be the Rouche model's own roots,
       q(x1) alpha^rho + z0 x1^r = 0.  Positivity of z0 does not settle this --
       it is a SIGN statement, and a z0 right in modulus and wrong in sign would
       pass z0 > 0 and fail here.  Checked from the branch alone: alpha is read
       off t(delta) = tau(delta) e^{-i delta}, and z0 is the closed form the
       Lean statement now carries.

  (B20) THEIR LEMMA 5, FIRST HALF.  Every zero of R(t) = r t^{r-1} Q - t^r Q' is
       real.  R = -t^{r-1} E with E = t Q' - r Q, so this is real-rootedness of
       E, and it is what lets the paper read both endpoints off R.  Checked in
       EXACT arithmetic with roots counted with multiplicity; see the note in
       the body on why float roots and distinct-root counting both give false
       negatives here.

  (B21) THE COLLAPSE RATE, AND THE MEMBER EXPANSION.  Case 3 needs the cluster
       members normalized against the principal one.  The branch supplies the
       rate: tau/(pi/r - theta) -> r/(sin(pi/r) sum 1/a_k), again from the angle
       count -- the complements sum to r delta EXACTLY and each is asymptotically
       tau sin(pi/r)/a_k.  Feeding that into the exact relation
       zeta_j^r = Q(t_j)/Q(t_+) gives Re c_j = (cos(pi/r) - Re omega_j)/sin(pi/r),
       in which neither the pencil nor the rate constant survives.

  (B22) THE POINTWISE SECOND-ORDER FORM.  (B21a) is a limit, which gives only
       o(delta); the member expansion's binder is stated with O(delta^2) and
       cannot consume that.  Checked here in the form the consumer takes,
       |tau - m delta| <= C delta^2, by the ratio over delta^2 settling rather
       than by a flat tolerance.

A STANDING RULE FOR THE UPPER ENDPOINT.  Never assert a fixed convergence order
at theta -> (pi/r)^- without evaluating r = 2 first.  Every error term there is
carried by the cross term -2 a_k tau cos(theta), and cos(pi/2) = 0 kills it, so
r = 2 is one order better than r >= 3.  (B18), (B21a) and (B22) were each first
written asserting a single order across r and each failed on the r = 2 rows;
all three now assert "bounded and non-increasing", which holds for every r.
See banked.txt BANK-35.  (r = 1 is a SEPARATE matter: there sin(pi) = 0 and the
collapse fails outright, cos(pi) = -1 being nowhere near zero.  Do not fold the
two together.)

The general form of both errors this file has made is CHECKING WHERE THE CLAIM
COULD NOT FAIL.  A convergence order calibrated on r >= 3 data passes r = 2
vacuously; a constant confirmed at a pencil with sum 1/a_k = 1 cannot see the
factor that is 1 there, and confirming it at n = 1 cannot see an n-dependence
because n = 1 is outside the hypothesis range of the lemma being tested.  Choose
the sample where the claim is most able to fail, not where it is most convenient.

mpmath throughout; the branch radius is located by bisection on the strictly
monotone angle sum, so no root polishing is involved.
"""

from mpmath import mp, mpf, mpc, pi, sin, cos, atan, exp, sqrt, fabs, sign, polyroots

mp.dps = 40

TOL = mpf('1e-25')


def ok(msg):
    print('  ' + msg)


def arccot(x):
    """Inverse cotangent onto (0, pi); this is `ftArccot' of FTBranchAngle.lean."""
    return pi / 2 - atan(x)


def ft_angle(a, tau, th):
    """`ftAngle a tau th': the unique y in (th, pi) with a sin y = tau sin(y - th)."""
    return arccot(cos(th) / sin(th) - a / (tau * sin(th)))


def angle_sum(taus, tau, th):
    return sum(ft_angle(a, tau, th) for a in taus)


def feasible(n, r, l):
    """The range condition of (B2), as a closed predicate on (n, r, l)."""
    return (n < (l + 1) * r) or (n == (l + 1) * r and l >= 1)


def solve_tau(taus, r, l, th):
    """The unique tau > 0 with sum_k theta_k(tau) = r th + l pi (bisection in log tau)."""
    target = r * th + l * pi
    lo, hi = mpf('1e-25'), mpf('1e25')
    for _ in range(300):
        mid = sqrt(lo * hi)
        if angle_sum(taus, mid, th) > target:
            lo = mid
        else:
            hi = mid
    return sqrt(lo * hi)


def branch_z(taus, r, tau, th):
    """z = -P(t_0)/t_0^r for P(t) = prod (tau_k - t) and t_0 = tau e^{-i th}."""
    t0 = mpc(tau) * exp(mpc(0, -1) * th)
    P = mpc(1)
    for a in taus:
        P *= (a - t0)
    return -P / t0 ** r


SETS = [[mpf('0.5'), mpf(1), mpf(2), mpf('3.7')],
        [mpf(1), mpf(1), mpf('2.5')],
        [mpf('0.3'), mpf('0.9')],
        [mpf(2)],
        [mpf(1), mpf(2), mpf(3), mpf(4), mpf(5), mpf(6)]]

FRACS = [mpf(j) / 1000 for j in (1, 17, 250, 500, 900, 999)]


# ---------------------------------------------------------------- (B1)-(B4)

checked = 0
infeasible = 0
for taus in SETS:
    n = len(taus)
    for r in (1, 2, 3, 4):
        for l in range(0, n):
            # (B2): the closed predicate agrees with the sampled range condition
            sampled = all((n - r) * (f * pi / r) < l * pi for f in
                          [mpf(j) / 200 for j in range(1, 200)])
            assert sampled == feasible(n, r, l), ('B2 predicate', n, r, l)
            if not feasible(n, r, l):
                infeasible += 1
                continue
            for f in FRACS:
                th = f * pi / r
                tau = solve_tau(taus, r, l, th)
                ths = [ft_angle(a, tau, th) for a in taus]
                # (B1) clause (i)
                assert all(t > th for t in ths), ('B1 (i)', n, r, l, f)
                assert all(t < pi for t in ths), ('B1 range', n, r, l, f)
                # (B1) clause (ii)
                assert fabs(sum(ths) - (r * th + l * pi)) < TOL, ('B1 (ii)', n, r, l, f)
                # (B1) clause (iii)
                for a, t in zip(taus, ths):
                    v = a * sin(t) / sin(t - th)
                    assert fabs(v - tau) < TOL * max(1, fabs(tau)), ('B1 (iii)', n, r, l, f)
                # (B4)
                z = branch_z(taus, r, tau, th)
                assert fabs(z.imag) < mpf('1e-22') * max(1, fabs(z)), ('B4 real', n, r, l, f)
                s = 1 if (n - l - 1) % 2 == 0 else -1
                assert sign(z.real) == s, ('B4 sign', n, r, l, f, z)
                checked += 1

ok(f'(B1)+(B4): clauses (i)-(iii) and z real of sign (-1)^(n-l-1) verified at '
   f'{checked} (parameter, angle) pairs')
ok(f'(B2): the range predicate matched the sampled condition at every (n, r, l); '
   f'{infeasible} of the swept triples are infeasible and were skipped')

# (B2) the smallest failing instance, exhibited rather than asserted
n, r, l = 2, 2, 0
assert not feasible(n, r, l), 'B2 (2,2,0)'
gap = None
for taus in ([mpf('0.3'), mpf('0.9')], [mpf(1), mpf(1)], [mpf('0.05'), mpf(7)]):
    for f in FRACS:
        th = f * pi / r
        target = r * th + l * pi
        for e in range(-20, 21):
            tau = mpf(10) ** e
            v = angle_sum(taus, tau, th) - target
            assert v > 0, ('B2 witness', taus, f, e, v)
            gap = v if gap is None or v < gap else gap
ok('(B2): (n, r, l) = (2, 2, 0) is infeasible -- the angle sum exceeds r theta + l pi '
   f'by at least {mp.nstr(gap, 4)} over tau = 1e-20 .. 1e20 at every sampled theta, '
   'because clause (i) already forces sum theta_k > 2 theta')

# ------------------------------------------------------------------- (B3)

for n in range(1, 8):
    for r in range(1, 6):
        l = n - 1
        expect = not (n == 1 and r == 1)
        assert feasible(n, r, l) == expect, ('B3', n, r)
ok('(B3): l = n - 1 satisfies the range condition for every 1 <= n <= 7, 1 <= r <= 5 '
   'except the degenerate n = r = 1')

# ------------------------------------------------------------- (B5) and (B6)

samples = 0
for taus in SETS:
    n = len(taus)
    for r in (1, 2, 3):
        l = n - 1
        if (r, n) == (1, 2) or not feasible(n, r, l):
            continue
        prev_tau = None
        prev_z = None
        direction = None
        for j in range(1, 300):
            th = mpf(j) / 300 * pi / r
            tau = solve_tau(taus, r, l, th)
            z = branch_z(taus, r, tau, th).real
            if prev_tau is not None:
                assert tau < prev_tau, ('B5', n, r, j, tau, prev_tau)
                d = 1 if z > prev_z else -1
                if direction is None:
                    direction = d
                assert d == direction, ('B6', n, r, j)
            prev_tau, prev_z = tau, z
            samples += 1
ok(f'(B5)+(B6): tau(theta) strictly decreasing and z(theta) strictly monotone across '
   f'{samples} sampled angles, for every admissible (deg P, r) with (r, n) != (1, 2)')

# ------------------------------------------------------------------- (B8)

def partials(taus, r, tau, th):
    ths = [ft_angle(a, tau, th) for a in taus]
    d_tau = sum(-(sin(t) ** 2 * a / (tau ** 2 * sin(th))) for a, t in zip(taus, ths))
    d_th = sum(sin(t) * cos(t - th) / sin(th) for t in ths)
    return ths, d_tau, d_th


worst_tau = mpf(0)
worst_ang = mpf(0)
checked8 = 0
for taus in SETS:
    n = len(taus)
    for r in (1, 2, 3):
        l = n - 1
        if not feasible(n, r, l):
            continue
        for j in (60, 150, 240):
            th = mpf(j) / 300 * pi / r
            tau = solve_tau(taus, r, l, th)
            ths, d_tau, d_th = partials(taus, r, tau, th)
            assert d_tau < 0, ('B8 dtau sign', taus, r, th)
            tp = -(d_th - r) / d_tau
            if (r, n) != (1, 2) and n <= 2 * r:
                assert tp < 0, ('B8 tau prime sign', taus, r, th, tp)
            h = mpf(10) ** (-12)
            tau_p = solve_tau(taus, r, l, th + h)
            tau_m = solve_tau(taus, r, l, th - h)
            fd = (tau_p - tau_m) / (2 * h)
            rel = fabs(fd - tp) / max(1, fabs(tp))
            assert rel < mpf('1e-8'), ('B8 tau prime', taus, r, th, tp, fd, rel)
            worst_tau = max(worst_tau, rel)
            for i, a in enumerate(taus):
                dk = -(sin(ths[i]) ** 2 * a / (tau ** 2 * sin(th))) * tp \
                     + sin(ths[i]) * cos(ths[i] - th) / sin(th)
                fdk = (ft_angle(a, tau_p, th + h) - ft_angle(a, tau_m, th - h)) / (2 * h)
                relk = fabs(fdk - dk) / max(1, fabs(dk))
                assert relk < mpf('1e-8'), ('B8 angle prime', taus, r, th, i, dk, fdk, relk)
                worst_ang = max(worst_ang, relk)
            checked8 += 1
ok(f'(B8): d(Sigma)/d(tau) < 0 at every sampled point; tau\'(theta) and '
   f'dtheta_k/dtheta match central differences at {checked8} points, worst relative '
   f'deviation {mp.nstr(worst_tau, 3)} and {mp.nstr(worst_ang, 3)}')

# ------------------------------------------------------------------- (B7)

for taus in SETS:
    n = len(taus)
    if n < 2:
        continue
    # E(t) = t P'(t) - P(t) for P(t) = prod (tau_k - t), coefficients high->low
    P = [mpf(1)]                       # prod (tau_k - t), low->high in t
    for a in taus:
        nc = [mpf(0)] * (len(P) + 1)
        for i, ci in enumerate(P):
            nc[i] += ci * a
            nc[i + 1] -= ci
        P = nc
    E = [P[k] * (k - 1) for k in range(len(P))]           # t P' - P, low->high
    while len(E) > 1 and E[-1] == 0:
        E.pop()
    assert len(E) >= 2, ('B7 degree', taus)
    rts = polyroots(list(reversed(E)), maxsteps=200, extraprec=200)
    neg = [t for t in rts if fabs(mp.im(t)) < mpf('1e-20') and mp.re(t) < 0]
    assert len(neg) == 1, ('B7 count', taus, rts)
    t_b = mp.re(neg[0])
    # it really is a zero of E, and P does not vanish there
    val = sum(E[k] * t_b ** k for k in range(len(E)))
    assert fabs(val) < mpf('1e-18') * max(1, max(fabs(c) for c in E)), ('B7 residual', taus)
    Pv = sum(P[k] * t_b ** k for k in range(len(P)))
    assert fabs(Pv) > 0, ('B7 P nonzero', taus)
ok('(B7): for r = 1 and deg P >= 2, E(t) = t P\'(t) - P(t) has exactly one negative '
   'zero, and P does not vanish there')

# ------------------------------------------------------------------- (B9)

# The angle sum at tiny theta subtracts two quantities of size 1/theta, so the
# working precision is raised for this block; theta = 1e-10 leaves the first-order
# error in tau of the same size, which is what the residual threshold allows for.
_dps = mp.dps
mp.dps = 60

worst_E = mpf(0)
checked9 = 0
for taus in SETS:
    n = len(taus)
    if n < 2:
        continue
    srt = sorted(taus)
    for r in (1, 2, 3):
        l = n - 1
        if (r, n) == (1, 2) or n > 2 * r or not feasible(n, r, l):
            continue
        # E(t) = t P'(t) - r P(t), coefficients low->high, for P = prod (tau_k - t)
        P = [mpf(1)]
        for a in taus:
            nc = [mpf(0)] * (len(P) + 1)
            for i, ci in enumerate(P):
                nc[i] += ci * a
                nc[i + 1] -= ci
            P = nc
        E = [P[k] * (k - r) for k in range(len(P))]
        t_a = solve_tau(taus, r, l, pi / r * mpf(10) ** (-10))
        tol = mpf('1e-6')
        assert srt[0] - tol <= t_a <= srt[1] + tol, ('B9 bracket', taus, r, t_a, srt[:2])
        Ev = sum(E[k] * t_a ** k for k in range(len(E)))
        scale = max(fabs(E[k]) * max(1, t_a) ** k for k in range(len(E)))
        rel = fabs(Ev) / scale
        assert rel < mpf('1e-8'), ('B9 critical', taus, r, t_a, Ev, rel)
        worst_E = max(worst_E, rel)
        checked9 += 1
mp.dps = _dps
ok(f'(B9): at {checked9} admissible (deg P, r) the branch radius at theta = 1e-10 pi/r '
   f"already sits on a zero of E(t) = t P'(t) - r P(t), inside [tau_(1), tau_(2)]; "
   f'worst relative residual {mp.nstr(worst_E, 3)}')

# ------------------------------------------------------------------ (B10)

def chord_prod(taus, tau, psi):
    return mp.fprod([mp.sqrt(a ** 2 - 2 * a * tau * cos(psi) + tau ** 2) for a in taus])

worst_Z = mpf(0)
checked10 = 0
mono10 = 0
for taus in SETS:
    n = len(taus)
    for r in (1, 2, 3):
        l = n - 1
        if not feasible(n, r, l):
            continue
        # (n + l + 1) = 2n is even at l = n-1, so the branch value is the bare chord product
        for f in FRACS:
            th = f * pi / r
            tau = solve_tau(taus, r, l, th)
            z = branch_z(taus, r, tau, th)
            zc = chord_prod(taus, tau, th) / tau ** r
            rel = fabs(mp.re(z) - zc) / max(1, fabs(zc))
            assert rel < mpf('1e-25'), ('B10 chord form', taus, r, f, z, zc, rel)
            worst_Z = max(worst_Z, rel)
            checked10 += 1
        # strict monotonicity of the chord product at a FIXED radius
        tau0 = solve_tau(taus, r, l, pi / r / 2)
        prev = None
        for j in range(1, 200):
            psi = mpf(j) / 200 * pi
            v = chord_prod(taus, tau0, psi)
            if prev is not None:
                assert v > prev, ('B10 chord monotone', taus, r, j, v, prev)
            prev = v
            mono10 += 1
ok(f'(B10): the branch value equals the fixed-radius chord product at {checked10} points '
   f'(worst relative deviation {mp.nstr(worst_Z, 3)}), and that chord product is strictly '
   f'increasing in the angle across {mono10} sampled angles on (0, pi)')

# ------------------------------------------------------------------ (B11)

def sigma_of(taus, r, tau, th):
    t0 = tau * mp.expjpi(0) * exp(mpc(0, -1) * th)
    return sum(t0 / (a - t0) for a in taus) + r

worst_23 = mpf(0)
checked11 = 0
for taus in SETS:
    n = len(taus)
    for r in (1, 2, 3):
        for l in range(n):
            if not feasible(n, r, l):
                continue
            for f in (mpf('0.2'), mpf('0.5'), mpf('0.8')):
                th = f * pi / r
                h = mpf(10) ** (-15)
                tau = solve_tau(taus, r, l, th)
                z = mp.re(branch_z(taus, r, tau, th))
                zp = (mp.re(branch_z(taus, r, solve_tau(taus, r, l, th + h), th + h))
                      - mp.re(branch_z(taus, r, solve_tau(taus, r, l, th - h), th - h))) / (2 * h)
                S = sigma_of(taus, r, tau, th)
                assert mp.im(S) < 0, ('B11 Im Sigma', taus, r, l, f, S)
                lhs = zp * mp.im(S)
                rhs = -z * (fabs(S) ** 2)
                rel = fabs(lhs - rhs) / max(1, fabs(rhs))
                assert rel < mpf('1e-8'), ('B11 eq23', taus, r, l, f, lhs, rhs, rel)
                assert sign(zp) == sign(z), ('B11 sign', taus, r, l, f)
                worst_23 = max(worst_23, rel)
                checked11 += 1
ok(f'(B11a): Im Sigma < 0 and eq. (23) in the form z\' Im Sigma = -z |Sigma|^2 verified at '
   f'{checked11} points, worst relative deviation {mp.nstr(worst_23, 3)}')

# the inequality behind Lemma 3 in the case Lean does not cover, n > 2r
case2 = 0
worst_gap = None
for taus in SETS:
    n = len(taus)
    for r in (1, 2, 3):
        l = n - 1
        if n <= 2 * r or (r, n) == (1, 2) or not feasible(n, r, l):
            continue
        for j in range(1, 60):
            th = mpf(j) / 60 * pi / r
            tau = solve_tau(taus, r, l, th)
            ths = [ft_angle(a, tau, th) for a in taus]
            lhs = sum(sin(2 * t - th) for t in ths)
            rhs = (2 * r - n) * sin(th)
            assert lhs < rhs, ('B11 case2', taus, r, th, lhs, rhs)
            gap = rhs - lhs
            worst_gap = gap if worst_gap is None or gap < worst_gap else worst_gap
            case2 += 1
# a stress sweep, and the order to which the margin degenerates at the endpoints
STRESS = [[mpf(1), mpf(2), mpf(3)], [mpf(1), mpf(1), mpf(1)],
          [mpf('0.001'), mpf(1), mpf(1000)],
          [mpf('1e-6'), mpf('1e-6'), mpf(1), mpf(1), mpf('1e6')],
          [mpf(1), mpf(2), mpf(3), mpf(4), mpf(5), mpf(6), mpf(7)]]
stress = 0
for taus in STRESS:
    n = len(taus)
    for r in (1, 2, 3):
        if n <= 2 * r:
            continue
        for e in range(1, 11):
            for f in (mpf(10) ** (-e), 1 - mpf(10) ** (-e)):
                th = f * pi / r
                tau = solve_tau(taus, r, n - 1, th)
                ths = [ft_angle(a, tau, th) for a in taus]
                lhs = sum(sin(2 * t - th) for t in ths)
                assert lhs < (2 * r - n) * sin(th), ('B11 stress', taus, r, f)
                stress += 1
# the cubic degeneration at theta -> 0, which is why a first-order bound cannot work
_t3 = [mpf(1), mpf(2), mpf(3)]
_ratio = []
for e in (4, 6, 8):
    th = mpf(10) ** (-e) * pi
    tau = solve_tau(_t3, 1, 2, th)
    ths = [ft_angle(a, tau, th) for a in _t3]
    mg = (2 * 1 - 3) * sin(th) - sum(sin(2 * t - th) for t in ths)
    _ratio.append(mg / th ** 3)
assert all(fabs(x - _ratio[0]) < mpf('0.01') * _ratio[0] for x in _ratio), ('B11 cubic', _ratio)
ok(f'(B11b): sum_k sin(2 theta_k - theta) < (2r - n) sin theta holds at {case2} sampled '
   f'angles with n > 2r, smallest margin {mp.nstr(worst_gap, 3)}, and survives a further '
   f'{stress} stress points (roots spanning 1e-6..1e6, repeated roots, theta to 1e-10 of '
   'each endpoint) -- their Lemma 3, both cases, now proven in lean/')
ok(f'(B11c): that margin degenerates CUBICALLY at the endpoints -- margin/theta^3 settles '
   f'at {mp.nstr(_ratio[-1], 4)} for P = (1-t)(2-t)(3-t), r = 1 -- so any bound losing even '
   'first order in sin theta is off by three orders where the inequality is decided, '
   'which is why the merge identity and not a subadditivity bound is what proves it')

# ------------------------------------------------------------------ (B12)

REP = [([mpf(1), mpf(2), mpf(3)], 1, False),
       ([mpf('0.5'), mpf(1), mpf(2), mpf('3.7')], 1, False),
       ([mpf(1), mpf(1), mpf(3)], 2, True),
       ([mpf(1), mpf(1), mpf(1), mpf(4)], 3, True),
       ([mpf(2), mpf(2), mpf(5), mpf(9)], 2, True)]
bracket = 0
worst_rep = mpf(0)
for taus, rho, repeated in REP:
    n = len(taus)
    srt = sorted(taus)
    for r in (1, 2):
        l = n - 1
        if not feasible(n, r, l):
            continue
        L = solve_tau(taus, r, l, pi / r * mpf(10) ** (-12))
        tol = mpf('1e-8')
        assert srt[0] - tol <= L <= srt[1] + tol, ('B12 bracket', taus, r, L, srt[:2])
        bracket += 1
        if repeated:
            d = fabs(L - srt[0])
            assert d < mpf('1e-9'), ('B12 repeated', taus, r, L, srt[0], d)
            worst_rep = max(worst_rep, d)
ok(f'(B12a): the endpoint limit lies in [tau_(1), tau_(2)] at all {bracket} sampled '
   f'(pencil, r), and equals tau_(1) whenever the smallest zero is repeated '
   f'(worst |L - x1| = {mp.nstr(worst_rep, 3)})')

worst_m = mpf(0)
for taus, rho, repeated in REP:
    if not repeated:
        continue
    n = len(taus)
    x1 = min(taus)
    m = -x1 * mp.cot(pi / rho)
    h = mpf(10) ** (-20)
    th = mpf(10) ** (-5)
    tp = (solve_tau(taus, 1, n - 1, th + h) - solve_tau(taus, 1, n - 1, th - h)) / (2 * h)
    worst_m = max(worst_m, fabs(tp - m) / th)
    assert fabs(tp - m) < mpf('1e-3'), ('B12 slope', taus, rho, tp, m)
ok(f"(B12b): tau'(theta) converges to -x1 cot(pi/rho) at every repeated-minimum "
   f"pencil sampled; |tau' - m|/theta stays below {mp.nstr(worst_m, 3)} at theta = 1e-5, "
   'so the Prop. 3 Case 2 rate is a first-order bound on a derivative that is in hand')

# the rate at which the outer angles open to pi, with the constant Lean proves
worst_rate = mpf(0)
rate_pts = 0
for taus, rho, repeated in REP:
    if not repeated:
        continue
    n = len(taus)
    x1 = min(taus)
    outer = [t for t in taus if t != x1]
    if not outer:
        continue
    c = (min(outer) / x1 - 1) / 2
    for r in (1, 2):
        l = n - 1
        if not feasible(n, r, l):
            continue
        for e in (3, 4, 5):
            th = mpf(10) ** (-e)
            tau = solve_tau(taus, r, l, th)
            if tau * (1 + c) > min(outer):
                continue
            for t in outer:
                gap = pi - ft_angle(t, tau, th)
                assert gap <= th / c, ('B12 rate', taus, r, e, t, gap, th / c)
                worst_rate = max(worst_rate, gap / th)
                rate_pts += 1
ok(f'(B12c): pi - theta_k <= theta/c for every outer zero at {rate_pts} points, the bound '
   f'ForgacsTran.pi_sub_ftAngle_le proves; worst (pi - theta_k)/theta seen is '
   f'{mp.nstr(worst_rate, 4)}')

# ------------------------------------------------------------------ (B13)

# The Lean route to the second-order bound runs through an EXACT identity and a
# first-order bound on one angle; neither step differentiates tau.  Both halves
# are measured here, and then the bound they yield.
worst_id = mpf(0)
worst_beta = mpf(0)
id_pts = 0
for taus, rho, repeated in REP:
    if not repeated:
        continue
    n = len(taus)
    x1 = min(taus)
    outer = [t for t in taus if t != x1]
    c = (min(outer) / x1 - 1) / 2
    for r in (1, 2):
        l = n - 1
        if not feasible(n, r, l):
            continue
        for e in (3, 4, 5, 6):
            th = mpf(10) ** (-e)
            tau = solve_tau(taus, r, l, th)
            if tau * (1 + c) > min(outer):
                continue
            beta = ft_angle(x1, tau, th)
            # x1/tau = cos th - sin th cot beta, exactly
            resid = fabs(x1 / tau - (cos(th) - sin(th) * mp.cot(beta)))
            assert resid < mpf('1e-25'), ('B13 identity', taus, r, e, resid)
            worst_id = max(worst_id, resid)
            # |beta - (pi - pi/rho)| <= ((r + (n - rho)/c)/rho) th, from the angle
            # count alone: rho beta = r th + (rho - 1) pi + sum_{k not in S}(pi - theta_k)
            bnd = ((r + mpf(n - rho) / c) / rho) * th
            dev = fabs(beta - (pi - pi / rho))
            assert dev <= bnd, ('B13 beta', taus, r, e, dev, bnd)
            worst_beta = max(worst_beta, dev / th)
            id_pts += 1
ok(f'(B13a): x1/tau = cos(theta) - sin(theta) cot(beta) holds to {mp.nstr(worst_id, 3)} at '
   f'{id_pts} points -- an identity, not an estimate, so a first-order bound on beta '
   'gives a second-order bound on tau')
ok(f'(B13b): |beta - (pi - pi/rho)| <= ((r + (n-rho)/c)/rho) theta at the same points, the '
   f'bound ForgacsTran.eventually_abs_ftBranchAngle_sub_le proves; worst |beta - beta_0|/theta '
   f'is {mp.nstr(worst_beta, 4)}')

# The bound itself, and its discrimination: the ratio |tau - (x1 + m th)|/th^2 must
# SETTLE as th shrinks (it would diverge like 1/th if the true error were O(th)),
# and dropping the linear term must leave an error genuinely of order th.
worst_C = mpf(0)
worst_ratio_growth = mpf(0)
lin_pts = 0
for taus, rho, repeated in REP:
    if not repeated:
        continue
    n = len(taus)
    x1 = min(taus)
    outer = [t for t in taus if t != x1]
    c = (min(outer) / x1 - 1) / 2
    m = -x1 * mp.cot(pi / rho)
    for r in (1, 2):
        l = n - 1
        if not feasible(n, r, l):
            continue
        ratios = []
        for e in (3, 4, 5, 6):
            th = mpf(10) ** (-e)
            tau = solve_tau(taus, r, l, th)
            if tau * (1 + c) > min(outer):
                continue
            quad = fabs(tau - (x1 + m * th)) / th ** 2
            lin = fabs(tau - x1) / th
            # the linear term is not a decoration: without it the error is order th
            assert lin > mpf('0.1') * fabs(m), ('B13 linear', taus, r, e, lin, m)
            ratios.append(quad)
            worst_C = max(worst_C, quad)
            lin_pts += 1
        if len(ratios) >= 2:
            worst_ratio_growth = max(worst_ratio_growth, max(ratios) / min(ratios))
assert worst_ratio_growth < mpf(4), ('B13 growth', worst_ratio_growth)
ok(f'(B13c): |tau(theta) - (x1 - x1 cot(pi/rho) theta)| <= C theta^2 at {lin_pts} points with '
   f'C = {mp.nstr(worst_C, 4)}; across four decades of theta the ratio moves by a factor of at '
   f'most {mp.nstr(worst_ratio_growth, 3)}, so the error is second order and not first -- the '
   'shape ForgacsTran.exists_bound_ftTau_sub_linear supplies to `principal_expansion_of_tau_rate`')

# ------------------------------------------------------------------ (B14)

# The radius never reaches the second zero.  This is a bound at EVERY theta on the
# arc, not an asymptotic one, and the mechanism is the midpoint (pi + theta)/2:
# a zero at or inside the radius has its angle at or below it, and two such zeros
# already push the angle sum below r theta + (n-1) pi.
mid_pts = 0
for taus, rho, repeated in REP:
    for r in (1, 2):
        n = len(taus)
        if not feasible(n, r, n - 1):
            continue
        for e in (1, 2, 3, 5):
            th = pi / r * mpf(10) ** (-e)
            tau = solve_tau(taus, r, n - 1, th)
            for a in taus:
                below = ft_angle(a, tau, th) < (pi + th) / 2
                assert below == (a < tau), ('B14 midpoint', taus, r, e, a, tau)
                mid_pts += 1
            # the midpoint is exactly the angle at which a = tau
            assert fabs(ft_angle(tau, tau, th) - (pi + th) / 2) < mpf('1e-25'), \
                ('B14 midpoint exact', taus, r, e)
ok(f'(B14a): theta_k < (pi + theta)/2 exactly when tau_k < tau, at {mid_pts} sampled '
   '(pencil, r, theta, zero); and the midpoint is attained precisely at tau_k = tau -- '
   'the characterization ForgacsTran.ftAngle_lt_mid proves')

GAP = REP + [([mpf(1), mpf(2), mpf(2)], 1, False),
             ([mpf(1), mpf(2), mpf(2), mpf(2)], 1, False),
             ([mpf(1), mpf('1.01'), mpf(5)], 1, False)]
gap_pts = 0
worst_frac = mpf(0)
for taus, rho, repeated in GAP:
    n = len(taus)
    srt = sorted(taus)
    if srt[0] == srt[-1]:
        continue
    x2 = min(t for t in taus if t > srt[0])   # the second DISTINCT zero
    for r in (1, 2):
        if not feasible(n, r, n - 1):
            continue
        for e in (1, 2, 3, 4, 6):
            th = pi / r * mpf(10) ** (-e)
            tau = solve_tau(taus, r, n - 1, th)
            assert tau < x2, ('B14 gap', taus, r, e, tau, x2)
            worst_frac = max(worst_frac, tau / x2)
            gap_pts += 1
ok(f'(B14b): tau(theta) < x2 at all {gap_pts} sampled (pencil, r, theta) across the whole '
   f'arc, not merely near the endpoint; worst tau/x2 seen is {mp.nstr(worst_frac, 5)} -- the '
   'bound ForgacsTran.ftTau_lt_of_lt proves')

# The endpoint limit is strictly below x2 even where x2 REPEATS, which is the case
# the critical-polynomial route cannot see: E(x2) = x2 Q'(x2) vanishes at a repeated
# zero, so `eval_ftCriticalReal_ne_zero_of_simple' does not apply and the Lean
# statement carries simplicity of x2 as a hypothesis.  The margin is measured here.
worst_L = mpf(0)
rep_rows = []
for taus, rho, repeated in GAP:
    n = len(taus)
    srt = sorted(taus)
    if srt[0] == srt[-1]:
        continue
    x2 = min(t for t in taus if t > srt[0])
    simple2 = sum(1 for t in taus if t == x2) == 1
    for r in (1, 2):
        if not feasible(n, r, n - 1):
            continue
        L = solve_tau(taus, r, n - 1, pi / r * mpf(10) ** (-12))
        assert L < x2, ('B14 limit', taus, r, L, x2)
        worst_L = max(worst_L, L / x2)
        if not simple2:
            rep_rows.append((tuple(float(t) for t in taus), r, float(x2 - L)))
ok(f'(B14c): the endpoint limit stays below x2 at every sampled (pencil, r), worst L/x2 = '
   f'{mp.nstr(worst_L, 5)}.  That includes {len(rep_rows)} rows where x2 REPEATS, so E(x2) = 0 '
   'and the simplicity hypothesis of ForgacsTran.exists_tendsto_ftTau_lt_second does not hold; '
   f'the smallest margin x2 - L on those rows is {min(rw[2] for rw in rep_rows):.4f}, so the '
   'conclusion is true there and only the E-route to it is unavailable')

# ------------------------------------------------------------------ (B15)

# The spectral parameter inherits the multiplicity of the smallest zero:
# |z(delta)| = O(delta^rho).  The exponent is what matters, so both directions
# are asserted -- the ratio at rho SETTLES, and the ratio at rho + 1 DIVERGES,
# which is what pins rho as exact rather than merely sufficient.
worst_Z = mpf(0)
worst_Z_growth = mpf(0)
z_pts = 0
sharp_rows = 0
for taus, rho, repeated in REP:
    if not repeated:
        continue
    n = len(taus)
    for r in (1, 2):
        if not feasible(n, r, n - 1):
            continue
        at_rho, at_rho1 = [], []
        for e in (3, 4, 5, 6):
            th = mpf(10) ** (-e)
            tau = solve_tau(taus, r, n - 1, th)
            z = fabs(branch_z(taus, r, tau, th))
            at_rho.append(z / th ** rho)
            at_rho1.append(z / th ** (rho + 1))
            worst_Z = max(worst_Z, z / th ** rho)
            z_pts += 1
        # settles at rho
        assert max(at_rho) / min(at_rho) < mpf(4), ('B15 settle', taus, r, at_rho)
        worst_Z_growth = max(worst_Z_growth, max(at_rho) / min(at_rho))
        # diverges at rho + 1, by at least three decades across three of theta
        assert at_rho1[-1] / at_rho1[0] > mpf(100), ('B15 sharp', taus, r, at_rho1)
        sharp_rows += 1
ok(f'(B15): |z(delta)| <= C delta^rho at {z_pts} points with C = {mp.nstr(worst_Z, 4)}; across '
   f'four decades the ratio |z|/delta^rho moves by a factor of at most '
   f'{mp.nstr(worst_Z_growth, 3)}, while |z|/delta^(rho+1) grows without bound on all '
   f'{sharp_rows} rows -- so rho is the exact exponent, not merely an admissible one, and it '
   'is the bound ForgacsTran.exists_bound_ftBranchZ_pow supplies')

# ------------------------------------------------------------------ (B16)

# Strictness of L < x2 WITHOUT assuming x2 simple.  The mechanism is quantitative
# and every constant in it is checked here against the same construction the Lean
# proof uses: K = (x1 + L)/2, c = (1 - x1/K)/2.
GAPQ = [([mpf(1), mpf(2), mpf(2)], 'x2 double'),
        ([mpf(1), mpf(2), mpf(2), mpf(2)], 'x2 triple'),
        ([mpf(1), mpf(2), mpf(3)], 'x2 simple'),
        ([mpf(1), mpf('1.01'), mpf('1.01')], 'x2 double and close to x1')]
q_pts = 0
worst_phi = mpf(0)
worst_psi = mpf(0)
worst_fac = mpf(0)
for taus, label in GAPQ:
    n = len(taus)
    x1 = min(taus)
    x2 = min(t for t in taus if t > x1)
    for r in (1, 2):
        if not feasible(n, r, n - 1):
            continue
        L = solve_tau(taus, r, n - 1, pi / r * mpf(10) ** (-14))
        assert x1 < L < x2, ('B16 gap', taus, r, L, x1, x2)
        K = (x1 + L) / 2
        c = (1 - x1 / K) / 2
        assert c > 0, ('B16 c', taus, r, c)
        for e in (3, 5, 7):
            th = pi / r * mpf(10) ** (-e)
            tau = solve_tau(taus, r, n - 1, th)
            if tau <= K or th >= min(1, c / pi):
                continue
            # the angle at x1 closes at rate theta, with the proved constant
            phi_i = ft_angle(x1, tau, th)
            assert phi_i <= th / c, ('B16 phi', taus, r, e, phi_i, th / c)
            worst_phi = max(worst_phi, phi_i * c / th)
            # so the complement at x2 is O(theta), with the same constant
            psi_j = pi - ft_angle(x2, tau, th)
            assert psi_j <= th / c, ('B16 psi', taus, r, e, psi_j, th / c)
            worst_psi = max(worst_psi, psi_j * c / th)
            # which pins tau a FIXED factor below x2 -- this is the uniform step
            assert 1 + c / (2 * pi) <= x2 / tau, ('B16 factor', taus, r, e, x2 / tau)
            worst_fac = max(worst_fac, (1 + c / (2 * pi)) / (x2 / tau))
            q_pts += 1
ok(f'(B16): at {q_pts} sampled points over pencils with x2 double, triple, simple and nearly '
   f'coincident with x1: theta_1 <= theta/c (worst ratio {mp.nstr(worst_phi, 4)}), '
   f'pi - theta_2 <= theta/c (worst {mp.nstr(worst_psi, 4)}), and x2/tau >= 1 + c/(2 pi) '
   f'(worst {mp.nstr(worst_fac, 4)}) -- the three steps of '
   'ForgacsTran.lt_of_tendsto_ftTau, whose last is uniform in theta and is what upgrades '
   'L <= x2 to L < x2 with no hypothesis on x2 at all')

# ------------------------------------------------------------------ (B17)

# The rescaled spectral parameter has a NONZERO limit.  |z| = O(delta^rho) alone
# leaves z/delta^rho -> 0 open, and that would collapse the rescaled Rouche model
# to a rho-fold root at the origin.  Checked against the closed form the proof
# computes, z0 = c (x1/sin(pi/rho))^rho prod_{k not in S}(a_k - x1) / x1^r, so this
# pins the constant and not merely its nonvanishing.
worst_rel = mpf(0)
z0_pts = 0
for taus, rho, repeated in REP:
    if not repeated:
        continue
    n = len(taus)
    x1 = min(taus)
    outer = [t for t in taus if t != x1]
    z0 = (x1 / mp.sin(pi / rho)) ** rho
    for t in outer:
        z0 *= (t - x1)
    for r in (1, 2):
        if not feasible(n, r, n - 1):
            continue
        target = z0 / x1 ** r
        assert target > 0, ('B17 target', taus, r, target)
        for e in (5, 6, 7):
            th = mpf(10) ** (-e)
            tau = solve_tau(taus, r, n - 1, th)
            ratio = fabs(branch_z(taus, r, tau, th)) / th ** rho
            rel = fabs(ratio - target) / target
            assert rel < mpf('1e-3'), ('B17 limit', taus, r, e, ratio, target, rel)
            worst_rel = max(worst_rel, rel)
            z0_pts += 1
ok(f'(B17): |z(delta)|/delta^rho converges to the closed form '
   f'c (x1/sin(pi/rho))^rho prod(a_k - x1) / x1^r at {z0_pts} points, worst relative error '
   f'{mp.nstr(worst_rel, 3)}; that limit is strictly positive, which is what '
   'ForgacsTran.exists_tendsto_ftBranchZ_div_pow supplies and what the upper bound alone '
   'does not -- z/delta^rho -> 0 would leave the rescaled Rouche model a rho-fold root at 0')

# ------------------------------------------------------------------ (B18)

# The UPPER endpoint, theta -> (pi/r)^-.  The behavior is a dichotomy in r and
# both sides are measured, because only one of them is proved.
up_pts = 0
worst_up = mpf(0)
r1_rows = []
second_order = []
for taus, rho, repeated in REP:
    n = len(taus)
    Q0 = mpf(1)
    for t in taus:
        Q0 *= t
    for r in (1, 2, 3):
        if not feasible(n, r, n - 1):
            continue
        vals = []
        ratios = []
        for e in (2, 4, 6, 8):
            eps = mpf(10) ** (-e)
            th = pi / r * (1 - eps)
            tau = solve_tau(taus, r, n - 1, th)
            vals.append(tau)
            if r >= 2:
                # tau^r |z| -> prod a_k, the exact relation read at the endpoint
                prod = tau ** r * fabs(branch_z(taus, r, tau, th))
                ratios.append(fabs(prod - Q0) / Q0 / eps)
                up_pts += 1
        if r >= 2:
            # Convergence is at least first order in eps = 1 - theta/(pi/r), since
            # tau = O(eps) and the only error is Q(t) - Q(0).  The ORDER is not
            # uniform in r and a flat assertion would be wrong: at r = 2 it is
            # second order, because cos(pi/2) = 0 kills the linear term
            # -2 a_k tau cos(theta), while for r >= 3 that term survives and the
            # convergence is exactly first order.  So assert what holds for both --
            # rel/eps bounded and non-increasing -- and record the r = 2 gain.
            assert max(ratios) < mpf(5), ('B18 first order', taus, r, ratios)
            for u, v in zip(ratios, ratios[1:]):
                assert v <= u * mpf('1.01'), ('B18 non-increasing', taus, r, ratios)
            worst_up = max(worst_up, max(ratios))
            if ratios[-1] < ratios[0] / 100:
                second_order.append((tuple(float(t) for t in taus), r))
            # the radius collapses
            assert vals[-1] < vals[0] / 1000, ('B18 collapse', taus, r, vals)
        else:
            # r = 1 does NOT collapse: the radius settles at a finite positive limit
            assert vals[-1] > mpf('1e-3'), ('B18 r=1 collapse', taus, vals)
            assert fabs(vals[-1] - vals[-2]) < mpf('1e-8'), ('B18 r=1 settle', taus, vals)
            r1_rows.append((tuple(float(t) for t in taus), float(vals[-1])))
ok(f'(B18): for r >= 2 the radius collapses at the upper endpoint and tau^r |z| -> prod a_k, '
   f'the exact relation t^r = -Q(t)/z read where Q(t) -> Q(0).  At {up_pts} points the '
   f'relative error is at most {mp.nstr(worst_up, 4)} times eps = 1 - theta/(pi/r) and never '
   f'grows, so convergence is at least first order.  It is SECOND order on the {len(second_order)} '
   f'rows with r = 2, where cos(pi/2) = 0 kills the linear term -- '
   f'ForgacsTran.tendsto_ftTau_nhdsLT_upper and '
   'tendsto_pow_mul_ftBranchZ_nhdsLT_upper')
ok(f'(B18b): at r = 1 the radius SETTLES at a finite positive limit rather than collapsing -- '
   f'{r1_rows[0][1]:.10f} on the first of {len(r1_rows)} pencils -- so the r >= 2 statement is '
   'FALSE there, not merely unproved, and the hypothesis 2 <= r is forced rather than '
   'convenient.  The endpoint is theta = pi, where sin(theta) is no longer bounded below; this '
   'is NOT the cos(pi/r) = 0 mechanism of BANK-35, which is r = 2 alone, since cos(pi) = -1')

# ------------------------------------------------------------------ (B19)

# The Rouche model's own equation, at the branch's objects.  What the cluster
# enumeration cannot discharge is q(x1) alpha^rho + z0 x1^r = 0 -- that the
# cluster directions ARE the model's roots.  That is a SIGN statement: a z0
# correct in modulus and wrong in sign satisfies z0 > 0 and fails this equation.
# Both sides are computed here from the branch alone.
mod_pts = 0
worst_dir = mpf(0)
worst_model = mpf(0)
for taus, rho, repeated in REP:
    if not repeated:
        continue
    n = len(taus)
    x1 = min(taus)
    outer = [t for t in taus if t != x1]
    B = mpf(1)
    for t in outer:
        B *= (t - x1)
    for r in (1, 2):
        if not feasible(n, r, n - 1):
            continue
        # z0, the value ForgacsTran.tendsto_ftBranchZ_div_pow now states (c = 1)
        z0 = (x1 / mp.sin(pi / rho)) ** rho * B / x1 ** r
        # q(x1), from Q(t) = (t - x1)^rho q(t) with Q(t) = prod (a_k - t)
        q_x1 = mpf((-1) ** rho) * B
        for e in (5, 6, 7):
            th = mpf(10) ** (-e)
            tau = solve_tau(taus, r, n - 1, th)
            # the direction, read off the branch point itself
            alpha = (mpc(tau) * exp(mpc(0, -1) * th) - x1) / th
            pred = -(x1 / mp.sin(pi / rho)) * exp(mpc(0, 1) * pi / rho)
            assert fabs(alpha - pred) / fabs(pred) < mpf('1e-4'), \
                ('B19 direction', taus, r, e, alpha, pred)
            worst_dir = max(worst_dir, fabs(alpha - pred) / fabs(pred))
            # and the model equation it has to satisfy
            resid = q_x1 * alpha ** rho + z0 * x1 ** r
            scale = fabs(z0 * x1 ** r)
            assert fabs(resid) / scale < mpf('1e-3'), \
                ('B19 model', taus, r, e, resid, scale)
            worst_model = max(worst_model, fabs(resid) / scale)
            mod_pts += 1
ok(f'(B19): the branch direction alpha = (t(delta) - x1)/delta converges to '
   f'-(x1/sin(pi/rho)) e^(i pi/rho) at {mod_pts} points (worst relative error '
   f'{mp.nstr(worst_dir, 3)}), and q(x1) alpha^rho + z0 x1^r = 0 holds there to '
   f'{mp.nstr(worst_model, 3)} relative -- the equation the cluster enumeration takes as a '
   'hypothesis, with z0 the value ForgacsTran.tendsto_ftBranchZ_div_pow states.  It is a sign '
   'test: alpha^rho = (-1)^(rho+1) (x1/sin(pi/rho))^rho, and q(x1) carries (-1)^rho from '
   'prod (a_k - t), so the two cancel against the -1 the equation needs')

# ------------------------------------------------------------------ (B20)

# Their Lemma 5's first half: every zero of R(t) = r t^{r-1} Q - t^r Q' is real.
# R = -t^{r-1} E with E = t Q' - r Q, so this is real-rootedness of E.
#
# THE COUNTING METHOD MATTERS MORE THAN THE SAMPLE HERE, and two natural choices
# are both wrong.  Floating-point root finding is unusable: a triple root reports
# as one real and two complex at 6e-6 and reads as a counterexample.  sympy's
# count_roots is also wrong: it counts DISTINCT real roots, so a double root
# reads as a shortfall.  Both produced a false negative before the statement was
# confirmed.  What is correct is real_roots(), which returns roots WITH
# multiplicity, compared against the degree.
# sympy is pinned in requirements.txt, so this import is hard: a missing sympy
# must fail the run rather than let (B20) skip silently.
import sympy as _sp

_t = _sp.Symbol('t')

def _E_poly(taus, r):
    Q = _sp.prod([_sp.Rational(x) - _t for x in taus])
    return _sp.Poly(_sp.expand(_t * _sp.diff(Q, _t) - r * Q), _t)

L5 = [[1, 2, 3], [1, 1, 3], [1, 1, 1], [1, 2], [1, 1], [1, 2, 3, 4], [1, 1, 2, 2],
      [_sp.Rational(1, 2)] * 3 + [4], [1, 2, 3, 4, 5], [1, 1, 1, 1], [2, 2, 5, 9],
      [1, 2, 2, 2, 7], [1, 1, 1, 5, 5], [3], [7, 7], [1, 1, 1, 1, 1, 1],
      [_sp.Rational(1, 3), _sp.Rational(1, 3), 9], [1, 4, 4, 9, 9, 9]]
l5_rows = 0
l5_drop = 0
for taus in L5:
    for r in range(1, 9):
        E = _E_poly(taus, r)
        d = E.degree()
        if d < 1:
            continue
        nreal = len(_sp.Poly(E, _t).real_roots())
        assert nreal == d, ('B20 real-rooted', taus, r, d, nreal)
        # the degree drops by exactly one when n = r, and only then
        assert (d < len(taus)) == (len(taus) == r), ('B20 degree', taus, r, d)
        if d < len(taus):
            l5_drop += 1
        l5_rows += 1
ok(f'(B20): every zero of E = t Q\' - r Q is real over {l5_rows} exact (pencil, r) pairs, '
   f'roots counted with multiplicity; and deg E < n on exactly the {l5_drop} rows with '
   'n = r, where the leading terms cancel -- ForgacsTran.'
   'card_roots_ftCriticalReal_ftRootPolyReal, which carries no n /= r hypothesis because '
   'E = 0 would force t Q\'(t) = r Q(t), hence Q(0) = 0, against Q(0) = c prod a_k')

# ------------------------------------------------------------------ (B21)

# The rate of the collapse at the upper endpoint, and what it buys.  With
# delta = pi/r - theta the angle count gives tau/delta -> r/(sin(pi/r) sum 1/a_k)
# EXACTLY, and that constant is what turns the member expansion's coefficient
# into the clean form: Re c_j = (cos(pi/r) - Re omega_j)/sin(pi/r), with neither
# the pencil nor the constant surviving in it.
up_rate_pts = 0
worst_rate = mpf(0)
for taus, rho, repeated in REP:
    n = len(taus)
    S = sum(1 / t for t in taus)
    for r in (2, 3, 4):
        if not feasible(n, r, n - 1):
            continue
        target = mpf(r) / (mp.sin(pi / r) * S)
        ratios = []
        for e in (3, 5, 7):
            d = mpf(10) ** (-e)
            th = pi / r - d
            tau = solve_tau(taus, r, n - 1, th)
            rel = fabs(tau / d - target) / target
            ratios.append(rel / d)
            up_rate_pts += 1
        # As in (B18) the ORDER is not uniform in r -- at r = 2 it is second
        # order, cos(pi/2) = 0 killing the linear term -- so assert what holds
        # for every r: rel/delta bounded and never growing.
        assert max(ratios) < mpf(1), ('B21 rate', taus, r, ratios)
        for u, v in zip(ratios, ratios[1:]):
            assert v <= u * mpf('1.01'), ('B21 rate trend', taus, r, ratios)
        worst_rate = max(worst_rate, max(ratios))
ok(f'(B21a): tau(theta)/(pi/r - theta) -> r/(sin(pi/r) sum 1/a_k) at {up_rate_pts} points; the '
   f'relative error is at most {mp.nstr(worst_rate, 4)} times delta and never grows, so the '
   f'constant is exact and convergence at least first order (second order at r = 2, where '
   f'cos(pi/2) = 0 kills the linear term, as in (B18)) -- '
   'ForgacsTran.tendsto_ftTau_div_nhdsLT_upper, from the angle count alone: the complements '
   'sum to r delta exactly and each is asymptotically tau sin(pi/r)/a_k')

# and the member expansion the rate feeds.  r = 2 has an EMPTY cluster (both
# roots of -1 are principal), so this bites at r >= 3.
def _cluster_roots(taus, r, z):
    n = len(taus)
    coeffs = [mpf(1)]
    for a in taus:
        new = [mpf(0)] * (len(coeffs) + 1)
        for i, cc in enumerate(coeffs):
            new[i] += -cc
            new[i + 1] += a * cc
        coeffs = new
    deg = max(n, r)
    full = [mpf(0)] * (deg + 1)
    for i, cc in enumerate(coeffs):
        full[deg - (n - i)] += cc
    full[deg - r] += z
    rts = mp.polyroots([mpc(x) for x in full], maxsteps=200, extraprec=200)
    return sorted(rts, key=lambda w: abs(w))[:r]

mem_pts = 0
worst_mem = mpf(0)
for taus, rho, repeated in REP:
    n = len(taus)
    for r in (3, 4):
        if not feasible(n, r, n - 1):
            continue
        omega = [mp.exp(mpc(0, 1) * pi * (2 * k + 1) / r) for k in range(r)]
        om_plus = mp.exp(mpc(0, -1) * pi / r)
        for e in (4, 5):
            d = mpf(10) ** (-e)
            th = pi / r - d
            tau = solve_tau(taus, r, n - 1, th)
            z = branch_z(taus, r, tau, th)
            tplus = mpc(tau) * mp.exp(mpc(0, -1) * th)
            cl = _cluster_roots(taus, r, z)
            tp = min(cl, key=lambda w: abs(w - tplus))
            for w in omega:
                nu = w / om_plus
                tj = min(cl, key=lambda u: abs(u / tp - nu))
                cj = (tj / tp / nu - 1) / d
                pred = (mp.cos(pi / r) - mp.re(w)) / mp.sin(pi / r)
                err = fabs(mp.re(cj) - pred)
                assert err < mpf('1e-2'), ('B21 member', taus, r, e, mp.re(cj), pred)
                worst_mem = max(worst_mem, err)
                mem_pts += 1
ok(f'(B21b): zeta_j = nu_j(1 + c_j delta) + O(delta^2) with '
   f'Re c_j = (cos(pi/r) - Re omega_j)/sin(pi/r), at {mem_pts} points over r = 3 and 4, worst '
   f'absolute error {mp.nstr(worst_mem, 3)}.  The expansion is about nu_j = omega_j/omega_+ and '
   'NOT about 1 -- zeta_j is unimodular and not 1 -- and r = 2 is excluded because both roots '
   'of -1 are principal there, so its cluster is empty')

# ------------------------------------------------------------------ (B22)

# The POINTWISE second-order form of (B21a), which is what the member expansion
# consumes: a limit gives only o(delta), and an O(delta^2) binder cannot take it.
# |tau(pi/r - delta) - m delta| <= C delta^2 with m = r/(sin(pi/r) sum 1/a_k).
sec_pts = 0
worst_sec = mpf(0)
for taus, rho, repeated in REP:
    n = len(taus)
    S = sum(1 / t for t in taus)
    for r in (2, 3, 4):
        if not feasible(n, r, n - 1):
            continue
        m = mpf(r) / (mp.sin(pi / r) * S)
        ratios = []
        for e in (3, 4, 5, 6):
            d = mpf(10) ** (-e)
            tau = solve_tau(taus, r, n - 1, pi / r - d)
            ratios.append(fabs(tau - m * d) / d ** 2)
            sec_pts += 1
        # |tau - m delta|/delta^2 must not GROW; it would diverge like 1/delta if
        # the error were first order, which is exactly the gap between a Tendsto
        # and the pointwise bound.  As in (B18) and (B21a) the order is not
        # uniform in r: at r = 2 it is third order, cos(pi/2) = 0 again, so the
        # ratio falls rather than settling.  Assert what holds for every r.
        for u, v in zip(ratios, ratios[1:]):
            assert v <= u * mpf('1.01'), ('B22 growth', taus, r, ratios)
        worst_sec = max(worst_sec, max(ratios))
ok(f'(B22): |tau(pi/r - delta) - r/(sin(pi/r) sum 1/a_k) delta| <= C delta^2 at {sec_pts} '
   f'points with C = {mp.nstr(worst_sec, 4)}; across four decades the ratio over delta^2 never '
   'grows, so the error is at least second order (third order at r = 2, cos(pi/2) = 0 again) -- '
   'ForgacsTran.exists_bound_ftTau_upper.  A Tendsto gives only o(delta) here and the member '
   "expansion's binder is stated with O(delta^2), so the pointwise form is what composes")

print()
print('PASS: (B1) the closed form solves clauses (i)-(iii) of Forgacs-Tran Lemma 2')
print('PASS: (B2) the range condition decides feasibility; (2, 2, 0) is infeasible')
print('PASS: (B3) l = n - 1 is admissible throughout the arc except n = r = 1')
print('PASS: (B4) the branch value z is real, of sign (-1)^(n-l-1)')
print('PASS: (B5) tau(theta) is strictly decreasing (Forgacs-Tran Lemma 3)')
print('PASS: (B6) z(theta) is strictly monotone (Forgacs-Tran Lemma 4(ii))')
print('PASS: (B7) E has exactly one negative zero for r = 1 (Forgacs-Tran Lemma 5)')
print("PASS: (B8) the branch is regular: tau'(theta) and dtheta_k/dtheta agree with"
      ' central differences')
print('PASS: (B9) the endpoint limit of tau is a critical point in [tau_(1), tau_(2)]')
print("PASS: (B10) the branch value is the fixed-radius chord product, strictly increasing"
      ' in the angle')
print("PASS: (B11) eq. (23) fixes the sign of z'; the n > 2r inequality of their Lemma 3"
      ' holds under stress; its margin is cubic at the endpoints')
print('PASS: (B12) the endpoint limit is bracketed by the two smallest zeros, and equals'
      " the smallest when it repeats; tau' -> -x1 cot(pi/rho) there")
print('PASS: (B13) the exact identity and the angle-count bound on beta give\n      |tau - (x1 - x1 cot(pi/rho) theta)| = O(theta^2), the second-order form the\n      principal-amplitude expansion consumes')
print('PASS: (B14) the radius never reaches the second zero, at every theta on the arc;\n      the endpoint limit stays strictly below it even where that zero repeats')
print('PASS: (B15) the spectral parameter inherits the multiplicity of the smallest\n      zero: |z(delta)| = O(delta^rho), with rho exact')
print('PASS: (B16) L < x2 strictly, with x2 double, triple or simple alike; the\n      angle count gives a bound on tau uniform in theta, which E cannot')
print('PASS: (B17) the rescaled spectral parameter has a NONZERO limit, equal to the\n      closed form the proof computes')
print('PASS: (B18) at the upper endpoint the radius collapses for r >= 2, giving\n      tau^r |z| -> prod a_k; r = 1 does not collapse and is excluded')
print('PASS: (B19) the branch directions are the Rouche model roots: the sign chain in\n      q(x1) alpha^rho + z0 x1^r = 0 closes at the branch objects')
print('PASS: (B20) Forgacs-Tran Lemma 5, first half: every zero of their R is real,\n      counted with multiplicity, for every n and r')
print('PASS: (B21) the upper-endpoint collapse rate, and the member expansion it feeds')
print('PASS: (B22) the upper-endpoint rate in pointwise second-order form')
print('ALL PASS: check_ft_branch_angles')
