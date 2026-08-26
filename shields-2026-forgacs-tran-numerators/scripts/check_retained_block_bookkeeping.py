#!/usr/bin/env python3
r"""Paper section `subsec:proof`, `eq:Omega-M`, `eq:angular-distinct-lower`;
and `sec:dominance`, `eq:amplitude-deletion`, `eq:retained-range`.

`subsec:proof` counts "on each component of `Omega_M cap (alpha,beta)`" and then
sums.  Turning that sentence into a proof means naming the components, and the
naming is where the arithmetic can go wrong silently: a block can be cut so that
it lies inside a neighbor's deleted window, or outside the collar
`[h/M, pi/r - h/M]` entirely, and in either case `eq:dominance-bound` says
nothing on it while the length bookkeeping still charges its length.  This
script tests the construction the formalization uses and the two facts that make
it safe.

The blocks are cut at `theta_j -+ rho` with ONE common half-width `rho`, and each
cut point is projected onto `[A, b]`, `A = max(alpha, h/M)`,
`b = min(beta, pi/r - h/M)`.

Asserted, each as a failing test:

  (B1) The common half-width is an enlargement, not a change of statement:
       `exp(-cM/nu_j) <= exp(-cM/N)` for `nu_j <= N`, so the union of the
       enlarged windows contains `Omega_M`'s own, and the enlarged total length
       is still exponentially small.
  (B2) It is also NECESSARY.  With the per-zero half-widths of
       `eq:amplitude-deletion` the naive cut produces a block of positive length
       that MEETS a wider neighbor's window, where `eq:dominance-bound` says
       nothing -- exhibited, with the offending block located, and repaired by
       the common radius.
  (B3) The clamped block lengths telescope EXACTLY to
       `(b - A) - sum_j (clamp(theta_j+rho) - clamp(theta_j-rho))`, and the
       projection being 1-Lipschitz gives `sum len >= (b - A) - 2 rho J`.
       Both over randomized configurations, including windows straddling either
       endpoint and windows lying wholly outside `[A,b]`.
  (B4) The clamp is NECESSARY: a divisor point below the collar's left edge
       leaves, without it, a block of positive length lying wholly outside
       `[A,b]`, where `eq:dominance-bound` is not available while the length
       bookkeeping still charges it -- exhibited.
  (B5) Every block of positive length avoids every deleted window, and the
       blocks are ordered end to end.  Randomized.
  (B6) The dichotomy that lets a short block carry no count: if the phase turns
       by less than `pi` across a block -- below the hypothesis of the phase
       count -- then `(M+1)|I|/pi - Var_I psi/pi - 2 < 0`, so nothing is owed.
       Randomized.  SOME subtraction is needed (configurations with turning
       under `pi` and `(M+1)|I|/pi - Var/pi > 0` are exhibited); at this step
       alone `-1` would also serve, and it is (B8) that pins the `-2`.
  (B7) The collar case: when `A > b` the window is swallowed, and then
       `beta - alpha <= 2h/M`, hence `(M+1)(beta-alpha)/pi <= 4h/pi <= C_0`.
       Randomized over the four ways `A > b` can happen.
  (B8) End to end on a model amplitude.  With `z(theta) = theta` on `(0, pi)`,
       an amplitude `|W| = prod_j |theta - theta_j|` vanishing at the divisor, a
       branch `psi` whose total variation grows linearly in the number of
       divisor points, and a remainder at exactly the `eq:dominance-bound`
       ceiling `|W|/2` on the retained set (and above it inside the windows, so
       the deletion is doing work), the sign changes of
       `2|W| cos Phi_M + R` on the retained blocks satisfy both
       `n_i >= (M+1)|I_i|/pi - Var_i/pi - 2` per block and the assembled
       `sum_i n_i >= (M+1)(beta-alpha)/pi - C_0 - C_1 K` with
       `C_0 = (4h+1+kappa_0)/pi + 2`, `C_1 = kappa_1/pi + 2`.
  (B8b) The `-2` is attained.  With both endpoints of a retained interval
       placed just inside `pi Z`, the alternation delivers `L/pi - 2 + O(eps)`
       gaps and `-1` in its place is false.  Every gap is confirmed to carry a
       genuine sign change.  The realized number of zeros is about `L/pi`,
       since the sign changes sit at `Phi = pi/2 mod pi` rather than at the
       phase points -- which is why (B8) never sees the constant bind, and why
       it is pinned here against the phase-point count.

  (B9) `eq:phase-derivative-bound` does not move with the collar.  Every place
       `W` degenerates along the arc it degenerates through a REAL factor --
       `(theta-theta_j)^nu_j` at an amplitude zero, `delta^p` at an endpoint --
       and a real factor contributes `rho'/rho` to the logarithmic derivative,
       hence nothing to its imaginary part.  So `psi' = Im(W'/W)` equals the
       cofactor's contribution alone, and `sup |psi'|` over the collar
       `[h/M, b]` is FLAT in `M` rather than growing.  Checked against a
       numerically differentiated `W` with `p = -2`, so the natural-number form
       does not reach it; and the check is shown to have teeth by exhibiting a
       COMPLEX factor `e^{i/theta}` of the same modulus profile, for which the
       same sup grows like `M^2`.

`mpmath` throughout; no float64 comparison anywhere.
"""

from mpmath import mp, mpf, mpc, sin, cos, exp, atan, pi, fabs, sqrt, diff, j as I

mp.dps = 40

PIm = pi


# ---------------------------------------------------------------- helpers


def clamp(A, b, x):
    """Projection onto `[A, b]` -- `AngularBlocks.clampTo`."""
    return min(b, max(A, x))


def block_left(A, b, rho, e, i):
    """`AngularBlocks.blockLeft`."""
    return A if i == 0 else clamp(A, b, e[i - 1] + rho)


def block_right(A, b, rho, e, J, i):
    """`AngularBlocks.blockRight`."""
    return b if i == J else clamp(A, b, e[i] - rho)


def blocks(A, b, rho, e):
    J = len(e)
    return [(block_left(A, b, rho, e, i), block_right(A, b, rho, e, J, i))
            for i in range(J + 1)]


def window_radius(sigma, card_S, nu, M):
    """`AngularBookkeeping.windowRadius`, `eq:amplitude-deletion`."""
    c = (-mp.log(sigma)) / (2 * card_S)
    return exp(-(c * M / nu))


class Rng:
    """Deterministic LCG, so the sweeps are reproducible without `random`."""

    def __init__(self, seed):
        self.s = seed

    def next(self):
        self.s = (self.s * 6364136223846793005 + 1442695040888963407) % (2 ** 64)
        return self.s

    def unit(self):
        return mpf(self.next() % (2 ** 32)) / mpf(2 ** 32)

    def between(self, lo, hi):
        return lo + (hi - lo) * self.unit()

    def below(self, n):
        return self.next() % n


# ---------------------------------------------------------------- (B1)


def check_common_radius_is_an_enlargement():
    sigma = mpf('0.37')
    S = [mpf('0.4'), mpf('1.1'), mpf('2.0'), mpf('2.6')]
    nus = [1, 3, 2, 5]
    N = max(nus)
    worst_ratio = mpf(0)
    for M in [10, 25, 60, 140, 300]:
        common = window_radius(sigma, len(S), N, M)
        for nu in nus:
            own = window_radius(sigma, len(S), nu, M)
            assert own <= common, (
                "per-zero half-width exceeds the common one at "
                "M=%s nu=%s: %s > %s" % (M, nu, own, common))
            worst_ratio = max(worst_ratio, common / own)
    # `eq:amplitude-window-negligible` for the ENLARGED family: eventual, with
    # the threshold located rather than assumed
    thresh = None
    for M in range(1, 4001):
        total = 2 * len(S) * window_radius(sigma, len(S), N, M)
        if (M + 1) * total <= 1:
            thresh = M
            break
    assert thresh is not None, (
        "the enlarged deleted family never satisfies "
        "eq:amplitude-window-negligible below M = 4000")
    for M in [thresh, thresh + 50, thresh + 500, 4000]:
        total = 2 * len(S) * window_radius(sigma, len(S), N, M)
        assert (M + 1) * total <= 1, (
            "eq:amplitude-window-negligible fails for the ENLARGED family at "
            "M=%s: (M+1)*total = %s" % (M, (M + 1) * total))
    big = 2 * len(S) * window_radius(sigma, len(S), N, 4000)
    assert 4001 * big < mpf('1e-8'), (
        "the enlarged deleted length is not exponentially small: %s" % big)
    return worst_ratio, big, thresh


# ---------------------------------------------------------------- (B2)


def check_per_zero_radii_break_the_decomposition():
    """A nested pair of windows: the block between them lies inside the wider."""
    A, b = mpf(0), mpf(4)
    e = [mpf('1.0'), mpf('1.4')]
    rho = [mpf('0.9'), mpf('0.05')]          # window 0 is much wider
    # the naive cut, one radius per zero
    lefts = [A] + [e[i] + rho[i] for i in range(len(e))]
    rights = [e[i] - rho[i] for i in range(len(e))] + [b]
    offenders = []
    for i in range(len(e) + 1):
        L, R = lefts[i], rights[i]
        if L >= R:
            continue
        for j in range(len(e)):
            if L < e[j] + rho[j] and R > e[j] - rho[j]:
                offenders.append((i, j, L, R))
    assert offenders, (
        "per-zero half-widths were expected to leave a block meeting a window "
        "and did not; the common-radius step in AngularBlocks would then be "
        "unmotivated")
    # the common radius repairs it
    rho_c = max(rho)
    for (L, R) in blocks(A, b, rho_c, e):
        if L >= R:
            continue
        for j in range(len(e)):
            assert not (L < e[j] + rho_c and R > e[j] - rho_c), (
                "the common radius still leaves block [%s,%s] meeting window %s"
                % (L, R, j))
    return offenders


# ---------------------------------------------------------------- (B3), (B5)


def check_telescoping_and_avoidance(trials=400):
    rng = Rng(20260826)
    worst_slack = mpf('1e9')
    for _ in range(trials):
        A = rng.between(mpf(0), mpf(2))
        b = A + rng.between(mpf(0), mpf(3))
        rho = rng.between(mpf('0.001'), mpf('0.35'))
        J = int(rng.below(6))
        # centers anywhere near the interval, so windows straddle and overshoot
        raw = sorted(rng.between(A - 1, b + 1) for _ in range(J))
        e = raw
        bl = blocks(A, b, rho, e)
        # exact telescoping
        total = sum(R - L for (L, R) in bl)
        deleted = sum(clamp(A, b, ej + rho) - clamp(A, b, ej - rho) for ej in e)
        assert fabs(total - ((b - A) - deleted)) < mpf('1e-30'), (
            "telescoping identity failed: %s vs %s"
            % (total, (b - A) - deleted))
        # the 1-Lipschitz bound
        assert (b - A) - 2 * rho * J <= total + mpf('1e-30'), (
            "sum of block lengths below (b-A) - 2*rho*J: %s < %s"
            % (total, (b - A) - 2 * rho * J))
        worst_slack = min(worst_slack, total - ((b - A) - 2 * rho * J))
        # ordering, containment and avoidance
        for i in range(J + 1):
            L, R = bl[i]
            assert A <= L <= b and A <= R <= b, (
                "block endpoint outside [A,b]: %s %s" % (L, R))
            if i < J:
                assert R <= bl[i + 1][0] + mpf('1e-30'), (
                    "blocks out of order at i=%s" % i)
            if L >= R:
                continue
            for j in range(J):
                for theta in (L, R, (L + R) / 2):
                    assert fabs(theta - e[j]) >= rho - mpf('1e-30'), (
                        "block %s of positive length meets window %s: "
                        "|%s - %s| = %s < %s"
                        % (i, j, theta, e[j], fabs(theta - e[j]), rho))
    return worst_slack


# ---------------------------------------------------------------- (B4)


def check_clamp_is_necessary():
    """Divisor points below the collar leave an unclamped block outside `[A,b]`."""
    A, b = mpf(1), mpf(3)
    rho = mpf('0.1')
    e = [mpf('0.2'), mpf('0.9')]     # both centers below the collar's left edge
    # unclamped cut
    lefts = [A] + [ej + rho for ej in e]
    rights = [ej - rho for ej in e] + [b]
    outside = []
    for i in range(len(e) + 1):
        L, R = lefts[i], rights[i]
        if L < R and (R < A or L > b):
            outside.append((i, L, R, R - L))
    assert outside, (
        "expected an unclamped block of positive length outside [A,b]; "
        "without one the clamp in AngularBlocks would be unmotivated")
    # clamped: nothing of positive length escapes
    for (L, R) in blocks(A, b, rho, e):
        if L < R:
            assert A <= L and R <= b, (
                "clamped block [%s,%s] escaped [%s,%s]" % (L, R, A, b))
    return outside


# ---------------------------------------------------------------- (B6)


def check_short_block_owes_nothing(trials=600):
    """Turning below `pi` forces `(M+1)|I|/pi - Var/pi - 2 < 0`."""
    rng = Rng(777001)
    worst = mpf('-1e9')
    worst_bare = mpf('-1e9')
    seen = 0
    for _ in range(trials):
        M = int(rng.below(400)) + 1
        length = rng.between(mpf(0), mpf('4'))
        var = rng.between(mpf(0), mpf('30'))
        turning = (M + 1) * length - var
        if turning >= PIm:
            continue
        seen += 1
        owed = (M + 1) * length / PIm - var / PIm - 2
        assert owed < 0, (
            "a block turning by %s < pi is owed %s zeros" % (turning, owed))
        worst = max(worst, owed)
        worst_bare = max(worst_bare, (M + 1) * length / PIm - var / PIm)
    assert seen > 0, "no short block was generated"
    assert worst_bare > 0, (
        "with no constant subtracted the inequality still held everywhere, so "
        "the sweep does not show that a constant is needed at all")
    return worst, worst_bare, seen


# ---------------------------------------------------------------- (B7)


def check_collar_swallows(trials=800):
    rng = Rng(31337)
    seen = [0, 0, 0, 0]
    worst = mpf('-1e9')
    for _ in range(trials):
        M = int(rng.below(60)) + 1
        h = rng.between(mpf(0), mpf(3))
        bnd = rng.between(mpf('0.2'), mpf(4))
        alpha = rng.between(mpf(0), bnd)
        beta = rng.between(alpha, bnd)
        A = max(alpha, h / M)
        Bd = min(beta, bnd - h / M)
        if A <= Bd:
            continue
        # which of the four ways
        if beta < h / M:
            seen[0] += 1
        elif bnd - h / M < alpha:
            seen[1] += 1
        elif bnd - h / M < h / M:
            seen[2] += 1
        else:
            seen[3] += 1
        assert beta - alpha <= 2 * h / M + mpf('1e-30'), (
            "A > b but beta-alpha = %s exceeds 2h/M = %s"
            % (beta - alpha, 2 * h / M))
        assert (M + 1) * (beta - alpha) <= 4 * h + mpf('1e-30'), (
            "(M+1)(beta-alpha) = %s exceeds 4h = %s"
            % ((M + 1) * (beta - alpha), 4 * h))
        C0 = (4 * h + 1 + mpf(0)) / PIm + 2
        slack = C0 - (M + 1) * (beta - alpha) / PIm
        assert slack >= 0, "C_0 does not absorb the swallowed window: %s" % slack
        worst = max(worst, -slack)
    assert seen[3] == 0, (
        "a fifth way for A > b appeared, which the Lean case split does not "
        "cover: %s" % seen)
    assert sum(seen) > 0, "no degenerate configuration was generated"
    return seen, worst


# ---------------------------------------------------------------- (B8)


class Model:
    """`z(theta) = theta` on `(0, pi)`; amplitude vanishing at the divisor."""

    def __init__(self, thetas, csin=mpf('0.35'), eps=mpf('0.2')):
        self.thetas = thetas
        self.csin = csin
        self.eps = eps

    def psi(self, t):
        v = self.csin * sin(3 * t)
        for tj in self.thetas:
            v += atan((t - tj) / self.eps)
        return v

    def dpsi(self, t):
        v = 3 * self.csin * cos(3 * t)
        for tj in self.thetas:
            v += self.eps / (self.eps ** 2 + (t - tj) ** 2)
        return v

    def absW(self, t):
        v = mpf(1)
        for tj in self.thetas:
            v *= fabs(t - tj)
        return v

    def kappa(self):
        # |psi'| <= 3c + J/eps
        return 3 * self.csin + mpf(len(self.thetas)) / self.eps

    def kappa0(self):
        # total variation of the smooth part on (0, pi)
        return 3 * self.csin * mpf(2)          # |cos| integrates to 2 over 3 arcs

    def kappa1(self):
        return PIm                              # each atan sweeps under pi

    def var_on(self, L, R, n=400):
        """Variation of psi over [L,R], by |psi'| quadrature."""
        if R <= L:
            return mpf(0)
        acc = mpf(0)
        step = (R - L) / n
        for k in range(n):
            a = L + k * step
            acc += fabs(self.dpsi(a + step / 2)) * step
        return acc


def sign_changes(f, L, R, samples):
    if R <= L:
        return 0
    prev = f(L)
    n = 0
    step = (R - L) / samples
    for k in range(1, samples + 1):
        cur = f(L + k * step)
        if prev * cur < 0:
            n += 1
        if cur != 0:
            prev = cur
    return n


def check_end_to_end():
    thetas = [mpf('0.7'), mpf('1.9'), mpf('2.6')]
    J = len(thetas)
    K = J                                   # deg B >= J, taken at equality
    model = Model(thetas)
    bnd = PIm
    h = mpf('0.6')
    kappa0, kappa1 = model.kappa0(), model.kappa1()
    C0 = (4 * h + 1 + kappa0) / PIm + 2
    C1 = kappa1 / PIm + 2
    results = []
    for M in [40, 61, 90]:
        assert model.kappa() < M + 1, (
            "eq:phase-derivative-bound fails at M=%s: kappa=%s" % (M, model.kappa()))
        rho = mpf('0.02')
        assert (M + 1) * (2 * rho * J) > 0
        for (alpha, beta) in [(mpf(0), bnd), (mpf('0.3'), mpf('2.9')),
                              (mpf('1.0'), mpf('2.2'))]:
            A = max(alpha, h / M)
            Bd = min(beta, bnd - h / M)
            if A > Bd:
                continue
            e = [t for t in thetas]
            bl = blocks(A, Bd, rho, e)
            # the remainder sits exactly at the dominance ceiling on the
            # retained set and ABOVE it inside the windows
            floor = rho ** J

            def Rem(t, floor=floor):
                return mpf('0.49') * max(model.absW(t), floor) * sin(7 * t + 1)

            def F(t, M=M):
                Phi = (M + 1) * t - model.psi(t)
                return 2 * model.absW(t) * cos(Phi) + Rem(t)

            # dominance really does hold on every retained block, and really
            # does fail at the divisor points
            for (L, R) in bl:
                if L >= R:
                    continue
                for t in (L, (L + R) / 2, R):
                    assert fabs(Rem(t)) <= model.absW(t) / 2 + mpf('1e-25'), (
                        "eq:dominance-bound fails on a retained block at %s" % t)
            for tj in thetas:
                assert fabs(Rem(tj)) > model.absW(tj) / 2, (
                    "the remainder does not exceed |W|/2 at the divisor point "
                    "%s, so the deleted windows are doing no work" % tj)

            total_n = mpf(0)
            worst_block = mpf('-1e9')
            worst_block_one = mpf('-1e9')
            for (L, R) in bl:
                if L >= R:
                    continue
                var = model.var_on(L, R)
                span = R - L
                samples = int(60 * (M + 1) * span / (2 * PIm)) + 60
                n = sign_changes(F, L, R, samples)
                owed = (M + 1) * span / PIm - var / PIm - 2
                assert mpf(n) >= owed - mpf('1e-20'), (
                    "per-block count fails on [%s,%s] at M=%s: n=%s owed=%s"
                    % (L, R, M, n, owed))
                worst_block = max(worst_block, owed - n)
                worst_block_one = max(worst_block_one, owed + 1 - n)
                total_n += n
            bound = (M + 1) * (beta - alpha) / PIm - C0 - C1 * K
            assert total_n >= bound, (
                "eq:angular-distinct-lower fails at M=%s window (%s,%s): "
                "sum n = %s but the bound is %s" % (M, alpha, beta, total_n, bound))
            results.append((M, alpha, beta, total_n, bound,
                            total_n - bound, worst_block, worst_block_one))
    assert all(r[5] >= 0 for r in results)
    return C0, C1, results


def bisect(f, lo, hi, iters=200):
    flo = f(lo)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if f(mid) * flo <= 0:
            hi = mid
        else:
            lo = mid
            flo = f(lo)
    return (lo + hi) / 2


def check_minus_two_is_tight():
    """The `-2` of `exists_phase_points_of_length` is attained, not slack.

    Place both endpoints of a retained interval just inside `pi Z`: the phase
    then meets `pi Z` at `k'-k-1` interior points, so the alternation delivers
    `L/pi - 2 + O(eps)` gaps and `-1` in its place is false.  The realized
    number of zeros is larger -- the sign changes of `2|W| cos Phi + R` sit at
    `Phi = pi/2 mod pi`, so there are about `L/pi` of them -- which is why the
    block sweep of (B8) never sees the constant bind, and why it is pinned here
    against the phase-point count rather than against a zero count.
    """
    thetas = [mpf('0.7'), mpf('1.9'), mpf('2.6')]
    model = Model(thetas)
    M = 61
    eps = mpf('1e-6')

    def Phi(t):
        return (M + 1) * t - model.psi(t)

    def F(t):
        return 2 * model.absW(t) * cos(Phi(t)) \
            + mpf('0.49') * model.absW(t) * sin(7 * t + 1)

    p, q = mpf('1.0'), mpf('1.8')
    k = int(mp.ceil(Phi(p) / PIm))
    kp = int(mp.floor(Phi(q) / PIm))
    assert kp - k >= 3, "the probe interval is too short to pin the constant"
    L = bisect(lambda t: Phi(t) - (k * PIm + eps), p, q)
    R = bisect(lambda t: Phi(t) - (kp * PIm - eps), L, q)
    turning = Phi(R) - Phi(L)
    lo = int(mp.ceil(Phi(L) / PIm))
    hi = int(mp.floor(Phi(R) / PIm))
    gaps = hi - lo
    assert mpf(gaps) >= turning / PIm - 2, (
        "the phase-point count fails at the tight configuration: gaps=%s, "
        "L/pi-2=%s" % (gaps, turning / PIm - 2))
    assert mpf(gaps) < turning / PIm - 1, (
        "`-1` would have sufficed at the tight configuration too: gaps=%s, "
        "L/pi-1=%s -- the `-2` is then not pinned by this check"
        % (gaps, turning / PIm - 1))
    # every gap really carries a zero of `F`, so the count is a genuine lower
    # bound on distinct zeros and not merely on phase points
    xs = [bisect(lambda t, m=m: Phi(t) - m * PIm, L, R)
          for m in range(lo, hi + 1)]
    for i in range(gaps):
        assert F(xs[i]) * F(xs[i + 1]) < 0, (
            "consecutive phase points do not alternate at index %s" % i)
    span = R - L
    samples = int(200 * (M + 1) * span / (2 * PIm)) + 200
    n_actual = sign_changes(F, L, R, samples)
    assert n_actual >= gaps, (
        "fewer sign changes (%s) than gaps (%s)" % (n_actual, gaps))
    return gaps, turning / PIm, n_actual


# ---------------------------------------------------------------- (B9)


def _V(t):
    """An analytic nonvanishing cofactor: modulus `1+0.3t`, phase `0.4 sin 2t`."""
    return (1 + mpf('0.3') * t) * exp(I * mpf('0.4') * sin(2 * t))


def _im_log_deriv(f, t):
    """`Im(f'/f)` at `t`, by numerical differentiation -- not a closed form."""
    return (diff(f, t) / f(t)).imag


def check_phase_deriv_bound_flat_in_collar():
    """A real degeneracy leaves `sup|psi'|` on `[h/M, b]` flat in `M`."""
    b = mpf('1.4')
    h = mpf('0.6')
    p = -2                                    # negative: the nat-power form misses it

    def W(t):
        return t ** p * _V(t)

    def Wbad(t):                              # same modulus profile, COMPLEX factor
        return t ** p * exp(I / t) * _V(t)

    # the real factor really does drop out: Im(W'/W) = Im(V'/V) pointwise
    worst = mpf(0)
    for k in range(1, 15):
        t = mpf('0.05') + mpf(k) * mpf('0.09')
        worst = max(worst, fabs(_im_log_deriv(W, t) - _im_log_deriv(_V, t)))
    assert worst < mpf('1e-15'), (
        "the real factor did not drop out of Im(W'/W); worst gap %s" % worst)

    def sup_on_collar(f, M, n=60):
        lo = h / M
        acc = mpf(0)
        for k in range(n + 1):
            t = lo + (b - lo) * mpf(k) / n
            acc = max(acc, fabs(_im_log_deriv(f, t)))
        return acc

    Ms = [4, 16, 64, 256, 1024]
    good = [sup_on_collar(W, M) for M in Ms]
    bad = [sup_on_collar(Wbad, M) for M in Ms]
    # flat: the collar sup never exceeds the closed-arc sup of the cofactor
    ceiling = mpf('0.8') + mpf('1e-12')       # sup |0.8 cos 2t| over the arc
    for M, g in zip(Ms, good):
        assert g <= ceiling, (
            "the collar sup exceeded the cofactor's own bound at M=%s: %s > %s"
            % (M, g, ceiling))
        assert g < (M + 1), (
            "the collar sup is not below M+1 at M=%s: %s" % (M, g))
    assert good[-1] - good[0] < mpf('0.05'), (
        "the collar sup is not flat in M: %s -> %s" % (good[0], good[-1]))
    # teeth: a complex factor of the same modulus profile DOES grow, quadratically
    assert bad[-1] > 100 * bad[0], (
        "the complex-factor control did not grow, so the check cannot tell a "
        "real degeneracy from a complex one: %s -> %s" % (bad[0], bad[-1]))
    assert bad[-1] > (Ms[-1] + 1), (
        "the complex-factor control never breaks `kappa < M+1`, so the sweep "
        "does not show what the realness is buying: %s at M=%s"
        % (bad[-1], Ms[-1]))
    return good, bad, Ms


# ---------------------------------------------------------------- main


def main():
    print("check_retained_block_bookkeeping.py -- `subsec:proof`, `eq:Omega-M`")
    print()

    ratio, big, thresh = check_common_radius_is_an_enlargement()
    print("(B1) common half-width dominates every per-zero one; worst ratio "
          "%s. eq:amplitude-window-negligible holds for the ENLARGED family "
          "from M = %d, and (M+1)*length at M=4000 is %s"
          % (mp.nstr(ratio, 6), thresh, mp.nstr(4001 * big, 4)))

    off = check_per_zero_radii_break_the_decomposition()
    print("(B2) per-zero half-widths leave a block meeting a window: "
          "block %d meets window %d, [%s, %s]"
          % (off[0][0], off[0][1], mp.nstr(off[0][2], 6), mp.nstr(off[0][3], 6)))

    slack = check_telescoping_and_avoidance()
    print("(B3)/(B5) telescoping exact and blocks ordered and window-free over "
          "400 random configurations; tightest slack over (b-A)-2*rho*J is %s"
          % mp.nstr(slack, 6))

    outside = check_clamp_is_necessary()
    print("(B4) without the clamp, block %d has length %s and lies outside "
          "[A,b]" % (outside[0][0], mp.nstr(outside[0][3], 6)))

    worst, worst_bare, seen = check_short_block_owes_nothing()
    print("(B6) over %d short blocks, one turning by less than pi is owed at "
          "most %s zeros; with no constant subtracted it would be owed up to %s"
          % (seen, mp.nstr(worst, 6), mp.nstr(worst_bare, 6)))

    seen, w = check_collar_swallows()
    print("(B7) the four ways A > b occur %s times; C_0 absorbs every swallowed "
          "window with margin %s" % (seen[:3], mp.nstr(-w, 6)))

    C0, C1, res = check_end_to_end()
    print("(B8) end to end, C_0 = %s, C_1 = %s:" % (mp.nstr(C0, 6), mp.nstr(C1, 6)))
    for (M, a, b_, tot, bd, sl, wb, wb1) in res:
        print("     M=%3d window (%s, %s): sum n = %s, bound = %s, slack = %s"
              % (M, mp.nstr(a, 4), mp.nstr(b_, 4), mp.nstr(tot, 6),
                 mp.nstr(bd, 6), mp.nstr(sl, 6)))
    print("     worst per-block deficit with `-2`: %s; with `-1`: %s"
          % (mp.nstr(max(r[6] for r in res), 6),
             mp.nstr(max(r[7] for r in res), 6)))

    gaps, Lpi, n_actual = check_minus_two_is_tight()
    print("(B8b) at the tight configuration the phase count delivers %d gaps "
          "against L/pi = %s: `-2` holds and `-1` fails; the interval in fact "
          "carries %d zeros, which is why (B8) never sees the constant bind"
          % (gaps, mp.nstr(Lpi, 8), n_actual))

    good, bad, Ms = check_phase_deriv_bound_flat_in_collar()
    print("(B9) a REAL degeneracy leaves sup|psi'| on [h/M, b] flat in M: %s "
          "at M = %s; a complex factor of the same modulus profile grows %s -> %s"
          % (", ".join(mp.nstr(g, 5) for g in good), Ms,
             mp.nstr(bad[0], 5), mp.nstr(bad[-1], 5)))

    print()
    print("ALL PASS")


if __name__ == "__main__":
    main()
