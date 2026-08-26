#!/usr/bin/env python3
r"""Paper section `sec:consequences` (Global and local zero laws), section `subsec:strong-clock`
`subsec:strong-clock`, `prop:local-strong-clock`.

Local phase quantization and strong-clock spacing on zero-free co-dominant subarcs.

Checks `prop:local-strong-clock` claim by claim against the coefficient
recurrence, on three admissible configurations.  Everything is computed from

    F_M(z) = [t^M] B(t) / (Q(t) + z t^r)

at arbitrary precision; no float64 enters a verification loop.

The assertions, in the order the proof establishes them:

  (A) `eq:C1-interior-remainder`  ||R_M||_{C^1} = O(M sigma^M) on a compact
      zero-free subarc, with the log-slope in M measured and the M-prefactor
      exhibited.
  (B) `eq:local-phase-quantization`  Phi_M(theta_k) = (k+1/2)pi + O(sigma^M),
      with the exponential rate measured, and one zero per half-integer phase
      point over the subarc (no extra zeros, none missing).
  (C) simplicity of each corresponding zero of F_M as a polynomial in z.
  (D) `eq:local-strong-clock`  the spacing law with the psi' correction, whose
      residual must fall at log-log slope 3.  Dropping the correction must
      degrade the slope to 2 -- that comparison is the mutation test, run
      inline, so the correction term is shown load-bearing and not decorative.
  (E) `eq:W-on-g` and `eq:numerator-clock-correction`  the amplitude on the
      denominator curve, W = B(gamma)/(gamma^r g'(gamma)), and the resulting
      split of psi' = Im(W'/W) into a denominator-only term and the numerator's
      logarithmic derivative Im(B'(gamma) gamma'/B(gamma)).  Checked over three
      weights on ONE denominator: the split holds for each, the denominator-only
      term is identical across all three, and at a constant weight the
      correction vanishes and psi' reduces to it -- which is the sense in which
      the leading clock is denominator-universal and B first enters at order
      M^-2.
  (F) `eq:residue-amplitude` and `eq:W-def`  the residue amplitude
      W = -B/d_t D at EVERY denominator root, against the derivative read off
      the factored denominator and against the residue as a contour integral,
      so the display's sign and normalization are pinned by two routes that do
      not differentiate the coefficients of D at all.  This is the display (E)
      rewrites on the denominator curve, so it is checked ahead of it.

Configuration Q1 (deg Q = 2, r = 1) is the case where the principal pair
exhausts the denominator, so R_M vanishes identically and (B) holds exactly.
That isolates the spacing law from the contour estimate: the O(M^-3) there is
pure Taylor remainder with no exponential term hiding in it.
"""

from mpmath import mp, mpf
import mpmath


def ddx(f, x):
    """Central difference at a step chosen from the working precision.

    mpmath.diff raises precision internally, which is expensive against an
    O(M) recurrence; the residual error here is ~10^(-2 dps/3), far below
    anything asserted.
    """
    h = mpf(10) ** (-(mp.dps // 3))
    return (f(x + h) - f(x - h)) / (2 * h)


# ---------------------------------------------------------------- geometry

def poly_val(coeffs, t):
    """coeffs[k] is the coefficient of t^k."""
    acc = 0 * t
    for c in reversed(coeffs):
        acc = acc * t + c
    return acc


def poly_diff(coeffs):
    return [k * c for k, c in enumerate(coeffs)][1:]


def tau_of_theta(Qc, r, theta, tau_guess):
    """tau > 0 with tau e^{+-i theta} the principal pair at angle theta.

    Im g(tau e^{i theta}) can have a second positive root that is NOT the
    minimum-modulus pair, so the bracket is grown outward from a guess inside
    the principal branch and stopped at the first sign change; that the result
    really is the minimum-modulus pair is asserted separately, per
    configuration, by `assert_principal_branch`.  Bisection, not a secant step:
    at r > 1 the secant iteration stagnates near half working precision here.
    """
    def imag_g(tau):
        t = tau * mpmath.expj(theta)
        return mpmath.im(-poly_val(Qc, t) / t**r)
    f0 = mpmath.sign(imag_g(tau_guess))
    lo = hi = tau_guess
    for _ in range(400):
        lo, hi = lo * mpf('0.98'), hi * mpf('1.02')
        if mpmath.sign(imag_g(lo)) != f0:
            hi = tau_guess
            break
        if mpmath.sign(imag_g(hi)) != f0:
            lo = tau_guess
            break
    else:
        raise RuntimeError(f"no bracket for tau at theta={theta}")
    return mpmath.findroot(imag_g, (lo, hi), solver='bisect',
                           tol=mpf(10) ** (-mp.dps + 12), maxsteps=8 * mp.dps)


def assert_principal_branch(cfg, samples=9):
    """`thm:FT-geometry`'s hypothesis, checked rather than assumed: the two
    roots tau e^{+-i theta} are the two smallest in modulus."""
    lo, hi = cfg.J
    for i in range(samples):
        th = lo + (hi - lo) * mpf(i) / (samples - 1)
        tau, z, _ = cfg.zW(th)
        D = list(cfg.Qc) + [0] * max(0, cfg.r + 1 - len(cfg.Qc))
        D[cfg.r] = D[cfg.r] + z
        while len(D) > 1 and D[-1] == 0:
            D.pop()
        roots = mpmath.polyroots(list(reversed(D)), maxsteps=300,
                                 extraprec=3 * mp.dps)
        mods = sorted(abs(u) for u in roots)
        assert len(mods) >= 2, f"denominator has one root at theta={th}"
        tol = mpf(10) ** (-mp.dps + 20)
        assert abs(mods[0] - tau) < tol and abs(mods[1] - tau) < tol, \
            (f"tau={tau} at theta={th} is not the minimum-modulus pair; "
             f"two smallest moduli are {mods[0]}, {mods[1]}")
    return len(mods)


def z_of_theta(Qc, r, theta, tau):
    t = tau * mpmath.expj(theta)
    return mpmath.re(-poly_val(Qc, t) / t**r)


def amplitude_W(Qc, r, theta, tau, z, Bc):
    """W = -B(t_+)/d_t D(t_+, z), `eq:residue-amplitude` at the principal root."""
    t = tau * mpmath.expj(theta)
    dD = poly_val(poly_diff(Qc), t) + r * z * t**(r - 1)
    return -poly_val(Bc, t) / dD


def g_prime(Qc, r, t):
    """g'(t) for g = -Q/t^r, as (rQ - tQ')/t^(r+1)."""
    n1 = [(r - k) * c for k, c in enumerate(Qc)]
    return poly_val(n1, t) / t**(r + 1)


def g_second(Qc, r, t):
    """g''(t) = [t n1'(t) - (r+1) n1(t)] / t^(r+2), n1 = rQ - tQ'."""
    n1 = [(r - k) * c for k, c in enumerate(Qc)]
    return (t * poly_val(poly_diff(n1), t) - (r + 1) * poly_val(n1, t)) / t**(r + 2)


# ------------------------------------------------------- rescaled recurrence

def G_M(Qc, r, Bc, z, tau, M):
    """tau^{M+1} F_M(z), computed from the rescaled recurrence so every
    intermediate stays O(1) rather than growing like tau^{-m}."""
    D = list(Qc) + [0] * max(0, r + 1 - len(Qc))
    D[r] = D[r] + z
    d0 = D[0]
    fhat = []
    for m in range(M + 1):
        acc = (tau**m * Bc[m]) if m < len(Bc) else mpf(0)
        for k in range(1, min(m, len(D) - 1) + 1):
            acc -= D[k] * tau**k * fhat[m - k]
        fhat.append(acc / d0)
    return tau * fhat[M]


# ---------------------------------------------------------------- the checks

class Config:
    def __init__(self, name, Qc, r, Bc, J, tau_guess, tau_exact=None):
        self.name, self.Qc, self.r, self.Bc = name, Qc, r, Bc
        self.J = J                       # (theta_lo, theta_hi), compact and zero-free
        self.tau_guess, self.tau_exact = tau_guess, tau_exact
        self._memo = {}

    def tau(self, theta):
        if self.tau_exact is not None:
            return self.tau_exact
        return tau_of_theta(self.Qc, self.r, theta, self.tau_guess)

    def zW(self, theta):
        key = (mp.dps, mpmath.nstr(theta, mp.dps))
        hit = self._memo.get(key)
        if hit is not None:
            return hit
        tau = self.tau(theta)
        z = z_of_theta(self.Qc, self.r, theta, tau)
        W = amplitude_W(self.Qc, self.r, theta, tau, z, self.Bc)
        self._memo[key] = (tau, z, W)
        return tau, z, W

    def G(self, theta, M):
        tau, z, _ = self.zW(theta)
        return G_M(self.Qc, self.r, self.Bc, z, tau, M)

    def R(self, theta, M):
        tau, z, W = self.zW(theta)
        g = G_M(self.Qc, self.r, self.Bc, z, tau, M)
        return g - 2 * mpmath.re(W * mpmath.expj(-(M + 1) * theta))

    def gamma(self, theta):
        """The principal root as a point of the denominator curve, gamma = t_+."""
        return self.tau(theta) * mpmath.expj(theta)

    def dgamma(self, theta):
        return ddx(self.gamma, theta)

    def psi_and_deriv(self, theta):
        """Continuous phase derivative psi' = Im(W'/W); the branch of psi itself
        is fixed separately by unwrapping along the subarc."""
        Wf = lambda th: self.zW(th)[2]
        W = Wf(theta)
        dW = ddx(Wf, theta)
        return mpmath.arg(W), mpmath.im(dW / W)


def unwrapped_psi(cfg, thetas):
    vals, off = [], mpf(0)
    prev = None
    for th in thetas:
        a = mpmath.arg(cfg.zW(th)[2])
        if prev is not None:
            while a + off - prev > mpmath.pi:
                off -= 2 * mpmath.pi
            while a + off - prev < -mpmath.pi:
                off += 2 * mpmath.pi
        prev = a + off
        vals.append(prev)
    return vals


def loglog_slope(xs, ys):
    n = len(xs)
    lx = [mpmath.log(x) for x in xs]
    ly = [mpmath.log(y) for y in ys]
    mx, my = sum(lx) / n, sum(ly) / n
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    den = sum((a - mx) ** 2 for a in lx)
    return num / den


def semilog_slope(xs, ys):
    n = len(xs)
    ly = [mpmath.log(y) for y in ys]
    mx, my = sum(xs) / n, sum(ly) / n
    num = sum((a - mx) * (b - my) for a, b in zip(xs, ly))
    den = sum((a - mx) ** 2 for a in xs)
    return num / den


def zeros_of_G(cfg, M, grid=None):
    """Every zero of G_M on the closed subarc J, by sign change then bisection."""
    lo, hi = cfg.J
    if grid is None:  # ~6 samples per half-period, so no sign change is skipped
        grid = int(6 * (M + 1) * (hi - lo) / mpmath.pi) + 40
    ths = [lo + (hi - lo) * mpf(i) / grid for i in range(grid + 1)]
    vals = [cfg.G(th, M) for th in ths]
    out = []
    for i in range(grid):
        if vals[i] == 0:
            out.append(ths[i])
        elif mpmath.sign(vals[i]) != mpmath.sign(vals[i + 1]):
            out.append(mpmath.findroot(lambda th: cfg.G(th, M), (ths[i], ths[i + 1]),
                                       solver='bisect', tol=mpf(10)**(-mp.dps + 25),
                                       maxsteps=4 * mp.dps))
    return out


def check_A_C1_remainder(cfg, Ms):
    print(f"  (A) ||R_M||_C1 = O(M sigma^M) on J = {cfg.J}")
    lo, hi = cfg.J
    probes = [lo + (hi - lo) * mpf(i) / 8 for i in range(9)]
    sup_R, sup_dR = [], []
    for M in Ms:
        sup_R.append(max(abs(cfg.R(th, M)) for th in probes))
        sup_dR.append(max(abs(ddx(lambda x: cfg.R(x, M), th)) for th in probes))
    if max(sup_R) < mpf(10) ** (-mp.dps + 25):
        print(f"      R_M vanishes identically (principal pair exhausts the "
              f"denominator); sup|R_M| <= {mpmath.nstr(max(sup_R), 3)}")
        return None
    s0 = semilog_slope(Ms, sup_R)
    s1 = semilog_slope(Ms, sup_dR)
    sigma = mpmath.exp(s0)
    print(f"      sup|R_M|  ~ sigma^M with sigma = {mpmath.nstr(sigma, 6)}")
    print(f"      sup|R_M'| ~ rho^M   with rho   = {mpmath.nstr(mpmath.exp(s1), 6)}")
    assert sigma < 1, "contour remainder does not decay"
    # the two rates must agree; the whole difference is the M prefactor
    assert abs(s1 - s0) < mpf('0.06') * abs(s0), \
        f"derivative decay rate {s1} differs from {s0} by more than a prefactor"
    ratios = [dR / (M * R) for M, R, dR in zip(Ms, sup_R, sup_dR)]
    lo_r, hi_r = min(ratios), max(ratios)
    print(f"      sup|R_M'| / (M sup|R_M|) in [{mpmath.nstr(lo_r,4)}, {mpmath.nstr(hi_r,4)}]"
          f" -- bounded, so the M factor is exactly right")
    assert hi_r / lo_r < 4, "the M prefactor is not the whole story"
    return sigma


def check_BCD(cfg, Ms, sigma):
    lo, hi = cfg.J
    grid = [lo + (hi - lo) * mpf(i) / 200 for i in range(201)]
    psi_grid = unwrapped_psi(cfg, grid)

    def psi_at(theta):
        # piecewise-linear index into the unwrapped branch, refined by the local arg
        i = min(int((theta - lo) / (hi - lo) * 200), 199)
        a = mpmath.arg(cfg.zW(theta)[2])
        k = mpmath.nint((psi_grid[i] - a) / (2 * mpmath.pi))
        return a + 2 * mpmath.pi * k

    print("  (B) phase quantization, (C) simplicity, (D) strong-clock spacing")
    quant_err, spacing_err, spacing_err_nocorr = [], [], []
    for M in Ms:
        zs = zeros_of_G(cfg, M)
        # (B) each zero sits at a half-integer phase point, and they are consecutive
        ks = []
        for th in zs:
            Phi = (M + 1) * th - psi_at(th)
            k = mpmath.nint(Phi / mpmath.pi - mpf(1) / 2)
            ks.append(k)
            quant_err.append((M, abs(Phi - (k + mpf(1) / 2) * mpmath.pi)))
        assert len(set(int(k) for k in ks)) == len(ks), f"M={M}: two zeros share a phase index"
        assert all(int(ks[i + 1]) - int(ks[i]) == 1 for i in range(len(ks) - 1)), \
            f"M={M}: phase indices {[int(k) for k in ks]} are not consecutive -- a zero is missing or spurious"
        # the count must track the phase advance across J
        adv = ((M + 1) * (hi - lo) - (psi_at(hi) - psi_at(lo))) / mpmath.pi
        assert abs(len(zs) - adv) <= 1, f"M={M}: {len(zs)} zeros against phase advance {adv}"

        # (C) simplicity of the corresponding zero of F_M in z
        for th in zs:
            d = ddx(lambda x: cfg.G(x, M), th)
            assert abs(d) > mpf(10) ** (-mp.dps + 20), f"M={M}: non-simple zero at theta={th}"

        # (D) spacing against the two-term law, and against the one-term law
        for i in range(len(zs) - 1):
            th, nxt = zs[i], zs[i + 1]
            _, dpsi = cfg.psi_and_deriv(th)
            pred = mpmath.pi / (M + 1) + mpmath.pi * dpsi / (M + 1) ** 2
            spacing_err.append((M, abs((nxt - th) - pred)))
            spacing_err_nocorr.append((M, abs((nxt - th) - mpmath.pi / (M + 1))))

    if sigma is not None:
        by_M = [max(e for m, e in quant_err if m == M) for M in Ms]
        rate = mpmath.exp(semilog_slope(Ms, by_M))
        print(f"      quantization defect ~ {mpmath.nstr(rate,6)}^M against sigma = "
              f"{mpmath.nstr(sigma,6)}")
        assert rate < 1, "quantization defect does not decay"
        # the defect is R_M/(2|W|) at the zero, so it must decay at sigma's own
        # rate, not merely at some rate
        assert rate < sigma ** mpf('0.75'), \
            f"quantization defect rate {rate} is far slower than sigma = {sigma}"
    else:
        worst = max(e for _, e in quant_err)
        print(f"      quantization is EXACT: worst defect {mpmath.nstr(worst, 3)}")
        # the floor here is the bisection tolerance times |Phi_M'| ~ M,
        # not a mathematical residual
        assert worst < mpf(10) ** (-mp.dps + 32)

    corr = [max(e for m, e in spacing_err if m == M) for M in Ms]
    nocorr = [max(e for m, e in spacing_err_nocorr if m == M) for M in Ms]
    s_corr = loglog_slope([mpf(M) for M in Ms], corr)
    s_nocorr = loglog_slope([mpf(M) for M in Ms], nocorr)
    print(f"      with    psi' correction: residual ~ M^-{mpmath.nstr(-s_corr, 4)}"
          f"   (claim: M^-3)")
    print(f"      without psi' correction: residual ~ M^-{mpmath.nstr(-s_nocorr, 4)}"
          f"   (mutation: must degrade to M^-2)")
    assert -s_corr > mpf('2.7'), f"two-term spacing law is not O(M^-3): slope {s_corr}"
    assert -s_nocorr < mpf('2.3'), \
        f"dropping the psi' term did NOT degrade the rate -- the correction is untested"
    assert -s_corr - (-s_nocorr) > mpf('0.7'), "the correction buys less than one order"


def run(cfg, Ms, dps):
    mp.dps = dps
    print(f"\n{cfg.name}")
    lo, hi = cfg.J
    Wmin = min(abs(cfg.zW(lo + (hi - lo) * mpf(i) / 40)[2]) for i in range(41))
    print(f"  subarc J = [{mpmath.nstr(lo,5)}, {mpmath.nstr(hi,5)}], "
          f"min|W| = {mpmath.nstr(Wmin, 5)} > 0 (hypothesis holds)")
    assert Wmin > mpf('1e-6'), "J is not zero-free: the proposition does not apply"
    nroots = assert_principal_branch(cfg)
    print(f"  principal branch verified at 9 sample angles; D has {nroots} roots"
          f"{' (principal pair only -- R_M vanishes)' if nroots == 2 else ''}")
    sigma = check_A_C1_remainder(cfg, Ms)
    check_BCD(cfg, Ms, sigma)


def check_hypothesis_is_load_bearing():
    """Across an amplitude zero the law must fail: J zero-free is not decorative.

    Q = (1-t)(1-t/2)(1-t/4), r = 1, B = 7t^2+8 has an amplitude zero at
    theta = pi/2 (`fig:decomposition-and-defect`, panel A).  Straddle it.
    """
    mp.dps = 60
    print("\nHypothesis check: the same law across an amplitude zero (must FAIL)")
    cfg = Config("straddling", [mpf(1), mpf(-7)/4, mpf(7)/8, mpf(-1)/8], 1,
                 [mpf(8), mpf(0), mpf(7)], (mpf(1), mpf(2)), mpf('1.05'))
    lo, hi = cfg.J
    # The zero is exactly at theta = pi/2: there t_+ = i sqrt(8/7) and
    # B(t_+) = 7(-8/7) + 8 = 0.  A sampling grid lands near it but not on it,
    # so assert the value AT the zero rather than a grid minimum.
    th_star = mpmath.pi / 2
    assert lo < th_star < hi
    W_star = abs(cfg.zW(th_star)[2])
    print(f"  |W| at theta = pi/2 is {mpmath.nstr(W_star, 4)} -- the amplitude "
          f"zero of `fig:decomposition-and-defect`(A), inside [1,2]")
    assert W_star < mpf(10) ** (-mp.dps + 20), \
        "this interval was supposed to straddle a zero of W"
    errs = []
    for M in (30, 40, 50):
        zs = zeros_of_G(cfg, M)
        grid = [lo + (hi - lo) * mpf(i) / 200 for i in range(201)]
        psi_grid = unwrapped_psi(cfg, grid)
        worst = mpf(0)
        for th in zs:
            i = min(int((th - lo) / (hi - lo) * 200), 199)
            a = mpmath.arg(cfg.zW(th)[2])
            k = mpmath.nint((psi_grid[i] - a) / (2 * mpmath.pi))
            Phi = (M + 1) * th - (a + 2 * mpmath.pi * k)
            kk = mpmath.nint(Phi / mpmath.pi - mpf(1) / 2)
            worst = max(worst, abs(Phi - (kk + mpf(1) / 2) * mpmath.pi))
        errs.append(worst)
        print(f"  M={M}: worst quantization defect {mpmath.nstr(worst, 4)}")
    assert max(errs) > mpf('1e-3'), \
        "quantization held across the amplitude zero -- the zero-free hypothesis is untested here"
    print("  PASS: the law degrades across the amplitude zero, so `W != 0` on J is load-bearing")


def check_residue_amplitude(cfgs, label):
    r"""`eq:residue-amplitude` W(t,z) = -B(t)/d_t D(t,z), at every denominator root.

    The paper's formula differentiates D(t,z) = Q(t) + z t^r coefficient by
    coefficient.  Two independent routes to the same residue are checked against
    it, at every simple root of D and not only at the principal one:

      (i)  the factored denominator.  D(.,z) = c_d prod_j (t - t_j), so at a
           simple root d_t D(t_i,z) = c_d prod_{j != i} (t_i - t_j) -- the
           derivative read off the factorization rather than off the
           coefficients, which is what makes it a second route and not the same
           computation twice.
      (ii) a small positively oriented circle about the root, on which
           -(1/2 pi i) contour-integral B/D dt is the residue by definition.  The
           integrand is analytic on and inside the circle apart from the one
           pole, so the equally spaced trapezoid rule converges geometrically;
           its own error is asserted by halving the node count.  The circle is
           taken at a tenth of the distance to the nearest other root, so the
           integrand is analytic in a wide enough strip for that rule to reach
           the working precision.

    Route (ii) is what pins the SIGN and the normalization: `eq:residue-amplitude`
    carries a minus sign, and a residue identity that agreed up to sign would
    leave `eq:principal-decomposition` and every clock statement downstream
    unverified.  `eq:W-def` -- that W(theta) is this amplitude at the principal
    root -- is asserted last, tying the display to the routine the rest of this
    script computes with.
    """
    print(f"  (F) eq:residue-amplitude at every denominator root, {label}")
    tol = mpf(10) ** (-mp.dps + 25)
    for cfg in cfgs:
        lo, hi = cfg.J
        worst_fac = worst_int = mpf(0)
        nroots = 0
        for i in range(1, 6):
            th = lo + (hi - lo) * mpf(i) / 6
            tau, z, W = cfg.zW(th)
            D = list(cfg.Qc) + [mpf(0)] * max(0, cfg.r + 1 - len(cfg.Qc))
            D[cfg.r] = D[cfg.r] + z
            while len(D) > 1 and D[-1] == 0:
                D.pop()
            rts = mpmath.polyroots(list(reversed(D)), maxsteps=300,
                                   extraprec=3 * mp.dps)
            sep = min(abs(u - v) for k, u in enumerate(rts) for v in rts[k + 1:])
            assert sep > mpf(10) ** (-mp.dps + 30), \
                f"D(.,z) has a repeated root at theta={th}: the residue formula does not apply"
            for idx, u in enumerate(rts):
                assert abs(poly_val(D, u)) <= tol * max(1, abs(u)) ** len(D), \
                    f"polyroots returned a non-root at theta={th}"
                # the paper's formula
                W_paper = -poly_val(cfg.Bc, u) / (poly_val(poly_diff(cfg.Qc), u)
                                                  + cfg.r * z * u**(cfg.r - 1))
                assert abs(W_paper) > mpf(10) ** -20, \
                    (f"the amplitude vanishes at theta={th}: the routes would "
                     f"agree at zero and nothing would be tested")
                # (i) the factored denominator
                dD = D[-1] * mpmath.fprod([u - v for j, v in enumerate(rts)
                                           if j != idx])
                W_fac = -poly_val(cfg.Bc, u) / dD
                e_fac = abs(W_fac - W_paper) / abs(W_paper)
                assert e_fac < mpf(10) ** (-mp.dps + 35), (th, u, mpmath.nstr(e_fac, 6))
                # (ii) the residue as a contour integral
                rad = sep / 10
                def circle(n, u=u, rad=rad, D=D):
                    acc = mpf(0)
                    for k in range(n):
                        w = u + rad * mpmath.expj(2 * mpmath.pi * mpf(k) / n)
                        acc += poly_val(cfg.Bc, w) / poly_val(D, w) * (w - u)
                    return -acc / n
                W_int = circle(128)
                assert abs(W_int - circle(64)) < mpf(10) ** (-mp.dps + 40), \
                    "the trapezoid rule has not converged on this circle"
                e_int = abs(W_int - W_paper) / abs(W_paper)
                assert e_int < mpf(10) ** (-mp.dps + 40), (th, u, mpmath.nstr(e_int, 6))
                worst_fac, worst_int = max(worst_fac, e_fac), max(worst_int, e_int)
                nroots += 1
            # `eq:W-def`: W(theta) is that amplitude at the principal root
            tp = tau * mpmath.expj(th)
            assert min(abs(u - tp) for u in rts) <= tol * max(1, tau), \
                f"the principal root is not a root of D at theta={th}"
            W_pr = -poly_val(cfg.Bc, tp) / (poly_val(poly_diff(cfg.Qc), tp)
                                            + cfg.r * z * tp**(cfg.r - 1))
            assert abs(W_pr - W) <= tol * max(1, abs(W)), (th, W_pr, W)
        print(f"      {cfg.name.split(':')[0]}: {nroots} residues over 5 angles; "
              f"worst relative disagreement {mpmath.nstr(worst_fac, 4)} against the "
              f"factored denominator and {mpmath.nstr(worst_int, 4)} against the "
              f"contour integral, sign included")
    print("      eq:W-def holds at every angle: W(theta) is that amplitude at t_+")


def check_E_numerator_correction(cfgs, label):
    r"""(E) `eq:W-on-g` and the split `eq:numerator-clock-correction`.

    On the denominator curve W = B(gamma)/(gamma^r g'(gamma)), so

        psi' = Im(W'/W)
             = Im(B'(gamma) gamma'/B(gamma))          <- eq:numerator-clock-correction
               - Im(r gamma'/gamma + g''(gamma) gamma'/g'(gamma)).

    The second bracket involves no B at all.  `cfgs` must share one (Q, r) and
    differ only in the weight.
    """
    Qc, r = cfgs[0].Qc, cfgs[0].r
    assert all(c.Qc == Qc and c.r == r for c in cfgs), 'configs differ in the denominator'
    lo, hi = cfgs[0].J
    thetas = [lo + (hi - lo) * mpf(i) / 6 for i in range(1, 6)]
    tol = mpf(10) ** (-mp.dps + 50)

    print(f"  (E) eq:W-on-g and the psi' split, {label}")
    den_rows = []
    for cfg in cfgs:
        dens, corrs = [], []
        for th in thetas:
            tau, zv, W = cfg.zW(th)
            g = cfg.gamma(th)
            dg = cfg.dgamma(th)

            # eq:W-on-g: the residue amplitude rewritten on the curve.
            W_on_g = poly_val(cfg.Bc, g) / (g**r * g_prime(Qc, r, g))
            assert abs(W_on_g - W) <= tol * max(1, abs(W)), \
                (f'eq:W-on-g fails at theta={th}: {W_on_g} vs {W}')

            _, dpsi = cfg.psi_and_deriv(th)
            corr = mpmath.im(poly_val(poly_diff(cfg.Bc), g) * dg / poly_val(cfg.Bc, g)) \
                if len(cfg.Bc) > 1 else mpf(0)
            den = -mpmath.im(r * dg / g + g_second(Qc, r, g) * dg / g_prime(Qc, r, g))

            # the split itself
            assert abs(dpsi - (corr + den)) <= mpf(10) ** (-mp.dps + 55) * max(1, abs(dpsi)), \
                (f"psi' split fails at theta={th}: {dpsi} vs {corr}+{den}")
            dens.append(den)
            corrs.append(corr)
        den_rows.append(dens)
        Bname = ' + '.join(f'{mpmath.nstr(c, 4)} t^{k}' for k, c in enumerate(cfg.Bc) if c != 0)
        print(f"      B = {Bname}: psi' = correction + denominator term at "
              f"{len(thetas)} angles; |correction| in "
              f"[{mpmath.nstr(min(abs(x) for x in corrs), 4)}, "
              f"{mpmath.nstr(max(abs(x) for x in corrs), 4)}]")

    # the denominator-only term is the SAME for every weight
    for j in range(1, len(den_rows)):
        for a, b in zip(den_rows[0], den_rows[j]):
            assert abs(a - b) <= mpf(10) ** (-mp.dps + 55) * max(1, abs(a)), \
                ('the denominator-only term moved with B', a, b)
    print(f"      the denominator-only term agrees across all {len(cfgs)} weights to "
          f"{mp.dps - 55} digits")

    # a constant weight kills the correction, so psi' IS the denominator term
    const = [c for c in cfgs if len(c.Bc) == 1]
    assert const, 'no constant weight among the configs; the sharp case is untested'
    for th in thetas:
        _, dpsi = const[0].psi_and_deriv(th)
        g, dg = const[0].gamma(th), const[0].dgamma(th)
        den = -mpmath.im(r * dg / g + g_second(Qc, r, g) * dg / g_prime(Qc, r, g))
        assert abs(dpsi - den) <= mpf(10) ** (-mp.dps + 55) * max(1, abs(dpsi))

    # and a nonconstant weight genuinely moves psi' -- otherwise the split is vacuous
    moved = max(abs(a - b) for a, b in
                zip([const[0].psi_and_deriv(th)[1] for th in thetas],
                    [cfgs[-1].psi_and_deriv(th)[1] for th in thetas]))
    assert moved > mpf('1e-3'), f'the weight does not move psi at all ({moved})'
    print(f"      at B = const the correction vanishes and psi' equals it exactly; a "
          f"nonconstant weight moves psi' by up to {mpmath.nstr(moved, 5)}, so the "
          f"correction is not decorative")


def main():
    # Q1: deg Q = 2, r = 1.  The principal pair exhausts the denominator, so
    # R_M == 0 and the quantization is exact; this isolates the Taylor content
    # of the spacing law.  tau = sqrt(q0/q2) is constant (`rem:quadratic-case`).
    mp.dps = 80
    Q1 = Config("Q1: Q = (1-t)(1-2t), r = 1, B = 1+t   [R_M vanishes; spacing law isolated]",
                [mpf(1), mpf(-3), mpf(2)], 1, [mpf(1), mpf(1)],
                (mpf(9) / 10, mpf(21) / 10), mpf('0.7'),
                tau_exact=mpmath.sqrt(mpf(1) / 2))

    # Q2: deg Q = 3, r = 1.  Nonprincipal roots present, so R_M is a genuine
    # exponentially small contour remainder and (A) has content.
    Q2 = Config("Q2: Q = (1-t)(1-t/2)(1-t/4), r = 1, B = 1+t   [genuine R_M]",
                [mpf(1), mpf(-7) / 4, mpf(7) / 8, mpf(-1) / 8], 1, [mpf(1), mpf(1)],
                (mpf(1), mpf(2)), mpf('1.05'))

    # Q3: r = 2 > 1, unbounded upper endpoint -- a structurally different regime.
    # deg Q > r, so a nonprincipal root survives and R_M is genuine; deg Q = r
    # would leave the principal pair alone and reduce to the Q1 situation.
    Q3 = Config("Q3: Q = (1-t)(1-t/2)(1-t/4), r = 2, B = 2+t   [r > 1]",
                [mpf(1), mpf(-7) / 4, mpf(7) / 8, mpf(-1) / 8], 2, [mpf(2), mpf(1)],
                (mpf(4) / 10, mpf(11) / 10), mpf('0.9'))

    # The M ladders are chosen so that sigma^M stays above the root-finding
    # floor (bisection tol ~ 10^-(dps-25), phase defect floor ~ M x that).
    # A ladder running past it flattens the measured exponential rate.
    run(Q1, [40, 60, 80, 100, 120], 55)
    run(Q2, [24, 30, 36, 42, 48], 70)
    run(Q3, [24, 30, 36, 42, 48], 70)
    # (E) needs several weights on ONE denominator, so that the denominator-only
    # half of the split can be compared across them.
    mp.dps = 80
    # (F) is the display the amplitude itself is defined by, so it is checked
    # across all three configurations before anything built on it.
    check_residue_amplitude([Q1, Q2, Q3], 'r = 1 and r = 2, deg Q = 2 and 3')
    QcE, rE, JE, tgE = Q2.Qc, Q2.r, Q2.J, Q2.tau_guess
    check_E_numerator_correction(
        [Config("B = 1", QcE, rE, [mpf(1)], JE, tgE),
         Config("B = 1+t", QcE, rE, [mpf(1), mpf(1)], JE, tgE),
         Config("B = 2+t", QcE, rE, [mpf(2), mpf(1)], JE, tgE)],
        'Q = (1-t)(1-t/2)(1-t/4), r = 1')
    check_hypothesis_is_load_bearing()
    print("\nALL PASS: check_local_clock")


if __name__ == '__main__':
    main()
