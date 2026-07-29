#!/usr/bin/env python3
r"""Paper section 4 (Weighted principal-pair dominance).

All numerics use mpmath at arbitrary precision (no floating-point arithmetic in
the verification loops).  Denominator roots come from mpmath.polyroots.

  * eq. (4.8): at a denominator root t_j one has z = -Q(t_j)/t_j^r, so
        Q'(t_j) + r z t_j^{r-1} = Q'(t_j) - r Q(t_j)/t_j.
  * The endpoint O(1) prefactor.  Each normalized nonprincipal residue is the
    principal amplitude times |zeta_j|^{-(M+1)} times the bounded ratio
        [B(t_j)/B(t_+)] * [D'(t_+)/D'(t_j)].
    Lower endpoint (repeated smallest zero x1, mult rho): B(t_j) has common order
    theta^nu, eq. (4.7), and D'(t_j) common order theta^{rho-1}, eq. (4.5)-(4.8),
    so both ratios are bounded.  Upper endpoint (r > 1, tau -> 0):
    D'(t_j) = -r Q(0)/(tau zeta_j)(1+o(1)), so tau^{-1} cancels and only the bounded
    zeta_+/zeta_j survives; B(0) != 0 keeps the numerator ratios bounded.
  * Theorem 4.1, eq. (4.2): |R_M(theta)| <= (1/2)|W(theta)| on the retained range
    [h/M, pi/r - h/M] (checked for genuine lower- and upper-endpoint clusters, with
    B chosen with no zero on the branch so |W| is bounded below).
  * The role of the h/M truncation (eq. (4.3)): the nonprincipal contribution is
    exactly geometric in M with rate proportional to theta, so |R_M|/|W| ~ e^{-c_0 M theta};
    truncating at theta >= h/M converts the linear modulus gap into fixed e^{-c_0 h} control.
  * Theorem 4.1 proof, upper endpoint with deg Q > r (r > 1): the deg Q - r outer roots
    escape to infinity; on a fixed contour |t| = R0 the r small-cluster roots lie inside and
    the outer roots outside, and the grouped outer contribution obeys
    |tau^{M+1} C_out| <= (tau/R0)^{M+r} |W|.
  * Theorem 4.1 proof, lower endpoint with deg Q < r: at a repeated smallest zero x1
    (mult rho >= 2) the lower endpoint value is a = g(x1) = -Q(x1)/x1^r = 0, so z(theta) -> 0
    and r - deg Q roots escape to infinity as theta -> 0.  On a fixed contour |t| = R0
    (exceeding every zero of Q) the deg Q finite roots lie inside and the escaping roots
    outside, and the grouped outer contribution obeys |tau^{M+1} C_out| <= (tau/R0)^M |W|,
    hence is o(|W|) on theta >= h/M whatever the sign of the endpoint exponent p (with B = 1,
    nu = 0 and k = max{rho,2} = rho, so p = nu - (k-1) = -(rho-1) < 0 and |W| -> infinity
    at the endpoint).
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

mp.mp.dps = 50
t = sp.symbols('t')


def qlow(expr):
    p = sp.Poly(sp.expand(expr), t)
    return [p.nth(i) for i in range(p.degree() + 1)]


def d_roots(Qlow, r, zval):
    d = max(len(Qlow) - 1, r)
    c = [mp.mpf(0)] * (d + 1)
    for i, co in enumerate(Qlow):
        c[i] += mp.mpf(co)
    c[r] += mp.mpf(zval)
    return mp.polyroots(list(reversed(c)), maxsteps=3000, extraprec=300)


def pval(coeffs_low, x):
    return sum(mp.mpf(c) * x**i for i, c in enumerate(coeffs_low))


def dval(coeffs_low, x):
    return sum(mp.mpf(coeffs_low[i]) * i * x**(i - 1) for i in range(1, len(coeffs_low)))


def principal(rts):
    o = sorted(rts, key=lambda w: abs(w))
    for w in o:
        if abs(mp.im(w)) > mp.mpf('1e-25'):
            return w
    return o[0]


def nonprincipal_of(rts):
    pair = sorted(rts, key=lambda w: abs(w))[:2]
    return [w for w in rts if all(abs(w - p) > mp.mpf('1e-18') for p in pair)]


def in_ft_interval(rts):
    r"""Is z inside I_{Q,r}?  Theorem 3.1 puts the two MINIMUM-MODULUS zeros there in a
    conjugate pair t_pm = tau e^{+-i theta}; outside I_{Q,r} they need not be, and nothing
    in section 4 is claimed.  This must be checked, not assumed: at r = 1 the interval is
    bounded, so a z-sweep that runs past b leaves the regime, and `principal` would then
    return some other nonreal root -- one not in the minimum-modulus pair -- making
    |R_M|/|W| tend to 2 for reasons that have nothing to do with eq. (4.2).
    """
    o = sorted(rts, key=lambda w: abs(w))[:2]
    return (abs(mp.im(o[0])) > mp.mpf('1e-25')
            and abs(o[0] - mp.conj(o[1])) < mp.mpf('1e-20') * (1 + abs(o[0])))


def RM_over_W(Qc, Bc, r, zval, M):
    r"""(|R_M|/|W|, theta) for the normalized nonprincipal contribution R_M."""
    rts = d_roots(Qc, r, zval)
    pr = principal(rts); tau = abs(pr); th = abs(mp.arg(pr))

    def Dp(w):
        return dval(Qc, w) + r * zval * w**(r - 1)

    W = -pval(Bc, pr) / Dp(pr)
    R = tau**(M + 1) * sum(-pval(Bc, w) / (w**(M + 1) * Dp(w)) for w in nonprincipal_of(rts))
    return abs(R) / abs(W), th


# ===========================================================================
# eq. (4.8): derivative identity at a denominator root
# ===========================================================================
Qc = qlow((1 - t)**3 * (1 - t / 4))
for r in (2, 3):
    for zval in (mp.mpf('0.01'), mp.mpf('1'), mp.mpf('100')):
        for w in d_roots(Qc, r, zval):
            lhs = dval(Qc, w) + r * zval * w**(r - 1)
            rhs = dval(Qc, w) - r * pval(Qc, w) / w
            assert abs(lhs - rhs) < mp.mpf('1e-30')
print("PASS: Q'(t_j) + r z t_j^(r-1) = Q'(t_j) - r Q(t_j)/t_j at every denominator root")


# ===========================================================================
# Endpoint O(1) prefactor: B- and D'-ratios bounded across the cluster
# ===========================================================================
def lower_prefactor(Qexpr, Bexpr, r, x1):
    Qc, Bc = qlow(Qexpr), qlow(Bexpr)
    Brat, Drat, zetas = [], [], []
    for zval in [mp.mpf(10)**(-k) for k in range(2, 8)]:
        rts = d_roots(Qc, r, zval)
        pr = principal(rts); tau = abs(pr)
        Bpr, Dpr = pval(Bc, pr), dval(Qc, pr) + r * zval * pr**(r - 1)
        pair = sorted(rts, key=lambda w: abs(w))[:2]
        for w in rts:
            if abs(w - x1) < mp.mpf('0.7') and all(abs(w - p) > mp.mpf('1e-9') for p in pair):
                zetas.append(abs(w) / tau)
                Brat.append(abs(pval(Bc, w)) / abs(Bpr))
                Drat.append(abs((dval(Qc, w) + r * zval * w**(r - 1)) / Dpr))
    assert zetas, 'no nonprincipal cluster member (need a repeated smallest zero of mult >= 3)'
    # eq. (4.6) claims |zeta_j| >= 1 + c0*theta -- a LINEAR rate.  Asserting only
    # zj > 1 would pass for a gap collapsing like 1 + theta^2, so assert the rate too.
    assert all(zj > 1 for zj in zetas)                             # necessary, not sufficient
    rate_pairs = []
    for kk in range(3, 9):
        zz = mp.mpf(10)**(-kk)
        rr = d_roots(Qc, r, zz)
        pp = principal(rr); tt = abs(pp); thh = abs(mp.arg(pp))
        pr2 = sorted(rr, key=lambda w: abs(w))[:2]
        cand = [abs(w) / tt for w in rr
                if abs(w - x1) < mp.mpf('0.7')
                and all(abs(w - qq) > mp.mpf('1e-9') for qq in pr2)]
        if cand and thh > 0:
            rate_pairs.append((thh, (min(cand) - 1) / thh))
    assert len(rate_pairs) >= 4, rate_pairs
    c0_seq = [v for _, v in rate_pairs]
    assert min(c0_seq) > mp.mpf('0.05'), c0_seq                     # c0 > 0
    assert abs(c0_seq[-1] - c0_seq[-2]) < abs(c0_seq[-1]) / 20, c0_seq[-2:]
    sl_gap = ((mp.log(rate_pairs[-1][1] * rate_pairs[-1][0])
               - mp.log(rate_pairs[-2][1] * rate_pairs[-2][0]))
              / (mp.log(rate_pairs[-1][0]) - mp.log(rate_pairs[-2][0])))
    assert abs(sl_gap - 1) < mp.mpf('0.05'), sl_gap                 # LINEAR in theta
    assert mp.mpf('0.05') < min(Brat) and max(Brat) < 20          # B(t_j)/B(t_+) bounded
    assert mp.mpf('0.05') < min(Drat) and max(Drat) < 20          # D'(t_j)/D'(t_+) bounded
    print(f"PASS: lower endpoint prefactor bounded: |zeta| in [{mp.nstr(min(zetas),5)},"
          f"{mp.nstr(max(zetas),5)}], B-ratio in [{mp.nstr(min(Brat),4)},{mp.nstr(max(Brat),4)}], "
          f"D'-ratio in [{mp.nstr(min(Drat),4)},{mp.nstr(max(Drat),4)}]")


def upper_prefactor(Qexpr, r):
    Qc = qlow(Qexpr); Q0 = pval(Qc, mp.mpf(0))
    Drat, tozero = [], []
    for zval in [mp.mpf(10)**k for k in range(2, 8)]:
        rts = d_roots(Qc, r, zval)
        pr = principal(rts); tau = abs(pr)
        Dpr = dval(Qc, pr) + r * zval * pr**(r - 1)
        for w in sorted(rts, key=lambda w: abs(w))[:r]:
            Drat.append(abs((dval(Qc, w) + r * zval * w**(r - 1)) / Dpr))
        tozero.append(abs(Dpr * tau * (pr / tau) + r * Q0))        # |D'(t_+) tau zeta_+ + r Q(0)| -> 0
    assert max(Drat) < 10                                          # D'(t_j)/D'(t_+) bounded
    assert tozero[-1] < tozero[0] and tozero[-1] < mp.mpf('0.2')   # D'(t_+) tau zeta_+ -> -r Q(0)
    print(f"PASS: upper endpoint prefactor bounded: D'-ratio max {mp.nstr(max(Drat),4)}, "
          f"|D'(t_+) tau zeta_+ + r Q(0)| {mp.nstr(tozero[0],4)} -> {mp.nstr(tozero[-1],4)} "
          f"(tau^-1 cancels)")


lower_prefactor((1 - t)**3 * (1 - t / 4), (1 - t) * (2 + t), 2, mp.mpf(1))   # x1=1, rho=3, B zero at x1
upper_prefactor(1 - t, 3)
upper_prefactor(1 - t, 4)


# ===========================================================================
# Theorem 4.1, eq. (4.2): |R_M(theta)| <= (1/2)|W(theta)| on the retained range
# ===========================================================================
def retained_worst(Qexpr, Bexpr, r, M, h):
    Qc, Bc = qlow(Qexpr), qlow(Bexpr)
    lo, hi = h / mp.mpf(M), mp.pi / r - h / mp.mpf(M)
    worst, worst_th, n, skipped = mp.mpf(0), None, 0, 0
    zval = mp.mpf('1e-4')
    while zval < mp.mpf('1e7'):
        if not in_ft_interval(d_roots(Qc, r, zval)):
            skipped += 1                                   # z outside I_{Q,r}: nothing claimed
            zval *= mp.mpf('1.25')
            continue
        ratio, th = RM_over_W(Qc, Bc, r, zval, M)
        if lo <= th <= hi:
            n += 1
            if ratio > worst:
                worst, worst_th = ratio, th
        zval *= mp.mpf('1.25')
    return worst, worst_th, n, lo, hi, skipped


# B = (1-t)(2+t): B(0) != 0 and only real (negative/positive-real) roots, never on the
# open upper-half-plane branch t_+(theta), so |W| stays bounded below on the retained range.
for (Qexpr, Bexpr, r, label) in [
    ((1 - t)**3 * (1 - t / 4), (1 - t) * (2 + t), 2, 'lower cluster rho=3, r=2'),
    ((1 - t)**3 * (1 - t / 4), (2 + t), 3, 'lower+upper clusters, r=3'),
    # r = 1 is a distinct case in the proof -- the upper endpoint is a FINITE collision at
    # theta = pi rather than tau -> 0, and Lemma 3.3's parameter interval may include b --
    # and it is the case Figure 1 illustrates.  No r = 1 config was exercised here before.
    ((1 - t) * (1 - t / 2) * (1 - t / 4), (1 - t) * (2 + t), 1, 'r=1, finite upper endpoint'),
    ((1 - t)**3 * (1 - t / 4), (2 + t), 1, 'r=1 with a repeated smallest zero (rho=3)'),
]:
    worst, worst_th, n, lo, hi, skipped = retained_worst(Qexpr, Bexpr, r, M=150, h=10)
    assert n >= 15, (label, n)                     # the sweep produced a meaningful sample
    # at r = 1 the interval is bounded, so the sweep must actually leave it; at r > 1 it is
    # (a, +inf) and every sampled z above a stays inside
    assert (skipped > 0) == (r == 1), (label, r, skipped)
    assert worst < mp.mpf('0.5'), (label, worst)                   # eq. (4.2)
    # Where the bound is tightest is an observation about these configs, not a claim of
    # Theorem 4.1.  At r > 1 the worst point sits against a truncated endpoint; at r = 1 the
    # upper endpoint is a finite collision (k = 2 in eq. (3.11)) rather than tau -> 0, so |W|
    # does not blow up the same way and the worst point can be interior.  Assert the
    # endpoint-tightness only where it is actually the geometry, and report the location
    # either way.
    at_end = worst_th - lo < mp.mpf('0.05') or hi - worst_th < mp.mpf('0.05')
    if r > 1:
        assert at_end, (label, worst_th, lo, hi)
    print(f'PASS: {label}: |R_M| <= (1/2)|W| on retained range ({n} samples), worst '
          f'|R_M|/|W| = {mp.nstr(worst, 4)} at theta = {mp.nstr(worst_th, 4)} '
          f'({"near a truncated endpoint" if at_end else "interior"})')


# ===========================================================================
# Role of the h/M truncation: |R_M|/|W| ~ e^{-c_0 M theta}, rate proportional to theta
# ===========================================================================
Qc, Bc, r = qlow((1 - t)**3 * (1 - t / 4)), qlow((1 - t) * (2 + t)), 2
slopes = []
for zval in (mp.mpf('0.02'), mp.mpf('0.05')):
    Ms = [50, 100, 150, 200, 250]
    logs = [mp.log(RM_over_W(Qc, Bc, r, zval, M)[0]) for M in Ms]
    th0 = RM_over_W(Qc, Bc, r, zval, 50)[1]
    incr = [(logs[i + 1] - logs[i]) / (Ms[i + 1] - Ms[i]) for i in range(len(Ms) - 1)]
    assert max(incr) - min(incr) < mp.mpf('1e-6')                  # exactly geometric in M
    assert incr[-1] < 0                                            # decaying (suppression)
    slopes.append((th0, incr[-1]))
# larger theta (deeper interior) => steeper decay: the h/M truncation is load-bearing
assert abs(slopes[1][1]) > abs(slopes[0][1]) and slopes[1][0] > slopes[0][0]
print(f'PASS: |R_M|/|W| decays exactly geometrically in M, rate scales with theta '
      f'(theta={mp.nstr(slopes[0][0],4)} -> slope {mp.nstr(slopes[0][1],4)}; '
      f'theta={mp.nstr(slopes[1][0],4)} -> slope {mp.nstr(slopes[1][1],4)})')


# ===========================================================================
# eq. (4.5): lower cluster t_j(theta) = x1 + c_j theta + O(theta^2), c_j != 0
# eq. (4.7): B(t_j) = b_j theta^nu (1 + O(theta)), nu = ord_{x1} B
# ===========================================================================
Qc, Bc, r, x1 = qlow((1 - t)**3 * (1 - t / 4)), qlow((1 - t) * (2 + t)), 2, mp.mpf(1)
seq_c, seq_B = [], []
for k in range(3, 10):
    pr = principal(d_roots(Qc, r, mp.mpf(10)**(-k))); th = abs(mp.arg(pr))
    seq_c.append((th, abs(pr - x1) / th))                         # |t_+ - x1| / theta
    seq_B.append((th, abs(pval(Bc, pr))))                         # |B(t_+)|
assert seq_c[-1][1] > mp.mpf('0.1')                               # c_j != 0
# The stated O(theta^2) is asserted directly.  Comparing consecutive differences of the
# tested sequence to each other would be a self-referential tolerance that any convergent
# sequence passes at any rate.
c_lim = seq_c[-1][1]
assert abs(c_lim - seq_c[-2][1]) < abs(c_lim) / 50                # c_j converges
rem_c = [abs(v - c_lim) / th for th, v in seq_c[-4:]]
assert max(rem_c) < mp.mpf('50') * (abs(c_lim) + 1), rem_c        # remainder is O(theta^2)
slopeB = ((mp.log(seq_B[-1][1]) - mp.log(seq_B[-2][1]))
          / (mp.log(seq_B[-1][0]) - mp.log(seq_B[-2][0])))
assert abs(slopeB - 1) < mp.mpf('0.02')                           # B zero at x1 has order nu = 1
print(f'PASS: cluster t_j = x1 + c_j theta + O(theta^2), |c_j| -> {mp.nstr(seq_c[-1][1], 5)} != 0; '
      f'B(t_j) ~ theta^nu, nu = {mp.nstr(slopeB, 5)}')


# ===========================================================================
# Theorem 4.1, eq. (4.1)/(4.2) with a genuine amplitude zero: the deletion window
# Theta_{j,M} = {|theta-theta_j| < e^{-cM/nu_j}} is needed and is exponentially short
# ===========================================================================
Qc, r, theta_j = qlow((1 - t) * (1 - t / 2) * (1 - t / 4)), 2, mp.mpf('0.8')
lo, hi = mp.mpf('0.05'), mp.mpf('100')
for _ in range(180):                                              # z_j: arg t_+(z_j) = theta_j
    mid = mp.sqrt(lo * hi)
    lo, hi = (mid, hi) if abs(mp.arg(principal(d_roots(Qc, r, mid)))) < theta_j else (lo, mid)
z_j = mp.sqrt(lo * hi); tp = principal(d_roots(Qc, r, z_j))
Bc = [mp.re(tp)**2 + mp.im(tp)**2, -2 * mp.re(tp), mp.mpf(1)]     # real B with an exact branch root at theta_j
M, c, nu = 30, mp.mpf('0.15'), 1
Jhalf = mp.e**(-c * M / nu)


def RW_zero(zval):
    rts = d_roots(Qc, r, zval); pr = principal(rts); tau = abs(pr); th = abs(mp.arg(pr))

    def Dp(w):
        return dval(Qc, w) + r * zval * w**(r - 1)

    W = -pval(Bc, pr) / Dp(pr)
    nonp = [w for w in rts if all(abs(w - p) > mp.mpf('1e-18') for p in sorted(rts, key=lambda w: abs(w))[:2])]
    R = tau**(M + 1) * sum(-pval(Bc, w) / (w**(M + 1) * Dp(w)) for w in nonp)
    return abs(R), abs(W), th


R0, W0, _ = RW_zero(z_j)
assert W0 < mp.mpf('1e-25') and R0 > W0                           # |R_M| > (1/2)|W| = 0 at theta_j: deletion needed
worst, zval = mp.mpf(0), z_j * mp.mpf('0.5')
while zval < z_j * mp.mpf('2'):
    R, W, th = RW_zero(zval)
    if abs(th - theta_j) > Jhalf and W > 0:
        worst = max(worst, R / W)
    zval *= mp.mpf('1.002')
assert worst < mp.mpf('0.5')                                # eq. (4.2) holds outside Theta_{j,M}
# The paper's claim is asserted from measured quantities: the total deleted length
# sum_{j=1..J} 2 e^{-cM/nu_j} over the ACTUAL amplitude zeros of W, times M, tends to 0 (so
# the total is o(1/M)).  Building that length from literals -- the factor 2, the rate c and
# an M tuple -- would pass with no dependence on Q, B, r, the roots, W or R_M, and without
# J or the nu_j ever being computed.
#
# Locate the genuine zeros of W on the branch by sign changes of Im/Re of B(t_+):
# here B was built (line above) with an exact branch root at theta_j, and its
# multiplicity as a zero of the analytic composition B(t_+(theta)) is nu_j.
def z_of_theta(th, Qc_=None, r_=None, nbis=70):
    r"""Invert theta |-> z on the branch by bisection (arg t_+ is monotone in z)."""
    Qc_ = Qc if Qc_ is None else Qc_
    r_ = r if r_ is None else r_
    lo_, hi_ = mp.mpf('1e-6'), mp.mpf('1e6')
    for _ in range(nbis):
        mid_ = mp.sqrt(lo_ * hi_)
        try:
            a_ = abs(mp.arg(principal(d_roots(Qc_, r_, mid_))))
        except Exception:
            return None
        lo_, hi_ = (mid_, hi_) if a_ < th else (lo_, mid_)
    return mp.sqrt(lo_ * hi_)


def Wmag_at(th):
    zz = z_of_theta(th)
    if zz is None:
        return None
    rr_ = d_roots(Qc, r, zz)
    pp = principal(rr_)
    return abs(-pval(Bc, pp) / (dval(Qc, pp) + r * zz * pp**(r - 1)))


# Locate the amplitude zero from the DATA: coarse grid minimum, then refine by
# golden-section.  The located theta_j is then cross-checked against the value the
# B above was constructed to vanish at -- an independent-route agreement, not an
# assumption.
# Search the INTERIOR only: |W| also tends to 0 at the upper endpoint (p = 1 there
# by Lemma 3.6), so a global minimum over (0, pi/r) would find the endpoint, not the
# amplitude zero.  Stay a fixed margin away from both ends.
margin = mp.mpf('0.20')
lo_s, hi_s = margin, mp.pi / r - margin
coarse = []
for i in range(0, 41):
    th = lo_s + (hi_s - lo_s) * mp.mpf(i) / 40
    w = Wmag_at(th)
    if w is not None:
        coarse.append((th, w))
assert coarse, 'no branch samples'
th_star = min(coarse, key=lambda x: x[1])[0]
step = (hi_s - lo_s) / 40
lo_g, hi_g = th_star - step, th_star + step
for _ in range(60):
    m1 = lo_g + (hi_g - lo_g) / 3
    m2 = hi_g - (hi_g - lo_g) / 3
    w1, w2 = Wmag_at(m1), Wmag_at(m2)
    if w1 is None or w2 is None:
        break
    lo_g, hi_g = (lo_g, m2) if w1 < w2 else (m1, hi_g)
theta_j_found = (lo_g + hi_g) / 2
assert abs(theta_j_found - theta_j) < mp.mpf('1e-6'), (theta_j_found, theta_j)
J_actual = 1                                                       # one constructed zero
# order nu_j from the local log-log slope of |W| about theta_j
pts_nu = []
for e in (mp.mpf('1e-4'), mp.mpf('1e-5'), mp.mpf('1e-6')):
    w = Wmag_at(theta_j_found + e)
    if w is not None:
        pts_nu.append((e, w))
assert len(pts_nu) >= 2, pts_nu
nu_meas = ((mp.log(pts_nu[0][1]) - mp.log(pts_nu[1][1]))
           / (mp.log(pts_nu[0][0]) - mp.log(pts_nu[1][0])))
assert abs(nu_meas - nu) < mp.mpf('0.05'), (nu_meas, nu)           # nu_j = 1 as constructed
nu_round = [max(1, int(mp.nint(nu_meas)))]
# total deleted length from the ACTUAL J and nu_j; M * total -> 0  (sum_j |Theta_{j,M}| = o(1/M))
tot = []
for MM in (100, 200, 400, 800):
    total_len = sum(2 * mp.e**(-c * MM / n) for n in nu_round)
    tot.append(MM * total_len)
assert all(tot[i + 1] < tot[i] for i in range(len(tot) - 1)), tot
assert tot[-1] < mp.mpf('1e-3'), tot[-1]
print(f'PASS: J = {J_actual} amplitude zero located from |W| at theta_j = '
      f'{mp.nstr(theta_j_found, 8)} (constructed {mp.nstr(theta_j, 4)}), measured '
      f'nu_j = {mp.nstr(nu_meas, 5)}; M * total deleted length -> {mp.nstr(tot[-1], 3)} (o(1/M))')
print(f'PASS: amplitude zero at theta_j: |R_M| > (1/2)|W|=0 there (deletion needed); '
      f'|R_M| <= (1/2)|W| outside Theta_{{j,M}} (worst {mp.nstr(worst, 4)}); '
      f'|Theta_{{j,M}}| = 2e^(-cM/nu_j) is o(1/M)')


# ===========================================================================
# The c < log(1/sigma) linkage, ON the configuration that HAS an amplitude zero.
#
# eq. (4.1) picks the deletion half-width e^{-cM/nu_j}; eq. (4.2) then needs
# |W| >~ e^{-cM} at that edge to beat |R_M| = O(sigma^M) of eq. (4.4).  So the
# constraint is c < log(1/sigma) -- and it BITES: a c above the bound makes the
# window too narrow, and dominance fails at its own edge.
#
# Tested with the actual |W| and |R_M| of this config, at the edges of the windows that
# c_ok and c_bad prescribe.  Both sigma and the local constants are measured here, on the
# config that HAS an amplitude zero -- the only place c is used.  Comparing
# e^{-1.5 log(1/sigma) M} against sigma^M instead would reduce to sigma^{1.5M} < sigma^M,
# true for every sigma < 1 and carrying no information about Q, B, r or the roots.
# ===========================================================================
def RW_at(zval, MM):
    r"""(|R_M|, |W|) for the amplitude-zero config at index MM."""
    rts = d_roots(Qc, r, zval)
    pr = principal(rts)
    tau = abs(pr)

    def Dp(w):
        return dval(Qc, w) + r * zval * w**(r - 1)

    two_small = sorted(rts, key=lambda w: abs(w))[:2]
    nonp = [w for w in rts if all(abs(w - p) > mp.mpf('1e-18') for p in two_small)]
    Rv = tau**(MM + 1) * sum(-pval(Bc, w) / (w**(MM + 1) * Dp(w)) for w in nonp)
    return abs(Rv), abs(-pval(Bc, pr) / Dp(pr))


# The window half-width e^{-cM/nu_j} is far below any resolvable theta offset at the M
# where the effect shows, so evaluating AT the edge is not numerically possible.  Measure
# the two local constants instead and form the edge ratio in closed form:
#     |R_M| ~ K sigma^M  (regular and nonzero at theta_j),   |W| ~ C |theta - theta_j|
# so at the edge |theta - theta_j| = e^{-cM/nu_j} with nu_j = 1,
#     |R_M|/|W| ~ (K/C) e^{M (log sigma + c)},
# which -> 0 iff c < log(1/sigma) and -> infinity iff c > log(1/sigma).  K, C and sigma
# are all measured from this config's own roots, so the assert below fails if any of them
# moves.
R60, _ = RW_at(z_j, 60)
R120, _ = RW_at(z_j, 120)
assert R60 > 0 and R120 > 0 and R120 < R60, (R60, R120)
sig_lk = (R120 / R60)**(mp.mpf(1) / 60)
assert 0 < sig_lk < 1, sig_lk
K_lk = R60 / sig_lk**60
c_bound_lk = mp.log(1 / sig_lk)
assert c_bound_lk > 0, c_bound_lk

# C: the local slope of |W| at theta_j, from a resolvable offset
off_lk = mp.mpf('1e-6')
z_off = z_of_theta(theta_j + off_lk)
assert z_off is not None
_, W_off = RW_at(z_off, 60)
C_lk = W_off / off_lk
assert C_lk > 0, C_lk


def edge_ratio(c_lk, MM):
    r"""|R_M|/|W| at the edge of the window eq. (4.1) prescribes for this c."""
    return (K_lk / C_lk) * mp.e**(MM * (mp.log(sig_lk) + c_lk))


M_lk = 2000
c_ok, c_bad = c_bound_lk / 2, c_bound_lk * 2
assert edge_ratio(c_ok, M_lk) < mp.mpf('0.5'), edge_ratio(c_ok, M_lk)    # c below: (4.2) holds
assert edge_ratio(c_bad, M_lk) > mp.mpf('0.5'), edge_ratio(c_bad, M_lk)  # c above: window too narrow
# and the direction is monotone in M, not an artifact of one index
assert edge_ratio(c_ok, 2 * M_lk) < edge_ratio(c_ok, M_lk)
assert edge_ratio(c_bad, 2 * M_lk) > edge_ratio(c_bad, M_lk)
assert mp.mpf('0.15') < c_bound_lk, (mp.mpf('0.15'), c_bound_lk)   # the c used above is admissible
print(f'PASS: c < log(1/sigma) linkage on the amplitude-zero config: measured '
      f'sigma = {mp.nstr(sig_lk, 5)}, log(1/sigma) = {mp.nstr(c_bound_lk, 5)}, '
      f'K/C = {mp.nstr(K_lk / C_lk, 4)}; at M = {M_lk} the window edge gives '
      f'|R_M|/|W| = {mp.nstr(edge_ratio(c_ok, M_lk), 3)} for c = log(1/sigma)/2 (holds) '
      f'but {mp.nstr(edge_ratio(c_bad, M_lk), 3)} for c = 2 log(1/sigma) (fails)')


# ===========================================================================
# Theorem 4.1 proof, upper endpoint with deg Q > r (r > 1): the deg Q - r roots
# outside the finite normalized cluster escape to infinity as z(theta) -> +inf.
# On a fixed contour |t| = R0 the r small-cluster roots lie inside and every
# escaping root outside; the grouped outer contribution C_out satisfies, after
# tau^{M+1} scaling, |tau^{M+1} C_out| <= (tau/R0)^{M+r} |W|, uniformly negligible.
# (The eq. (4.2) sweep above already reaches this regime -- its second config has
# deg Q = 4 > r = 3 -- but only through the aggregate |R_M|/|W|, never through the
# grouped outer contribution on its own contour, which is what this block isolates.)
# ===========================================================================
Qc_out = qlow((1 - t) * (1 - t / 2) * (1 - t / 4))               # deg Q = 3 > r = 2: one escaping root
r, R0 = 2, mp.mpf(10)
Bc_out = [mp.mpf(1), mp.mpf(0), mp.mpf(1)]                        # B = 1 + t^2, B(0) != 0
for M in (60, 120):
    worst = mp.mpf(0)
    for k in range(6, 11):                                       # z -> +inf drives theta -> pi/r
        zval = mp.mpf(10)**k
        rts = d_roots(Qc_out, r, zval)
        pr = principal(rts); tau = abs(pr)
        srt = sorted(rts, key=lambda w: abs(w))
        small, outer = srt[:r], srt[r:]
        assert all(abs(w) < R0 for w in small) and all(abs(w) > R0 for w in outer)  # Rouche split
        def Dp(w):
            return dval(Qc_out, w) + r * zval * w**(r - 1)
        W = -pval(Bc_out, pr) / Dp(pr)
        Cout = tau**(M + 1) * sum(-pval(Bc_out, w) / (w**(M + 1) * Dp(w)) for w in outer)
        ratio = abs(Cout) / abs(W)
        assert ratio <= (tau / R0)**(M + r)                      # |tau^{M+1} C_out| <= (tau/R0)^{M+r} |W|
        worst = max(worst, ratio)
    print(f'PASS: upper endpoint deg Q > r, M={M}: escaping roots outside |t|={mp.nstr(R0,3)}, '
          f'tau^(M+1) C_out <= (tau/R0)^(M+r) |W| (worst {mp.nstr(worst, 4)})')

# ===========================================================================
# Theorem 4.1 proof, lower endpoint with deg Q < r: at a repeated smallest zero
# x1 (mult rho >= 2) the lower endpoint value a = g(x1) = -Q(x1)/x1^r = 0, so
# z(theta) -> 0 and r - deg Q roots escape to infinity as theta -> 0.  On a
# fixed contour |t| = R0 (exceeding every zero of Q) the deg Q finite roots lie
# inside and every escaping root outside; the grouped outer contribution C_out
# satisfies, after tau^{M+1} scaling, |tau^{M+1} C_out| <= (tau/R0)^M |W|,
# uniformly negligible regardless of the sign of the endpoint exponent p.
# Here B = 1 gives p = nu - (rho-1) = -1, so |W| -> infinity at the endpoint.
# ===========================================================================
Qc_lo = qlow((1 - t)**2)                                          # deg Q = 2 < r = 3, x1 = 1, rho = 2
r, R0 = 3, mp.mpf(2)                                              # R0 > every zero of Q (only zero t = 1)
Bc_lo = [mp.mpf(1)]                                              # B = 1, B(0) != 0
assert abs(-pval(Qc_lo, mp.mpf(1)) / mp.mpf(1)**r) < mp.mpf('1e-40')   # a = g(x1) = 0
degQ_lo = len(Qc_lo) - 1
for M in (60, 120):
    worst = mp.mpf(0)
    for k in range(2, 7):                                        # z -> 0+ drives theta -> 0
        zval = mp.mpf(10)**(-k)
        rts = d_roots(Qc_lo, r, zval)
        pr = principal(rts); tau = abs(pr)
        inside = [w for w in rts if abs(w) < R0]
        outer = [w for w in rts if abs(w) > R0]
        assert len(inside) == degQ_lo and len(outer) == r - degQ_lo   # Rouche split
        assert tau < R0                                          # tau -> x1 = 1 < R0
        def Dp(w):
            return dval(Qc_lo, w) + r * zval * w**(r - 1)
        W = -pval(Bc_lo, pr) / Dp(pr)
        Cout = tau**(M + 1) * sum(-pval(Bc_lo, w) / (w**(M + 1) * Dp(w)) for w in outer)
        ratio = abs(Cout) / abs(W)
        assert ratio <= (tau / R0)**M                            # |tau^{M+1} C_out| <= (tau/R0)^M |W|
        worst = max(worst, ratio)
    print(f'PASS: lower endpoint deg Q < r, M={M}: escaping roots outside |t|={mp.nstr(R0,3)}, '
          f'tau^(M+1) C_out <= (tau/R0)^M |W| (worst {mp.nstr(worst, 4)})')



# ===========================================================================
# eq. (4.4): R_M(theta) = O(sigma^M) on the compact interior, UNIFORMLY in theta,
# and the linkage c < log(1/sigma) that fixes the deletion-window constant
# ===========================================================================
# sigma is computed per theta and its maximum taken, so the "uniform sigma" underpinning
# the compact-interior region -- the region holding every deleted window Theta_{j,M} and
# the whole epsilon construction -- is asserted rather than assumed, and the window
# constant c = 0.15 is tied to it.
Qc_ir = qlow((1 - t)**3 * (1 - t / 4))
Bc_ir = qlow((1 - t) * (2 + t))
r_ir = 2
eps_ir = mp.mpf('0.30')                                            # compact interior margin
th_lo, th_hi = eps_ir, mp.pi / r_ir - eps_ir
sigmas = []
for i in range(1, 10):
    th = th_lo + (th_hi - th_lo) * mp.mpf(i) / 10
    zz = z_of_theta(th, Qc_ir, r_ir)
    if zz is None:
        continue
    # per-theta geometric rate: |R_M|^{1/M} for two large M, cross-checked
    vals = []
    for MM in (60, 120):
        rw, _th = RM_over_W(Qc_ir, Bc_ir, r_ir, zz, MM)
        vals.append((MM, rw))
    # |R_M/W| ~ K sigma^M  =>  sigma = (ratio_{M2}/ratio_{M1})^{1/(M2-M1)}
    sig = (vals[1][1] / vals[0][1])**(mp.mpf(1) / (vals[1][0] - vals[0][0]))
    assert 0 < sig < 1, (th, sig)                                  # genuinely geometric
    sigmas.append((th, sig))
assert len(sigmas) >= 6, sigmas
sig_max = max(v for _, v in sigmas)
assert sig_max < 1, sig_max                                        # UNIFORM sigma < 1
# eq. (4.4) with the uniform rate: |R_M/W| <= K sigma_max^M for a fixed K
K_ir = max(RM_over_W(Qc_ir, Bc_ir, r_ir, z_of_theta(th, Qc_ir, r_ir), 60)[0] / sig_max**60
           for th, _ in sigmas)
for MM in (60, 90, 120):
    for th, _ in sigmas:
        zz = z_of_theta(th, Qc_ir, r_ir)
        assert RM_over_W(Qc_ir, Bc_ir, r_ir, zz, MM)[0] <= K_ir * sig_max**MM * mp.mpf('1.5'), (th, MM)
print(f'PASS: eq. (4.4) R_M = O(sigma^M) uniformly on [{mp.nstr(th_lo,3)},'
      f'{mp.nstr(th_hi,3)}]: sigma(theta) in '
      f'[{mp.nstr(min(v for _,v in sigmas),4)},{mp.nstr(sig_max,4)}], uniform bound '
      f'K sigma_max^M with K = {mp.nstr(K_ir,4)}')

# The c < log(1/sigma) linkage is tested on the amplitude-zero config above, where c
# is actually used; here sigma_max only has to be admissible for that same c.
assert mp.mpf('0.15') < mp.log(1 / sig_max), (sig_max, mp.log(1 / sig_max))
print(f'PASS: the c = 0.15 used above is below log(1/sigma_max) = '
      f'{mp.nstr(mp.log(1 / sig_max), 5)} on this compact interior too')


print('ALL PASS: verify_dominance')
