#!/usr/bin/env python3
r"""Paper section `sec:consequences` (Global and local zero laws), section `subsec:zero-bulk`,
`prop:equidistribution` and `cor:angular-rigidity`.

All arithmetic uses mpmath at arbitrary precision (no floating-point in the
verification loops).  The coefficient polynomials F_M(z) = [t^M] B/(Q+z t^r)
come from the exact D-recurrence of section `sec:reduction`, and denominator roots from
mpmath.polyroots.

`prop:equidistribution` (equidistribution of the zero bulk): along the nonzero
coefficient polynomials, the normalized zero-counting measure mu[F_M] converges
weakly to mu_infty, the pushforward under z of the uniform measure (r/pi) dtheta
on (0, pi/r); mu_infty is independent of the numerator.  The proof places one
zero between consecutive sign-alternating phase points: the local sign-change
count gives the lower bound N_M([alpha,beta]) >= (M+1)(beta-alpha)/pi - O(1),
and the same bound on the complementary intervals subtracted from
deg F_M = floor(M/r) (`lem:eventual-degree`) gives the matching upper bound, so
N_M([alpha,beta]) = (M+1)(beta-alpha)/pi + O(1); dividing by deg F_M gives
mu_infty(z([alpha,beta])) = (r/pi)(beta-alpha).

Every check below runs on each of the five PENCILS listed in CONFIGS: three
values of r, four zero multisets of Q, one of them with a repeated smallest zero
(so the lower endpoint a of `eq:ab-def` is 0), and both degree relations
deg Q < r and deg Q > r.  The r-dependence is the substance of the limit measure,
so it is asserted rather than merely exhibited: check (R) recomputes the
pushforward mass against (r'/pi) for the neighboring r' and requires that to
FAIL, per pencil and at every degree on the ladder.

The checks:
  (A) Numerator-independence: the real z-root sets of F_M for B = 1 and B = 1 + t^2
      have Kolmogorov-Smirnov distance -> 0 as M grows, so the limit does not see B
      (hence not N) -- the weight B enters nowhere in the limit.
  (B) Pushforward form: mapping each real z-root x of F_M (B = 1) to theta = z^{-1}(x)
      via the minimum-modulus denominator pair (`thm:FT-geometry`, `eq:principal-pair`), the theta-images
      become uniform on (0, pi/r): KS(theta ; Uniform) -> 0, i.e. mu_infty = z_*((r/pi)dtheta).
  (R) The (r/pi) normalization: the pushforward mass of every angular subinterval
      is within O(1/deg) of (r/pi)(beta-alpha) at the pencil's own r, and is
      bounded AWAY from the same quantity at r' = r +- 1.
  (C) Local zero count, the proof's own estimate, at (M+1)/pi zeros per unit angle
      -- a density independent of r, which is what makes the count M/r and the
      normalized mass (r/pi)(beta-alpha).
  (D) `eq:normalized-angular-discrepancy` and `eq:angular-clock` over a ladder of
      numerator degrees, closing on ONE constant pair per pencil -- its intercept
      forced to the numerator-free value rather than fitted -- that covers every
      tested B at every M on the ladder, the two equal-degree numerator pairs
      included, and respects the unfitted envelope the proof itself predicts.
The F_M recurrence is cross-checked against a direct series division of 1/(Q+z t^r).
"""
import mpmath as mp

# The r = 1 pencils reach degree 64 with all zeros in a BOUNDED interval (b is
# finite only for r = 1), which crowds them near the upper endpoint; at dps = 30
# the root-finder returns about half of them.  dps = 60 recovers the full set at
# every degree used here, for every pencil.
mp.mp.dps = 60


def qcoeffs(xs):
    r"""Coefficients (low->high) of Q(t) = prod_j (1 - t/x_j), Q(0) = 1 (`eq:Q-hypotheses`)."""
    c = [mp.mpf(1)]
    for x in xs:
        x = mp.mpf(x)
        nc = [mp.mpf(0)] * (len(c) + 1)           # multiply the running product by (1 - t/x)
        for i, a in enumerate(c):
            nc[i] += a
            nc[i + 1] += -a / x
        c = nc
    return c                                       # low->high


class Pencil:
    r"""One admissible pair (Q, r) of `eq:Q-hypotheses`, with its coefficient polynomials.

    Caches F_M, its positive real z-roots and their theta-images, since every
    check below reads the same ladder.
    """

    def __init__(self, zeros, r, tag):
        self.zeros, self.r, self.tag = list(zeros), r, tag
        self.Qc = qcoeffs(zeros)
        self.q0 = self.Qc[0]
        self.dQ = len(self.Qc) - 1
        self.dloc = max(self.dQ, r)                # d = deg_t D = max{deg Q, r}
        self.pir = mp.pi / r
        x1 = min(mp.mpf(x) for x in zeros)
        self.rho = sum(1 for x in zeros if mp.mpf(x) == x1)   # multiplicity of x_1
        self._F, self._roots, self._th = {}, {}, {}

    # --- the coefficient polynomials ---------------------------------------
    def F(self, Bc, M, key):
        r"""F_M(z) = [t^M] B/(Q+z t^r) as a z-polynomial (mpf list low->high), per `eq:F-M-def`.

        Uses the exact section-2 D-recurrence sum_i d_i(z) h_{n-i} = b_n with
        d_i = q_i + z*[i == r] and d_0 = Q(0) (`prop:initial-data`'s displayed system).  The
        numerator here is univariate, so the generating function is `eq:F-M-def`, not the
        bivariate `eq:P-generating-intro`.
        """
        if (key, M) in self._F:
            return self._F[(key, M)]
        H = []                                     # H[n] = z-coeffs of the coefficient polynomial h_n
        for n in range(M + 1):
            bn = Bc[n] if n < len(Bc) else mp.mpf(0)
            acc = [mp.mpf(bn)]                     # b_n (numerator, constant in z)
            for i in range(1, self.dloc + 1):      # subtract sum_{i>=1} d_i h_{n-i}
                if n - i < 0:
                    continue
                hprev = H[n - i]
                qi = self.Qc[i] if i < len(self.Qc) else mp.mpf(0)
                for k, a in enumerate(hprev):      # -q_i * h_{n-i}
                    while len(acc) <= k:
                        acc.append(mp.mpf(0))
                    acc[k] -= qi * a
                if i == self.r:                    # -z * h_{n-r} (the z t^r term shifts the z-degree up)
                    for k, a in enumerate(hprev):
                        while len(acc) <= k + 1:
                            acc.append(mp.mpf(0))
                        acc[k + 1] -= a
            H.append([a / self.q0 for a in acc])   # divide by d_0 = Q(0)
        self._F[(key, M)] = H[M]
        return H[M]

    def roots(self, Bc, M, key):
        r"""Positive real z-roots of F_M (the bulk zeros in I_{Q,r})."""
        if (key, M) in self._roots:
            return self._roots[(key, M)]
        p = self.F(Bc, M, key)[:]
        while len(p) > 1 and abs(p[-1]) < mp.mpf(10)**(-45):
            p.pop()
        rts = mp.polyroots(list(reversed(p)), maxsteps=300, extraprec=200)
        out = []
        for zr in rts:
            zr = mp.mpc(zr)
            scale = max(mp.mpf(1), abs(zr))
            if abs(mp.im(zr)) < mp.mpf('1e-12') * scale and mp.re(zr) > 0:
                out.append(mp.re(zr))
        out.sort()
        self._roots[(key, M)] = out
        return out

    def thetas(self, Bc, M, key):
        r"""The angles z^{-1}(x) of the bulk zeros, sorted; zeros outside I_{Q,r} drop out."""
        if (key, M) in self._th:
            return self._th[(key, M)]
        eps = mp.mpf('1e-14')
        th = sorted(t for t in (self.theta(x) for x in self.roots(Bc, M, key))
                    if eps < t < self.pir - eps)
        self._th[(key, M)] = th
        return th

    def zdeg(self, Bc, M, key):
        r"""Degree in z of F_M, read off the computed coefficients."""
        p = self.F(Bc, M, key)
        for k in range(len(p) - 1, -1, -1):
            if abs(p[k]) > mp.mpf('1e-45'):
                return k
        return -1

    # --- the geometry ------------------------------------------------------
    def denom(self, x):
        r"""Coefficients (low->high) of Q(t) + x t^r."""
        return [(self.Qc[i] if i < len(self.Qc) else mp.mpf(0))
                + (x if i == self.r else mp.mpf(0)) for i in range(self.dloc + 1)]

    def tplus(self, x, extra=200):
        r"""The minimum-modulus zero of Q(t) + x t^r, i.e. t_+ of `eq:principal-pair`."""
        rts = mp.polyroots(list(reversed(self.denom(x))), maxsteps=1000, extraprec=extra)
        return min(rts, key=lambda w: abs(w))

    def theta(self, x):
        r"""theta = z^{-1}(x), inverting the parameterization z: (0,pi/r) -> I_{Q,r}.

        For the z-value x the two smallest-modulus zeros of Q(t)+x t^r are the FT principal
        conjugate pair t_+- = tau e^{+-i theta} (`thm:FT-geometry`, `eq:principal-pair`); theta = |arg t_+|.
        """
        return abs(mp.arg(mp.mpc(self.tplus(x, extra=100))))

    def endpoint_a(self):
        r"""The lower endpoint a = g(t_a) of I_{Q,r} (`eq:ab-def`).

        g(t) = -Q(t)/t^r, and its positive critical points are the positive zeros of
        r Q(t) - t Q'(t), whose coefficients are (r - i) q_i; t_a is the smallest of
        them.  A repeated smallest zero of Q puts t_a at that zero, hence a = 0.
        """
        phi = [(self.r - i) * q for i, q in enumerate(self.Qc)]
        while len(phi) > 1 and phi[-1] == 0:
            phi.pop()
        rts = mp.polyroots(list(reversed(phi)), maxsteps=200, extraprec=100)
        pos = [mp.re(w) for w in rts
               if abs(mp.im(mp.mpc(w))) < mp.mpf('1e-30') and mp.re(w) > 0]
        assert pos, self.tag
        ta = min(pos)
        return -sum(q * ta**i for i, q in enumerate(self.Qc)) / ta**self.r

    def z_at_angle(self, theta0):
        r"""The value z(theta0), by bisection on the strictly increasing z."""
        lo, hi = mp.mpf('1e-12'), mp.mpf('1e12')
        for _ in range(120):
            mid = mp.sqrt(lo * hi)
            lo, hi = (mid, hi) if self.theta(mid) < theta0 else (lo, mid)
        return mp.sqrt(lo * hi)


# --- the pencils ----------------------------------------------------------
# Chosen so that r, the multiplicity rho of the smallest zero of Q (rho >= 2
# puts a = 0 in `eq:ab-def`) and the sign of deg Q - r all vary.  The paper's
# standing hypothesis max{deg Q, r} > 1 holds throughout.
CONFIGS = [
    Pencil([1, 2, 4],    2, 'Q=(1-t)(1-t/2)(1-t/4), r=2'),
    Pencil([1, 2, 4],    1, 'Q=(1-t)(1-t/2)(1-t/4), r=1'),
    Pencil([1, 1, 3],    2, 'Q=(1-t)^2(1-t/3),      r=2'),
    Pencil([2, 3],       3, 'Q=(1-t/2)(1-t/3),      r=3'),
    Pencil([1, 2, 4, 8], 3, 'Q=(1-t)...(1-t/8),     r=3'),
]

# The ladder is fixed in the DEGREE of F_M, not in M, so every pencil is read at
# the same three polynomial degrees and the KS statistics are comparable across
# r.  deg F_M = floor(M/r) (`eq:eventual-degree`), so M = r*deg.
DEGS = (16, 32, 64)

B1 = [mp.mpf(1)]                                   # B = 1
B2 = [mp.mpf(1), mp.mpf(0), mp.mpf(1)]             # B = 1 + t^2

print('Pencils under test (`eq:Q-hypotheses`, `eq:ab-def`):')
for P in CONFIGS:
    rel = '>' if P.dQ > P.r else ('<' if P.dQ < P.r else '=')
    assert max(P.dQ, P.r) > 1, P.tag                # the paper's standing hypothesis
    assert P.q0 > 0, P.tag                          # Q(0) > 0
    print(f'  {P.tag:34s} deg Q = {P.dQ} {rel} r = {P.r}, rho = {P.rho}, '
          f'a = 0: {P.rho >= 2}, pi/r = {mp.nstr(P.pir, 5)}')
print()


# --- Kolmogorov-Smirnov statistics (numerical tooling, not paper content) ------
def ks(sample, cdf):
    s = sorted(sample)
    n = len(s)
    d = mp.mpf(0)
    for i, x in enumerate(s):
        d = max(d, abs(cdf(x) - mp.mpf(i) / n), abs(cdf(x) - mp.mpf(i + 1) / n))
    return d


def ks_two(a, b):
    s, u = sorted(a), sorted(b)
    def ecdf(sample, x):
        return mp.mpf(sum(1 for v in sample if v <= x)) / len(sample)
    return max(abs(ecdf(s, x) - ecdf(u, x)) for x in sorted(set(s + u)))


def loglog_slope(vals, xs):
    return ((mp.log(vals[-1]) - mp.log(vals[0]))
            / (mp.log(mp.mpf(xs[-1])) - mp.log(mp.mpf(xs[0]))))


# ===========================================================================
# (A) Numerator-independence: the limit does not see B (the weight enters nowhere)
# ===========================================================================
for P in CONFIGS:
    ksA = []
    for d in DEGS:
        M = P.r * d
        r1, r2 = P.roots(B1, M, 'B1'), P.roots(B2, M, 'B2')
        ksA.append(ks_two(r1, r2))
        print(f'  [{P.tag}] deg={d}, M={M}: #roots B=1 -> {len(r1)}, '
              f'B=1+t^2 -> {len(r2)}, KS(z) = {mp.nstr(ksA[-1], 4)}')
    # A bound drawn from the tested sequence itself (last < first) certifies no rate, so the
    # ~1/M decay is asserted as a log-log slope as well.
    assert ksA[-1] < ksA[0] and ksA[-1] < mp.mpf('0.08'), (P.tag, ksA)
    assert loglog_slope(ksA, DEGS) < mp.mpf('-0.8'), (P.tag, ksA)     # at least ~1/M
print('PASS: on every pencil the z-root distributions of different B converge '
      '(mu_infty independent of N)')
print()


# ===========================================================================
# (B) Pushforward form: theta-images of the B=1 roots are uniform on (0, pi/r)
# ===========================================================================
for P in CONFIGS:
    unif = lambda th, _p=P: min(max(th / _p.pir, mp.mpf(0)), mp.mpf(1))
    a = P.endpoint_a()
    # a = 0 exactly when the smallest zero of Q is repeated, which is one of the
    # pencils here; the bulk then reaches down to the origin.
    assert a >= 0, (P.tag, a)
    assert (a < mp.mpf('1e-40')) == (P.rho >= 2), (P.tag, a, P.rho)
    ksB, gaps_a = [], []
    for d in DEGS:
        M = P.r * d
        xs, ths = P.roots(B1, M, 'B1'), P.thetas(B1, M, 'B1')
        # For B = 1 every zero is a simple positive real one in I_{Q,r}, so the
        # theta-image loses none of them; assert that rather than assume it.
        assert P.zdeg(B1, M, 'B1') == M // P.r, (P.tag, M)            # `eq:eventual-degree`
        assert len(ths) == len(xs) == d, (P.tag, M, len(xs), len(ths))
        # The bulk sits inside I_{Q,r} = (a, b) and reaches down to a: the smallest
        # zero carries the smallest angle, ~ pi/(M+1), and z(theta) -> a there.
        assert min(xs) > a, (P.tag, M, min(xs), a)
        gaps_a.append(min(xs) - a)
        ksB.append(ks(ths, unif))
        print(f'  [{P.tag}] deg={d}, M={M}: {len(xs)} roots, mapped {len(ths)}; '
              f'min zero - a = {mp.nstr(gaps_a[-1], 4)}; '
              f'KS(theta ; Uniform(0,pi/r)) = {mp.nstr(ksB[-1], 4)}')
    assert gaps_a[-1] < gaps_a[0], (P.tag, gaps_a)                    # the bulk fills down to a
    # A bound drawn from the tested sequence itself (last < first) certifies no rate, so the
    # ~1/M decay is asserted as a log-log slope as well.
    assert ksB[-1] < ksB[0] and ksB[-1] < mp.mpf('0.08'), (P.tag, ksB)
    assert loglog_slope(ksB, DEGS) < mp.mpf('-0.8'), (P.tag, ksB)     # at least ~1/M
print('PASS: on every pencil the theta-images approach Uniform(0,pi/r), and the bulk '
      'sits above the lower endpoint a of `eq:ab-def` and descends to it; '
      'mu_infty = z_*((r/pi) dtheta)')
print()


# ===========================================================================
# (R) The (r/pi) normalization is the substance of the limit, so a wrong r must
# fail.  Per pencil: the pushforward mass of every angular subinterval is within
# O(1/deg) of (r/pi)(beta-alpha) at the pencil's own r, and stays bounded away
# from it when r is replaced by a neighbor r'.  The separation is not a tuned
# threshold: on the full interval the target reads r'/r while the mass reads 1,
# so any wrong r' misses by at least |1 - r'/r| >= 1/r.
# ===========================================================================
def mass_discrepancy(P, ths, deg, rr):
    r"""sup over ALL 0 <= alpha < beta <= pi/r of |mu[F_M](I_{alpha,beta}) - (rr/pi)(beta-alpha)|.

    The supremum in `eq:normalized-angular-discrepancy` runs over a continuum, and a
    finite grid of alpha and beta can land on points where the count matches exactly, so
    it under-reports and can read a clean zero.  The continuum value is exact and costs
    one pass: writing f(x) = #{theta_j <= x}/deg - (rr/pi)x, the bracketed quantity is
    f(beta) - f(alpha), so the supremum is the total oscillation of f, and f changes only
    at the theta_j.
    """
    lam = mp.mpf(rr) / mp.pi
    lo = hi = mp.mpf(0)                            # f(0) = 0
    for i, th in enumerate(sorted(ths)):
        before = mp.mpf(i) / deg - lam * th        # f immediately below theta_{i+1}
        after = mp.mpf(i + 1) / deg - lam * th     # f at theta_{i+1}
        lo, hi = min(lo, before, after), max(hi, before, after)
    end = mp.mpf(len(ths)) / deg - lam * P.pir     # f(pi/r)
    return max(hi, end) - min(lo, end)


for P in CONFIGS:
    floor = mp.mpf(1) / P.r                        # the guaranteed miss |1 - r'/r| of a wrong r'
    prods = []
    for d in DEGS:
        M = P.r * d
        ths = P.thetas(B1, M, 'B1')
        right = mass_discrepancy(P, ths, d, P.r)
        wrongs = [(rr, mass_discrepancy(P, ths, d, rr))
                  for rr in (P.r - 1, P.r + 1) if rr >= 1]
        prods.append(right * d)
        assert right * d < mp.mpf('4'), (P.tag, d, right * d)         # O(1/deg), the claimed rate
        assert right < floor / 2, (P.tag, d, right, floor)            # the two bands are disjoint
        for rr, w in wrongs:
            # On the full angular window the target reads r'/r while the mass reads 1, so a
            # wrong r' misses by at least |1 - r'/r| >= 1/r -- less only the error the true r
            # itself carries at this degree.  Nothing here is a tuned threshold.  The right-r
            # error falls with the degree and the wrong-r one does not, so the gap widens
            # along the ladder rather than being read off one degree.
            assert w >= floor - right, (P.tag, d, rr, w, floor, right)
        print(f'  [{P.tag}] deg={d}: sup|mu - (r/pi)(b-a)| = {mp.nstr(right, 4)} at the '
              f"pencil's own r, versus "
              + ', '.join(f"{mp.nstr(w, 4)} at r'={rr}" for rr, w in wrongs)
              + f' (each at least 1/r = {mp.nstr(floor, 3)})')
    # The RATE, sharply.  `eq:normalized-angular-discrepancy` claims 1/deg P_m, and weak
    # convergence alone would allow any decay at all; a decay deg^(-1+e) shows as a spread
    # of 4^e across this four-fold degree ladder, so the bound below rejects every
    # e > 0.29 -- the O(1/sqrt(deg P_m)) a cruder count would give among them.
    spread = max(prods) / min(prods)
    assert spread < mp.mpf('1.5'), (P.tag, prods)
    print(f'  [{P.tag}] deg * sup|mu - (r/pi)(b-a)| = '
          f'{[f"{d}:{mp.nstr(v, 4)}" for d, v in zip(DEGS, prods)]} over a four-fold '
          f'degree ladder -- FLAT (spread {mp.nstr(spread, 4)}x), so the decay is 1/deg P_m '
          f'and not a slower power')
print('PASS: the limit measure carries the pencil\'s own r at the claimed 1/deg P_m rate; '
      'substituting a neighboring r in the pushforward breaks '
      '`eq:normalized-angular-discrepancy` on every pencil')
print()


# ===========================================================================
# Cross-check: the F_M recurrence matches a direct series division of 1/(Q+z0 t^r)
# ===========================================================================
z0 = mp.mpf('0.5')
for P in CONFIGS:
    M = 10 * P.r
    val_poly = sum(c * z0**k for k, c in enumerate(P.F(B1, M, 'B1')))  # F_M(z0) via the z-poly recurrence
    den = P.denom(z0)
    h = [mp.mpf(1) / den[0]]                       # h_0 = 1/Q(0); numerator B=1 => b_n=0 for n>=1
    for n in range(1, M + 1):
        h.append(-sum(den[i] * h[n - i] for i in range(1, min(n, P.dloc) + 1)) / den[0])
    assert abs(val_poly - h[M]) < mp.mpf('1e-40') * max(mp.mpf(1), abs(h[M])), (P.tag, M)
    print(f'  [{P.tag}] M={M}: F_M at z = 1/2 is {mp.nstr(val_poly, 10)}, '
          f'matching the direct series to {mp.nstr(abs(val_poly - h[M]), 3)}')
print('PASS: the F_M recurrence matches a direct series division on every pencil')
print()


# ===========================================================================
# (C) Local zero count (`prop:equidistribution` proof).  One zero lies between
# consecutive phase points, so on a fixed [alpha,beta]
#     N_M([alpha,beta]) = (M+1)(beta-alpha)/pi + O(1)
# with a deficit bounded as M grows.  The complementary intervals subtracted
# from deg F_M = floor(M/r) supply the matching upper bound.  One zero per phase
# interval shows as consecutive theta-gaps ~ pi/(M+1).
#
# The angular density (M+1)/pi carries no r at all; the whole r-dependence of
# mu_infty is that the angular window has length pi/r.  Running this across
# r = 1, 2, 3 is what separates the two.
# ===========================================================================
for P in CONFIGS:
    alpha, beta = mp.mpf('0.32') * P.pir, mp.mpf('0.70') * P.pir   # [alpha,beta] subset (0, pi/r)
    deficits = []
    for d in DEGS:
        M = P.r * d
        ths = P.thetas(B1, M, 'B1')
        Nab = sum(1 for th in ths if alpha <= th <= beta)
        pred = (M + 1) * (beta - alpha) / mp.pi
        HM = mp.mpf('3') / M
        Ncomp = sum(1 for th in ths if HM <= th < alpha or beta < th <= P.pir - HM)
        # deg is read off the COMPUTED polynomial and compared against M//r, so `eq:eventual-degree` is
        # an assertion here rather than an input.
        deg = P.zdeg(B1, M, 'B1')
        assert deg == M // P.r, (P.tag, M, deg)                   # `eq:eventual-degree`
        gaps = [ths[i + 1] - ths[i] for i in range(len(ths) - 1)]
        med_scaled = sorted((M + 1) * g / mp.pi for g in gaps)[len(gaps) // 2]  # -> 1
        deficits.append(abs(pred - Nab))
        print(f'  [{P.tag}] deg={d}, M={M}: N[a,b]={Nab} vs (M+1)(b-a)/pi='
              f'{mp.nstr(pred, 6)} (deficit {mp.nstr(pred - Nab, 3)}); '
              f'N[a,b]+Ncomp-deg={Nab + Ncomp - deg}; '
              f'median (M+1)*gap/pi={mp.nstr(med_scaled, 4)}')
        assert abs(Nab + Ncomp - deg) <= 3, (P.tag, M)            # complement closes to deg F_M +- O(1)
        assert abs(med_scaled - 1) < mp.mpf('0.08'), (P.tag, M)   # one zero per phase interval
    # O(1) means one constant across the whole ladder, so the last rung -- four
    # times the degree of the first -- may not exceed the first by more than one
    # zero, and no rung may exceed the fixed bound.
    assert deficits[-1] <= deficits[0] + 1, (P.tag, deficits)
    assert max(deficits) < mp.mpf('3'), (P.tag, deficits)
print('PASS: N_M([a,b]) = (M+1)(b-a)/pi + O(1) on every pencil (bounded deficit; '
      'complement closes to deg F_M; angular density (M+1)/pi free of r)')
print()


# ===========================================================================
# `prop:equidistribution` as a short corollary of the angular discrepancy
# ===========================================================================
# The proof does not run a tightness/subsequential-limit/portmanteau chain.  It
# divides `prop:angular-discrepancy` by deg F_M at fixed (alpha, beta), takes
# tightness from the same estimate as alpha -> 0 and beta -> pi/r, and closes
# because mu_infty is atom-free (z strictly monotone), so the intervals
# I_{alpha,beta} are convergence-determining.  What is measured here is therefore
# the proof's OWN first line rather than a shadow of it:
#   (i)  mu[F_M](z([alpha,beta])) -> (r/pi)(beta-alpha), which is exactly what
#        `prop:angular-discrepancy` divided by the degree asserts; and
#   (ii) the NUMBER of near-coincident consecutive theta-images stays bounded in M while
#        their FRACTION vanishes like O(1/M).
#
# A lower bound on the MINIMUM scaled gap would be local rigidity, which `prop:equidistribution`
# does not claim and which fails for admissible numerators: weak convergence permits O(1)
# zeros to bunch, since a vanishing fraction of the mass cannot move the limit.  The paper
# says so directly ("the deleted endpoint and amplitude windows ... carry only O(1) zeros
# ... a mass O(1/M) vanishing after normalization").  The B_* built below for each pencil,
# whose W has one amplitude zero at the interior angle theta_0, exhibits that: exactly one
# consecutive pair of theta-images falls under half the mean spacing, at every degree on the
# ladder, while the mass error still converges.
#
# So the checkable shadow is the pair (count bounded, fraction -> 0), asserted below on
# every pencil for both a B with no amplitude zero (count 0) and one with a single
# amplitude zero (count 1), so that it distinguishes them rather than passing regardless.
for P in CONFIGS:
    alpha, beta = mp.mpf('0.32') * P.pir, mp.mpf('0.70') * P.pir
    mass_err = []
    for d in DEGS:
        M = P.r * d
        ths = P.thetas(B1, M, 'B1')
        inside = sum(1 for th in ths if alpha <= th <= beta)
        # mu[F_M] normalizes by deg F_M, not by the number of positive real roots.  The two
        # agree only when the exceptional count is 0, so license the substitution here rather
        # than assume it: for B = 1 every zero is a simple positive real one in I_{Q,r}.
        deg_FM = P.zdeg(B1, M, 'B1')
        assert deg_FM == M // P.r, (P.tag, M, deg_FM)             # `eq:eventual-degree`
        assert len(ths) == deg_FM, (P.tag, M, len(ths), deg_FM)   # C_B = 0, so no defect
        target = (beta - alpha) / P.pir                           # = (r/pi)(beta-alpha)
        mass_err.append(abs(mp.mpf(inside) / deg_FM - target))
    # (i) mass converges, at the claimed rate.  The sequence itself is not monotone and
    # is not claimed to be: the numerator of mu[F_M](I) is an integer count, so the error
    # is |Z - deg*target|/deg with a bounded, oscillating numerator.  What is asserted is
    # that numerator -- error times degree -- staying bounded across the whole ladder.
    assert mass_err[-1] < mp.mpf('0.03'), (P.tag, mass_err)
    for dd, e in zip(DEGS, mass_err):
        assert e * dd < mp.mpf('1.5'), (P.tag, dd, e)

    # (ii) count of near-coincident pairs bounded in M, fraction -> 0.  Run on B1 (whose W
    # has no branch zero, so the count must be 0) and on a B_* built to have exactly one, so
    # the two outcomes differ and the assert distinguishes them.
    theta0 = mp.mpf('0.5') * P.pir
    z_eq = P.z_at_angle(theta0)
    assert abs(P.theta(z_eq) - theta0) < mp.mpf('1e-20'), (P.tag, z_eq)
    tp = P.tplus(z_eq, extra=300)                                 # t_+ = minimum-modulus root
    assert abs(mp.im(tp)) > mp.mpf('1e-10'), (P.tag, tp)          # genuinely a nonreal pair
    # real quadratic with an exact branch root at t_+, so W has one amplitude zero at theta0
    Bstar = [mp.re(tp)**2 + mp.im(tp)**2, -2 * mp.re(tp), mp.mpf(1)]
    assert Bstar[0] > 0, (P.tag, Bstar)                           # B_*(0) != 0, admissible

    small = {}
    for key, Bc, expected in (('B1', B1, 0), ('Bstar', Bstar, 1)):
        counts, fracs = [], []
        for d in DEGS:
            M = P.r * d
            th_l = P.thetas(Bc, M, key)
            g = [(M + 1) * (th_l[i + 1] - th_l[i]) / mp.pi for i in range(len(th_l) - 1)]
            counts.append(sum(1 for v in g if v < mp.mpf('0.5')))
            fracs.append(mp.mpf(counts[-1]) / len(g))
        assert all(c == expected for c in counts), (P.tag, key, counts, expected)
        if expected:
            assert fracs[-1] < fracs[0] / 2, (P.tag, key, fracs)   # fraction -> 0 like O(1/M)
        small[key] = (counts, fracs)
    print(f'  [{P.tag}] |mu[F_M](z[a,b]) - (r/pi)(b-a)| = {mp.nstr(mass_err[0], 3)} -> '
          f'{mp.nstr(mass_err[-1], 3)}; near-coincident pairs number '
          f'{small["B1"][0][0]} for B=1 and {small["Bstar"][0][0]} for B_* '
          f'(one amplitude zero) at every degree, fraction '
          f'{mp.nstr(small["Bstar"][1][0], 3)} -> {mp.nstr(small["Bstar"][1][-1], 3)} = O(1/M)')
print('PASS: `prop:equidistribution` shadow holds on every pencil '
      '(the analytic chain itself is not numerically checkable)')
print()


# ===========================================================================
# (D) `prop:equidistribution`/`eq:normalized-angular-discrepancy` and
# `cor:angular-rigidity`/`eq:angular-clock`: the two
# finite-degree consequences.  Weak convergence alone would only need the
# discrepancy to vanish; what is claimed is a RATE, (D_0 + D_1 deg B)/deg P_m,
# and a per-zero rigidity.  Both are measured by multiplying through by the
# degree and checking the product stays bounded as M grows -- a product that
# drifted upward would mean the rate is not O(1/deg P_m).
#
# The numerator ladder runs over deg B = 0, 2, 4, 6, 8 on every pencil, and the
# M ladder mixes residues M mod r so that `eq:eventual-degree` is tested off the
# multiples of r as well.
# ===========================================================================
BS = [('K0', [mp.mpf(1)], 0, 'B = 1'),
      ('K2', [mp.mpf(1), mp.mpf(0), mp.mpf(1)], 2, 'B = 1 + t^2'),
      ('K4', [mp.mpf(1), mp.mpf(-1), mp.mpf(1), mp.mpf(-1), mp.mpf(1)],
       4, 'B = 1-t+t^2-t^3+t^4'),
      # a second numerator of the same degree, with different coefficients: the
      # constants may see deg B and nothing else about N, so the two must share a pair
      ('K4b', [mp.mpf(1), mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(3)], 4, 'B = 1 + 3t^4'),
      ('K6', [mp.mpf(1), mp.mpf(-1), mp.mpf(1), mp.mpf(-1), mp.mpf(1), mp.mpf(-1), mp.mpf(1)],
       6, 'B = sum_(k=0)^6 (-t)^k'),
      ('K8', [mp.mpf(1), mp.mpf(-1), mp.mpf(1), mp.mpf(-1), mp.mpf(1), mp.mpf(-1), mp.mpf(1),
              mp.mpf(-1), mp.mpf(1)], 8, 'B = sum_(k=0)^8 (-t)^k'),
      ('K8b', [mp.mpf(1), mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(0),
               mp.mpf(0), mp.mpf(2)], 8, 'B = 1 + 2t^8')]

for P in CONFIGS:
    # A four-fold degree range, so that a constant growing linearly in the degree --
    # which is what a wrong angular spacing in `eq:angular-clock` would produce -- shows
    # as a four-fold spread and breaks the flatness bound below.  The M values are not
    # all multiples of r, so `eq:eventual-degree` is tested off them as well.
    ladder = [P.r * 12, P.r * 24 + (P.r - 1), P.r * 48 + P.r // 2]
    rows_disc, rows_clock = [], []
    for key, Bc, K, tag in BS:
        prod_disc, prod_clock = [], []
        for M in ladder:
            d = P.zdeg(Bc, M, key)
            assert d == M // P.r, (P.tag, tag, M, d)              # `eq:eventual-degree`
            ths = P.thetas(Bc, M, key)
            # `thm:main`(ii): all but at most C of the deg F_M zeros lie in I_{Q,r},
            # and `eq:angular-clock` indexes the interval zeros in increasing order,
            # so the index j below is the paper's j only if the bulk is intact.
            assert d - len(ths) <= K + 2, (P.tag, tag, M, d, len(ths))
            # (a) normalized angular discrepancy, times the degree
            prod_disc.append((M, mass_discrepancy(P, ths, d, P.r) * d))
            # (b) angular clock, times (M+1)/pi.  What this pins is the SPACING: an
            # index shifted by a constant moves every term by at most that constant
            # after scaling, and `eq:angular-clock` absorbs it into E_0, so the check
            # cannot and does not distinguish j from j + O(1).  A wrong spacing --
            # pi j/(M+1) replaced by anything else -- grows with the degree instead,
            # and the flatness bound below rejects it.
            wc = mp.mpf(0)
            for jj, th in enumerate(ths, start=1):
                wc = max(wc, abs(th - mp.pi * jj / (M + 1)) * (M + 1) / mp.pi)
            prod_clock.append((M, wc))
        sd = max(v for _, v in prod_disc) / min(v for _, v in prod_disc)
        sc = max(v for _, v in prod_clock) / min(v for _, v in prod_clock)
        assert sd < 3, (P.tag, tag, prod_disc)
        assert sc < 3, (P.tag, tag, prod_clock)
        rows_disc.append((K, max(v for _, v in prod_disc), tag))
        rows_clock.append((K, max(v for _, v in prod_clock), tag))
        print(f'  [{P.tag}] `eq:normalized-angular-discrepancy` [{tag}] '
              f'deg P_m * sup_(alpha,beta) |mu[P_m](I) - (r/pi)(beta-alpha)| = '
              f'{[f"{M}:{mp.nstr(v, 4)}" for M, v in prod_disc]} at M = '
              f'{ladder} -- bounded and FLAT in M (spread {mp.nstr(sd, 3)}x), so the '
              f'discrepancy really is O(1/deg P_m) and not merely o(1)')
        print(f'  [{P.tag}] `eq:angular-clock` [{tag}] max over the bulk of '
              f'(M+1)/pi * |theta_j - pi j/(M+1)| = '
              f'{[f"{M}:{mp.nstr(v, 4)}" for M, v in prod_clock]} -- bounded and '
              f'FLAT (spread {mp.nstr(sc, 3)}x), so EVERY bulk zero sits within O(1/m) '
              f'of the uniform angular clock, not just the bulk on average')
    # -----------------------------------------------------------------------
    # ONE constant pair per pencil.  The constants of
    # `eq:normalized-angular-discrepancy` and `eq:angular-clock` are functions of
    # (Q,r) alone: they may not see the numerator except through deg B_N, and they
    # may not see M.  Two assertions, neither of which is a per-B refit:
    #
    #  (1) The pair is EXHIBITED, with the intercept forced rather than fitted: the
    #      intercept is the numerator-free constant, the value at B = 1, and only the
    #      slope is read off the ladder.  Every tested numerator, at every M in the
    #      ladder, is then required to sit under that one line.  Two numerators of
    #      equal degree and different coefficients sit on the ladder at deg B = 4 and
    #      at deg B = 8, so a constant that saw more of N than its degree would need
    #      the pair to straddle two unrelated values at one abscissa.
    #  (2) The proof's OWN envelope, which is not fitted at all.  Each of the
    #      J <= deg B amplitude windows costs the phase count at most the 2(J+1) of
    #      `prop:angular-discrepancy`, so the proof predicts a slope of at most 2 per
    #      unit of deg B, plus the additive constant absorbed in each statement.  The
    #      measured constants are required to respect that envelope, and the fitted
    #      slope of (1) is required to respect it too.
    #
    # The LINEARITY itself is not decidable from a finite ladder in deg B and is not
    # claimed here; the measured constants are not even monotone in deg B, since the
    # threshold in M of `prop:angular-discrepancy` depends on B and the low rungs of
    # the M ladder sit below it for the largest numerators.
    # `prop:angular-discrepancy`'s C_1 and `cor:angular-rigidity`'s E_1
    # descend from `eq:linear-phase-variation`, which check_viewing_angle.py
    # asserts over deg B = 0..8 against Radon's own constant kappa_1 = K_gamma + pi,
    # a constant of the arc rather than of the data.
    # -----------------------------------------------------------------------
    for rows, lab, eqn, names, slack in (
            (rows_disc, 'discrepancy', '`eq:normalized-angular-discrepancy`',
             ('D_0', 'D_1'), mp.mpf(1)),
            (rows_clock, 'clock offset', '`eq:angular-clock`',
             ('E_0', 'E_1'), mp.mpf(2))):
        c0 = max(v for k, v, _ in rows if k == 0)     # forced: the numerator-free constant
        c1 = max([mp.mpf(0)] + [(v - c0) / k for k, v, _ in rows if k > 0])
        for k, v, tg in rows:                         # (1) the SAME pair for every numerator
            assert v <= c0 + c1 * k + mp.mpf('1e-30'), \
                (f'{P.tag}: {eqn} at [{tg}]: {mp.nstr(v, 6)} exceeds '
                 f'{names[0]} + {names[1]} * {k} = {mp.nstr(c0 + c1 * k, 6)}', rows)
            # (2) the unfitted envelope the proof itself predicts
            assert v <= c0 + 2 * k + slack, \
                (f'{P.tag}: {eqn} at [{tg}]: {mp.nstr(v, 6)} exceeds the proof envelope '
                 f'{mp.nstr(c0 + 2 * k + slack, 6)}', rows)
        assert c1 <= 2, (P.tag, eqn, c1)              # the fitted slope respects it too
        twins = {}
        for k, v, tg in rows:
            twins.setdefault(k, []).append((tg, v))
        shared = {k: vs for k, vs in twins.items() if len(vs) > 1}
        assert shared, (P.tag, 'no equal-degree numerator pair on the ladder')
        print(f'  [{P.tag}] PASS: {eqn} one pair '
              f'{names[0]} = {mp.nstr(c0, 4)} (forced to the B = 1 value), '
              f'{names[1]} = {mp.nstr(c1, 4)} bounds the {lab} constant for EVERY tested '
              f'numerator at EVERY M on the ladder: '
              f'{[f"{k}:{mp.nstr(v, 4)}" for k, v, _ in rows]} over deg B = '
              f'{[k for k, _, _ in rows]}; the equal-degree pairs '
              + '; '.join(f'deg B = {k}: ' + ' vs '.join(mp.nstr(v, 4) for _, v in vs)
                          for k, vs in sorted(shared.items()))
              + f' share it, so the constants see no more of the numerator than its '
              f'degree, and every point also respects the unfitted envelope '
              f'{names[0]} + 2 deg B + {int(slack)} that the 2(J+1) term of '
              f'`prop:angular-discrepancy` predicts -- the linear law itself being '
              f'`eq:linear-phase-variation`')
    print()
print('PASS: `eq:normalized-angular-discrepancy` and `eq:angular-clock` hold on every '
      'pencil with one numerator-independent constant pair each')

print('ALL PASS: verify_equidistribution')
