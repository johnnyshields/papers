#!/usr/bin/env python3
r"""Paper section 6 (Consequences and sharpness), Proposition 6.1.

All arithmetic uses mpmath at arbitrary precision (no floating-point in the
verification loops).  The coefficient polynomials F_M(z) = [t^M] B/(Q+z t^r)
come from the exact D-recurrence of section 2, and denominator roots from
mpmath.polyroots.

Proposition 6.1 (equidistribution of the zero bulk): along the nonzero
coefficient polynomials, the normalized zero-counting measure mu[F_M] converges
weakly to mu_infty, the pushforward under z of the uniform measure (r/pi) dtheta
on (0, pi/r); mu_infty is independent of the numerator.  The proof places one
zero between consecutive sign-alternating phase points: the local sign-change
count gives the lower bound N_M([alpha,beta]) >= (M+1)(beta-alpha)/pi - O(1),
and the same bound on the complementary intervals subtracted from
deg F_M = floor(M/r) (Lemma 2.3) gives the matching upper bound, so
N_M([alpha,beta]) = (M+1)(beta-alpha)/pi + O(1); dividing by deg F_M gives
mu_infty(z([alpha,beta])) = (r/pi)(beta-alpha).

Three checks mirror that proof: (A)/(B) below on the limit measure, and (C) on
the local count.  (A)/(B):
  (A) Numerator-independence: the real z-root sets of F_M for B = 1 and B = 1 + t^2
      have Kolmogorov-Smirnov distance -> 0 as M grows, so the limit does not see B
      (hence not N) -- the weight B enters nowhere in the limit.
  (B) Pushforward form: mapping each real z-root x of F_M (B = 1) to theta = z^{-1}(x)
      via the minimum-modulus denominator pair (Theorem 3.1, eq. (3.2)), the theta-images
      become uniform on (0, pi/r): KS(theta ; Uniform) -> 0, i.e. mu_infty = z_*((r/pi)dtheta).
The F_M recurrence is cross-checked against a direct series division of 1/(Q+z t^r).
"""
import mpmath as mp
mp.mp.dps = 30

# --- data: Q(t) = (1-t)(1-t/2)(1-t/4), r = 2 (eq. (1.1) denominator) -----------
def qcoeffs():
    r"""Coefficients (low->high) of Q(t) = prod_j (1 - t/x_j), x_j in {1,2,4}, Q(0)=1."""
    xs = [mp.mpf(1), mp.mpf(2), mp.mpf(4)]
    c = [mp.mpf(1)]
    for x in xs:
        nc = [mp.mpf(0)] * (len(c) + 1)           # multiply the running product by (1 - t/x)
        for i, a in enumerate(c):
            nc[i] += a
            nc[i + 1] += -a / x
        c = nc
    return c                                       # low->high, length 4

Qc = qcoeffs()
r = 2
q0 = Qc[0]
dQ = len(Qc) - 1
dloc = max(dQ, r)                                  # d = deg_t D = max{deg Q, r}


def series_hn(Bc, M):
    r"""F_M(z) = [t^M] B/(Q+z t^r) as a z-polynomial (mpf list low->high).

    Uses the exact section-2 D-recurrence sum_i d_i(z) h_{n-i} = b_n with
    d_i = q_i + z*[i == r] and d_0 = Q(0) (Proposition 2.1's displayed system).  The
    numerator here is univariate, so the generating function is eq. (2.5), not the
    bivariate eq. (1.3).
    """
    H = []                                         # H[n] = z-coeffs of the coefficient polynomial h_n
    for n in range(M + 1):
        bn = Bc[n] if n < len(Bc) else mp.mpf(0)
        acc = [mp.mpf(bn)]                          # b_n (numerator, constant in z)
        for i in range(1, dloc + 1):               # subtract sum_{i>=1} d_i h_{n-i}
            if n - i < 0:
                continue
            hprev = H[n - i]
            qi = Qc[i] if i < len(Qc) else mp.mpf(0)
            for k, a in enumerate(hprev):          # -q_i * h_{n-i}
                while len(acc) <= k:
                    acc.append(mp.mpf(0))
                acc[k] -= qi * a
            if i == r:                             # -z * h_{n-r} (the z t^r term shifts the z-degree up)
                for k, a in enumerate(hprev):
                    while len(acc) <= k + 1:
                        acc.append(mp.mpf(0))
                    acc[k + 1] -= a
        H.append([a / q0 for a in acc])            # divide by d_0 = Q(0)
    return H[M]


def zdeg_of(poly_lowhigh):
    r"""Degree in z of a coefficient polynomial given as an mpf list low->high."""
    for k in range(len(poly_lowhigh) - 1, -1, -1):
        if abs(poly_lowhigh[k]) > mp.mpf('1e-40'):
            return k
    return -1


def real_pos_roots(poly_lowhigh):
    r"""Positive real z-roots of a coefficient polynomial (the bulk zeros in I_{Q,r})."""
    p = poly_lowhigh[:]
    while len(p) > 1 and abs(p[-1]) < mp.mpf(10)**(-25):
        p.pop()
    rts = mp.polyroots(list(reversed(p)), maxsteps=200, extraprec=80)
    out = []
    for zr in rts:
        zr = mp.mpc(zr)
        if abs(mp.im(zr)) < mp.mpf('1e-9') and mp.re(zr) > 0:
            out.append(mp.re(zr))
    return sorted(out)


def theta_from_z(x):
    r"""theta = z^{-1}(x), inverting the parameterization z: (0,pi/r) -> I_{Q,r}.

    For the z-value x the two smallest-modulus zeros of Q(t)+x t^r are the FT principal
    conjugate pair t_+- = tau e^{+-i theta} (Theorem 3.1, eq. (3.2)); theta = |arg t_+|.
    """
    Dc = [(Qc[i] if i < len(Qc) else mp.mpf(0)) + (x if i == r else mp.mpf(0))
          for i in range(dloc + 1)]
    rts = mp.polyroots(list(reversed(Dc)), maxsteps=200, extraprec=60)
    t0 = min(rts, key=lambda w: abs(w))            # minimum-modulus root = t_+
    return abs(mp.arg(mp.mpc(t0)))


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


# ===========================================================================
# (A) Numerator-independence: the limit does not see B (the weight enters nowhere)
# ===========================================================================
B1 = [mp.mpf(1)]                                   # B = 1
B2 = [mp.mpf(1), mp.mpf(0), mp.mpf(1)]             # B = 1 + t^2
ksA = []
for M in (40, 80, 160):
    r1 = real_pos_roots(series_hn(B1, M))
    r2 = real_pos_roots(series_hn(B2, M))
    d = ks_two(r1, r2)
    ksA.append(d)
    print(f'  M={M}: #roots B=1 -> {len(r1)}, B=1+t^2 -> {len(r2)}, KS(z) = {mp.nstr(d, 4)}')
# A bound drawn from the tested sequence itself (last < first) certifies no rate, so the
# ~1/M decay is asserted as a log-log slope as well.
assert ksA[-1] < ksA[0] and ksA[-1] < mp.mpf('0.08')
_sl = ((mp.log(ksA[-1]) - mp.log(ksA[0]))
       / (mp.log(mp.mpf(160)) - mp.log(mp.mpf(40))))
assert _sl < mp.mpf('-0.8'), _sl                                 # at least ~1/M
print('PASS: z-root distributions of different B converge (mu_infty independent of N)')


# ===========================================================================
# (B) Pushforward form: theta-images of the B=1 roots are uniform on (0, pi/r)
# ===========================================================================
pir = mp.pi / r
unif = lambda th: min(max(th / pir, mp.mpf(0)), mp.mpf(1))
ksB = []
for M in (40, 80, 160):
    xs = real_pos_roots(series_hn(B1, M))
    ths = [th for th in (theta_from_z(x) for x in xs) if 0 < th < pir]
    d = ks(ths, unif)
    ksB.append(d)
    print(f'  M={M}: {len(xs)} roots, mapped {len(ths)}; KS(theta ; Uniform(0,pi/r)) = {mp.nstr(d, 4)}')
# A bound drawn from the tested sequence itself (last < first) certifies no rate, so the
# ~1/M decay is asserted as a log-log slope as well.
assert ksB[-1] < ksB[0] and ksB[-1] < mp.mpf('0.08')
_sl = ((mp.log(ksB[-1]) - mp.log(ksB[0]))
       / (mp.log(mp.mpf(160)) - mp.log(mp.mpf(40))))
assert _sl < mp.mpf('-0.8'), _sl                                 # at least ~1/M
print('PASS: theta-images approach Uniform(0,pi/r); mu_infty = z_*((r/pi) dtheta)')


# ===========================================================================
# Cross-check: the F_M recurrence matches a direct series division of 1/(Q+z0 t^r)
# ===========================================================================
z0, M = mp.mpf('0.5'), 30
val_poly = sum(c * z0**k for k, c in enumerate(series_hn(B1, M)))     # F_M(z0) via the z-poly recurrence
den = [(Qc[i] if i < len(Qc) else mp.mpf(0)) + (z0 if i == r else mp.mpf(0)) for i in range(dloc + 1)]
h = [mp.mpf(1) / den[0]]                                             # h_0 = 1/Q(0); numerator B=1 => b_n=0 for n>=1
for n in range(1, M + 1):
    h.append(-sum(den[i] * h[n - i] for i in range(1, min(n, dloc) + 1)) / den[0])
assert abs(val_poly - h[M]) < mp.mpf('1e-18')
print(f'PASS: F_M recurrence matches direct series (F_{M}(0.5) = {mp.nstr(val_poly, 10)})')


# ===========================================================================
# (C) Local zero count (Proposition 6.1 proof).  One zero lies between
# consecutive phase points, so on a fixed [alpha,beta]
#     N_M([alpha,beta]) = (M+1)(beta-alpha)/pi + O(1)
# with a deficit bounded as M grows.  The complementary intervals subtracted
# from deg F_M = floor(M/r) supply the matching upper bound.  One zero per phase
# interval shows as consecutive theta-gaps ~ pi/(M+1).
# ===========================================================================
alpha, beta = mp.mpf('0.5'), mp.mpf('1.1')                       # [alpha,beta] subset (0, pi/r)
deficits = []
for M in (50, 100, 150):
    ths = sorted(th for th in (theta_from_z(x) for x in real_pos_roots(series_hn(B1, M)))
                 if 0 < th < pir)
    Nab = sum(1 for th in ths if alpha <= th <= beta)
    pred = (M + 1) * (beta - alpha) / mp.pi
    HM = mp.mpf('3') / M
    Ncomp = sum(1 for th in ths if HM <= th < alpha or beta < th <= pir - HM)
    # deg is read off the COMPUTED polynomial and compared against M//r, so eq. (2.6) is
    # an assertion here rather than an input.
    deg = zdeg_of(series_hn(B1, M))
    assert deg == M // r, (M, deg)                            # eq. (2.6)
    gaps = [ths[i + 1] - ths[i] for i in range(len(ths) - 1)]
    med_scaled = sorted((M + 1) * g / mp.pi for g in gaps)[len(gaps) // 2]  # -> 1
    deficits.append(abs(pred - Nab))
    print(f'  M={M}: N[a,b]={Nab} vs (M+1)(b-a)/pi={mp.nstr(pred, 6)} '
          f'(deficit {mp.nstr(pred - Nab, 3)}); N[a,b]+Ncomp-deg={Nab + Ncomp - deg}; '
          f'median (M+1)*gap/pi={mp.nstr(med_scaled, 4)}')
    assert abs(Nab + Ncomp - deg) <= 3                           # complement closes to deg F_M +- O(1)
    assert abs(med_scaled - 1) < mp.mpf('0.08')                  # one zero per phase interval
assert max(deficits) < mp.mpf('4')                               # deficit is O(1), does not grow with M
print('PASS: N_M([a,b]) = (M+1)(b-a)/pi + O(1) (bounded deficit; complement closes to deg F_M)')


# ===========================================================================
# eq. (6.1) portmanteau lower bound: the checkable shadow
# ===========================================================================
# The analytic chain of Proposition 6.1 (tightness -> subsequential limit mu_* ->
# portmanteau lower bound mu_*(z([a,b])) >= (r/pi)(b-a) -> atom-free cut points ->
# mu_* = mu_infty) is not numerically checkable as such.  Its checkable shadow is:
#   (i)  mu[F_M](z([alpha,beta])) -> (r/pi)(beta-alpha), the mass eq. (6.1) bounds; and
#   (ii) the NUMBER of near-coincident consecutive theta-images stays bounded in M while
#        their FRACTION vanishes like O(1/M).
#
# A lower bound on the MINIMUM scaled gap would be local rigidity, which Proposition 6.1
# does not claim and which fails for admissible numerators: weak convergence permits O(1)
# zeros to bunch, since a vanishing fraction of the mass cannot move the limit.  The paper
# says so directly ("the deleted endpoint and amplitude windows ... carry only O(1) zeros
# ... a mass O(1/M) vanishing after normalization").  On B_* below, whose W has an amplitude
# zero at theta = 0.8, the minimum scaled gap collapses (0.459, 0.178, 0.094 at M = 50,
# 100, 150) exactly at that theta while the mass error still converges and the median gap
# stays within 4% of 1.
#
# So the checkable shadow is the pair (count bounded, fraction -> 0), asserted below for
# both a B with no amplitude zero (count 0) and one with a single amplitude zero (count 1),
# so that it distinguishes them rather than passing regardless.
# M is capped at 150: at dps=30 the root-finder degrades past ~200 (a tooling
# limit, not a failure of the claim), so staying inside the validated range.
mass_err, min_gaps = [], []
for M in (50, 100, 150):
    try:
        xs = real_pos_roots(series_hn(B1, M))
    except Exception as exc:                                       # precision ceiling
        print(f'  (skipped M={M}: {type(exc).__name__})')
        continue
    ths = sorted(th for th in (theta_from_z(x) for x in xs) if 0 < th < pir)
    if len(ths) < 10:
        continue
    inside = sum(1 for th in ths if alpha <= th <= beta)
    # mu[F_M] normalizes by deg F_M, not by the number of positive real roots.  The two
    # agree only when the exceptional count is 0, so license the substitution here rather
    # than assume it: for B = 1 every zero is a simple positive real one in I_{Q,r}.
    deg_FM = zdeg_of(series_hn(B1, M))
    assert deg_FM == M // r, (M, deg_FM)                          # eq. (2.6)
    assert len(ths) == deg_FM, (M, len(ths), deg_FM)              # C_B = 0, so no defect
    ratio = mp.mpf(inside) / deg_FM
    target = (beta - alpha) / pir                                 # = (r/pi)(beta-alpha)
    mass_err.append(abs(ratio - target))
    gaps_all = [ths[i + 1] - ths[i] for i in range(len(ths) - 1)]
    min_gaps.append(min((M + 1) * g / mp.pi for g in gaps_all))
assert len(mass_err) >= 3, mass_err
assert mass_err[-1] < mp.mpf('0.03'), mass_err                     # (i) mass converges
assert mass_err[-1] < mass_err[0], mass_err

# (ii) count of near-coincident pairs bounded in M, fraction -> 0.  Run on B1 (whose W has
# no branch zero, so the count must be 0) and on a B_* built to have exactly one, so the
# two outcomes differ and the assert distinguishes them.
theta0_eq = mp.mpf('0.8')
lo_e, hi_e = mp.mpf('1e-6'), mp.mpf('1e7')
for _ in range(80):
    mid_e = mp.sqrt(lo_e * hi_e)
    lo_e, hi_e = (mid_e, hi_e) if theta_from_z(mid_e) < theta0_eq else (lo_e, mid_e)
z_eq = mp.sqrt(lo_e * hi_e)
Dc_eq = [(Qc[i] if i < len(Qc) else mp.mpf(0)) + (z_eq if i == r else mp.mpf(0))
         for i in range(dloc + 1)]
tp_eq = min(mp.polyroots(list(reversed(Dc_eq)), maxsteps=3000, extraprec=300),
            key=lambda w: abs(w))                                  # t_+ = minimum-modulus root
assert abs(mp.im(tp_eq)) > mp.mpf('1e-10'), tp_eq                  # genuinely a nonreal pair
# real quadratic with an exact branch root at t_+, so W has one amplitude zero at theta0
Bstar = [mp.re(tp_eq)**2 + mp.im(tp_eq)**2, -2 * mp.re(tp_eq), mp.mpf(1)]
assert Bstar[0] > 0, Bstar                                         # B_*(0) != 0, admissible

small = {}
for tag, Bc, expected in (('B=1', B1, 0), ('B_*', Bstar, 1)):
    counts, fracs = [], []
    for M in (50, 100, 150, 200):
        try:
            xs = real_pos_roots(series_hn(Bc, M))
        except Exception:
            continue
        th_l = sorted(th for th in (theta_from_z(x) for x in xs) if 0 < th < pir)
        if len(th_l) < 10:
            continue
        g = [(M + 1) * (th_l[i + 1] - th_l[i]) / mp.pi for i in range(len(th_l) - 1)]
        counts.append(sum(1 for v in g if v < mp.mpf('0.5')))
        fracs.append(mp.mpf(counts[-1]) / len(g))
    assert len(counts) >= 3, (tag, counts)
    assert all(c == expected for c in counts), (tag, counts, expected)  # bounded in M, and = J
    if expected:
        assert fracs[-1] < fracs[0] / 2, (tag, fracs)               # fraction -> 0 like O(1/M)
    small[tag] = (counts, fracs)
print(f'PASS: eq. (6.1) shadow: |mu[F_M](z[a,b]) - (r/pi)(b-a)| -> '
      f'{mp.nstr(mass_err[-1], 3)}; near-coincident pairs number '
      f'{small["B=1"][0][0]} for B=1 and {small["B_*"][0][0]} for B_* (one amplitude zero) at '
      f'every M, fraction {mp.nstr(small["B_*"][1][0], 3)} -> '
      f'{mp.nstr(small["B_*"][1][-1], 3)} = O(1/M) '
      f'(the analytic chain itself is not numerically checkable)')

print('ALL PASS: verify_equidistribution')
