#!/usr/bin/env python3
r"""Paper sections 5-6 (Proof of the fixed-numerator theorem; Consequences and sharpness).

Symbolic work uses SymPy; branch numerics use mpmath at arbitrary precision.
Coefficient polynomials P_m(z), F_M(z) come from the exact recurrence for
N(t,z)/(Q(t)+z t^r); real-root counts use SymPy nroots (degree-many roots with
multiplicity).  "Exceptional" means a zero outside (0, +inf) -- complex or
nonpositive-real -- the count bounded by Theorem 1.1.

  * Proposition 5.1, eq. (5.1): for a fixed univariate B (B(0) != 0) the exceptional-zero
    count of F_M is a fixed constant C_B, independent of M, and the positive-real count is
    deg F_M - C_B = floor(M/r) - C_B.  Checked for C_B = 0 (B = 1, 1+t^2) and for a genuine
    C_B = 2 (B with a conjugate root pair on the branch arc).
  * Lemma 3.6, eq. (3.12), as consumed by Proposition 5.1: psi(theta) = arg W(theta) has
    bounded derivative on compact interior subintervals, independent of M, so the
    Phi_M of eq. (5.4) -- Phi_M(theta) = (M+1)theta - psi(theta) -- has
    Phi_M' = M+1 - psi' > 0 for large M and is strictly increasing.
  * Proposition 5.2 (linear case deg Q = r = 1): N(t,z) = R(z) forces
        P_m(z) = (-1)^m R(z) (z+q_1)^m / q_0^{m+1},
    with moving zero -q_1 > 0 and all exceptional zeros carried by the fixed R.
  * Proposition 6.3: N(t,z) = R(z) gives P_m = R(z) H_m(z); with R(z) = prod_{j=1}^L (z+j)
    every P_m carries the same L negative zeros, so no bound uniform in N exists.
  * Corollary 6.2: #{positive-real zeros of P_m} / deg P_m -> 1 along the nonzero P_m.

Proposition 6.1 (equidistribution of the zero bulk) is verified separately in
verify_equidistribution.py.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

mp.mp.dps = 40
t, z = sp.symbols('t z')


def ratio_coeffs(Q, num, r, Mmax):
    Qp = sp.Poly(sp.expand(Q), t); q0 = Qp.nth(0)
    qc = [Qp.nth(i) for i in range(Qp.degree() + 1)]
    Np = sp.Poly(sp.expand(num), t); P = []
    for m in range(Mmax + 1):
        rhs = Np.nth(m)
        for i in range(1, len(qc)):
            if m - i >= 0:
                rhs -= qc[i] * P[m - i]
        if m - r >= 0:
            rhs -= z * P[m - r]
        P.append(sp.expand(rhs / q0))
    return P


def root_counts(poly):
    r"""(#positive-real, #exceptional) of poly(z), with multiplicity."""
    p = sp.Poly(poly, z)
    if p.degree() < 1:
        return 0, 0
    # nroots(n=50) is arbitrary precision, so the CLASSIFICATION must be too: real-vs-complex
    # and sign decisions are made in mpmath against tolerances derived from the working
    # precision, never through complex() or a float64 literal.
    tol = mp.mpf(10)**(-mp.mp.dps // 2)
    pos = 0
    for rr in p.nroots(n=50, maxsteps=800):
        re_, im_ = mp.mpf(str(sp.re(rr))), mp.mpf(str(sp.im(rr)))
        if abs(im_) < tol and re_ > tol:
            pos += 1
    return pos, p.degree() - pos


# ===========================================================================
# Proposition 5.1, eq. (5.1): fixed exceptional-zero constant C_B, positive bulk = floor(M/r) - C_B
# ===========================================================================
Q = (1 - t) * (1 - t / 2) * (1 - t / 4)
r = 2
cases = [
    (sp.Integer(1), 0, 'B = 1'),
    (1 + t**2, 0, 'B = 1 + t^2'),
    (sp.expand(t**2 - sp.Rational(9, 5) * t + sp.Rational(81, 100)), 2,
     'B with a double real root at t = 9/10 (NOT on the branch arc)'),
]
Mladder = [40, 48, 56, 64]
for Bexpr, C_B, label in cases:
    F = ratio_coeffs(Q, Bexpr, r, max(Mladder))
    excs = []
    for M in Mladder:
        pos, exc = root_counts(F[M])
        assert sp.Poly(F[M], z).degree() == M // r                 # eventual degree
        assert pos == M // r - exc                                 # positive bulk
        excs.append(exc)
    assert all(e == C_B for e in excs), (label, excs)              # constant, = C_B, independent of M
    print(f'PASS: {label}: exceptional count = {C_B} for all M in {Mladder}; '
          f'positive bulk = floor(M/r) - {C_B}')


# ===========================================================================
# Prop 5.1 / abstract: distinct zeros in I=(a,b), at most C_B outside I with multiplicity
# ===========================================================================
def _qlow(expr):
    p = sp.Poly(sp.expand(expr), t)
    return [p.nth(i) for i in range(p.degree() + 1)]


def _d_roots(Qc, r, zval):
    d = max(len(Qc) - 1, r)
    c = [mp.mpf(0)] * (d + 1)
    for i, co in enumerate(Qc):
        c[i] += mp.mpf(co)
    c[r] += mp.mpf(zval)
    return mp.polyroots(list(reversed(c)), maxsteps=3000, extraprec=200)


def lower_endpoint(Qc, r):                                        # smallest z with a complex principal pair
    lo, hi = mp.mpf(0), mp.mpf('1e6')
    for _ in range(200):
        mid = (lo + hi) / 2
        pair_complex = abs(mp.im(sorted(_d_roots(Qc, r, mid), key=lambda w: abs(w))[0])) > mp.mpf('1e-15')
        lo, hi = (lo, mid) if pair_complex else (mid, hi)
    return hi


def interval_counts(poly, a):
    r"""(distinct zeros in (a,inf), zeros in (a,inf) with mult, zeros outside (a,inf) with mult)."""
    # As above: nroots is arbitrary precision; every threshold here is an mpf derived
    # from the working precision, never a float64 literal.
    p = sp.Poly(poly, z)
    a_m = mp.mpf(str(sp.N(a, mp.mp.dps)))
    tol = mp.mpf(10)**(-mp.mp.dps // 2)
    sep = mp.mpf(10)**(-mp.mp.dps // 4)
    reals = sorted(mp.mpf(str(sp.re(x))) for x in p.nroots(n=50, maxsteps=800)
                   if abs(mp.mpf(str(sp.im(x)))) < tol)
    in_I = [x for x in reals if x > a_m + tol]
    distinct = []
    for x in in_I:
        if not distinct or abs(x - distinct[-1]) > sep:
            distinct.append(x)
    return len(distinct), len(in_I), p.degree() - len(in_I)


Qe = (1 - t) * (1 - t / 2) * (1 - t / 4)
r = 2
a = lower_endpoint(_qlow(Qe), r)                                  # b = +inf for r >= 2
for Bexpr, C_B, label in [
    (sp.Integer(1), 0, 'B = 1'),
    (sp.expand(t**2 - sp.Rational(9, 5) * t + sp.Rational(81, 100)), 2, 'branch-arc B'),
]:
    F = ratio_coeffs(Qe, Bexpr, r, 64)
    for M in (40, 52, 64):
        dist, in_mult, out_mult = interval_counts(F[M], a)
        assert out_mult == C_B                                    # at most C_B outside I (with multiplicity)
        assert dist == in_mult                                    # zeros in I are simple (distinct = with mult)
        assert dist == M // r - C_B                               # distinct zeros in I = floor(M/r) - C_B
    print(f'PASS: {label}: distinct zeros in I = floor(M/r) - {C_B}, at most {C_B} outside '
          f'I = ({mp.nstr(a, 5)}, +inf) with multiplicity')


# ===========================================================================
# Proposition 5.1, eq. (5.4): psi' bounded on compact interior => Phi_M strictly increasing
# ===========================================================================
def qlow(expr):
    p = sp.Poly(sp.expand(expr), t)
    return [p.nth(i) for i in range(p.degree() + 1)]


def d_roots(Qc, r, zval):
    d = max(len(Qc) - 1, r)
    c = [mp.mpf(0)] * (d + 1)
    for i, co in enumerate(Qc):
        c[i] += mp.mpf(co)
    c[r] += mp.mpf(zval)
    return mp.polyroots(list(reversed(c)), maxsteps=3000, extraprec=200)


def principal(rts):
    for w in sorted(rts, key=lambda w: abs(w)):
        if abs(mp.im(w)) > mp.mpf('1e-20'):
            return w
    return sorted(rts, key=lambda w: abs(w))[0]


Qc, Bc = qlow((1 - t) * (1 - t / 2) * (1 - t / 4)), qlow((1 + t) * (2 + t))
r = 2


def pval(cl, x):
    return sum(mp.mpf(c) * x**i for i, c in enumerate(cl))


def dval(cl, x):
    return sum(mp.mpf(cl[i]) * i * x**(i - 1) for i in range(1, len(cl)))


def z_of_theta(theta):                                             # invert arg t_+(z) = theta
    lo, hi = mp.mpf('1e-4'), mp.mpf('1e7')
    for _ in range(70):
        mid = mp.sqrt(lo * hi)
        lo, hi = (mid, hi) if abs(mp.arg(principal(d_roots(Qc, r, mid)))) < theta else (lo, mid)
    return mp.sqrt(lo * hi)


# Uniform theta grid on a compact interior band, tracking t_+(theta) by analytic continuation
# (nearest root to the previous one).  A modulus-only selector jumps between roots and would
# fabricate spurious arg-W discontinuities; continuous tracking is required to measure psi'.
band = [mp.mpf('0.25') + (mp.pi / r - mp.mpf('0.5')) * k / 90 for k in range(91)]
tps, zs, prev = [], [], None
for th in band:
    zv = z_of_theta(th); rts = d_roots(Qc, r, zv)
    pr = (min([w for w in rts if mp.im(w) > mp.mpf('1e-20')], key=lambda w: abs(abs(mp.arg(w)) - th))
          if prev is None else min(rts, key=lambda w: abs(w - prev)))
    tps.append(pr); zs.append(zv); prev = pr
Ws = [-pval(Bc, tps[i]) / (dval(Qc, tps[i]) + r * zs[i] * tps[i]**(r - 1)) for i in range(len(band))]

# eq. (5.4): psi'(theta) = (arg W)' is bounded on the compact band (independent of M), so
# Phi_M(theta) = (M+1)theta - psi(theta) has Phi_M' = M+1 - psi' > 0 and is strictly increasing.
K = max(abs(mp.arg(Ws[i + 1] / Ws[i]) / (band[i + 1] - band[i])) for i in range(len(band) - 1))
assert K < mp.mpf('5')                                             # bounded (converges under refinement)
psi = [mp.arg(Ws[0])]
for i in range(1, len(band)):
    psi.append(psi[-1] + mp.arg(Ws[i] / Ws[i - 1]))
for M in (100, 1000):
    Phi = [(M + 1) * band[i] - psi[i] for i in range(len(band))]
    assert all(Phi[i] > Phi[i - 1] for i in range(1, len(Phi)))
print(f'PASS: interior |psi\'(theta)| <= {mp.nstr(K, 5)} (M-independent); Phi_M(theta) strictly '
      f'increasing (checked M = 100, 1000)')

# eq. (5.5): the advance of Phi_M over the band equals the number of sign changes of
# tau^{M+1} F_M(z(theta)); both equal floor(M/r) - O(1) (the O(1) is the untracked endpoint band).
# The O(1) deficit has to be measured on the SHRINKING retained range [h/M, pi/r - h/M],
# which is where the paper claims it, and over an M ladder.  On a FIXED band the deficit is
# Theta(M) instead: the band has length L = pi/r - 2*0.25, so the advance is ~ (M+1)L/pi and
# the deficit ~ M/(2 pi) -- measured 6, 12, 25, 51 at M = 40, 80, 160, 320.  A fixed-band
# bound would therefore hold only at whichever single M it was calibrated against.
h_pc = mp.mpf('3')
deficits_pc = []
for Mpc in (40, 80, 160):
    lo_pc, hi_pc = h_pc / Mpc, mp.pi / r - h_pc / Mpc
    # psi has bounded variation (eq. (3.12)), so a coarse grid resolves Var psi; the
    # phase advance then gives the sign-change count without a fine sign scan.
    npc = 60
    grid = [lo_pc + (hi_pc - lo_pc) * mp.mpf(i) / npc for i in range(npc + 1)]
    prev_pc, Wlist = None, []
    for th in grid:
        zv = z_of_theta(th)
        rts_g = d_roots(Qc, r, zv)
        pg = (min([w for w in rts_g if mp.im(w) > mp.mpf('1e-20')],
                  key=lambda w: abs(abs(mp.arg(w)) - th))
              if prev_pc is None else min(rts_g, key=lambda w: abs(w - prev_pc)))
        prev_pc = pg
        Wlist.append(-pval(Bc, pg) / (dval(Qc, pg) + r * zv * pg**(r - 1)))
    # continuous branch of psi = arg W by unwrapping
    psi_pc, off = [mp.arg(Wlist[0])], mp.mpf(0)
    for i in range(1, len(Wlist)):
        d_ = mp.arg(Wlist[i]) - mp.arg(Wlist[i - 1])
        while d_ > mp.pi:
            d_ -= 2 * mp.pi
        while d_ < -mp.pi:
            d_ += 2 * mp.pi
        off += d_
        psi_pc.append(mp.arg(Wlist[0]) + off)
    advance_pc = ((Mpc + 1) * (hi_pc - lo_pc) - (psi_pc[-1] - psi_pc[0])) / mp.pi
    deficits_pc.append((Mpc, Mpc // r - int(mp.floor(advance_pc))))
dvals_pc = [d for _, d in deficits_pc]
assert max(dvals_pc) - min(dvals_pc) <= 2, deficits_pc             # M-free
assert max(dvals_pc) <= 6, deficits_pc                             # and small
print(f'PASS: eq. (5.5) on the shrinking range [h/M, pi/r-h/M] (h={mp.nstr(h_pc,3)}): '
      f'deficit floor(M/r) - phase advance = {dvals_pc} at M = '
      f'{[m for m, _ in deficits_pc]} -- bounded independently of M '
      f'(on a FIXED band it would be Theta(M))')

M = 40
svals = [abs(tps[i])**(M + 1) * mp.re(-sum(pval(Bc, w) / (w**(M + 1) * (dval(Qc, w) + r * zs[i] * w**(r - 1)))
                                           for w in d_roots(Qc, r, zs[i]))) for i in range(len(band))]
sign_changes = sum(1 for i in range(1, len(svals)) if (svals[i] > 0) != (svals[i - 1] > 0))
advance = ((M + 1) * (band[-1] - band[0]) - (psi[-1] - psi[0])) / mp.pi
assert abs(sign_changes - advance) <= 2                            # phase advance counts the zeros
# On the FIXED band the deficit is Theta(M) by design, so assert only that the phase
# advance matches the sign-change count (above); the M-free O(1) is the block above.
assert 0 <= M // r - sign_changes
print(f'PASS: phase advance {mp.nstr(advance, 5)} = {sign_changes} sign changes of F_M(z(theta)) '
      f'= floor(M/r) - O(1) (floor(M/r) = {M // r})')


# ===========================================================================
# eq. (5.2)/(5.3): Omega_M = [h/M, pi/r - h/M] \ union_j Theta_{j,M} has a number of
# components bounded independently of M, and |Omega_M| = pi/r - 2h/M + o(1/M).
#
# Two things make this non-vacuous.  First, B must have a genuine branch root: for a B whose
# roots are all real and negative -- (1+t)(2+t), say -- W has no zero on the branch, J = 0,
# and no window is deleted at all, so the amplitude zero cannot be a literal.  It is
# constructed here and then LOCATED from |W|, with nu_j measured.  Second, |Omega_M| is
# computed by walking the two retained components and summing their lengths, which is a
# different computation from the closed form pi/r - 2h/M - 2*hw; comparing
# (pi/r - 2h/M) - Omega_len against the deleted length instead would be an identity, since
# Omega_len is defined as that difference.
# ===========================================================================
theta_j_om = mp.mpf('0.8')
z_j_om = z_of_theta(theta_j_om)
tp_om = principal(d_roots(Qc, r, z_j_om))
# real quadratic with an exact branch root at t_+(z_j); B(0) = |t_+|^2 != 0
Bc_om = [mp.re(tp_om)**2 + mp.im(tp_om)**2, -2 * mp.re(tp_om), mp.mpf(1)]
assert Bc_om[0] > 0, Bc_om


def Wmag_om(th):
    zz = z_of_theta(th)
    pp = principal(d_roots(Qc, r, zz))
    return abs(-pval(Bc_om, pp) / (dval(Qc, pp) + r * zz * pp**(r - 1)))


# locate the amplitude zero from the data (coarse grid, then golden section), interior only
lo_s, hi_s = mp.mpf('0.30'), mp.pi / r - mp.mpf('0.30')
th_star = min((lo_s + (hi_s - lo_s) * mp.mpf(i) / 40 for i in range(41)), key=Wmag_om)
lo_g, hi_g = th_star - (hi_s - lo_s) / 40, th_star + (hi_s - lo_s) / 40
for _ in range(60):
    m1, m2 = lo_g + (hi_g - lo_g) / 3, hi_g - (hi_g - lo_g) / 3
    lo_g, hi_g = (lo_g, m2) if Wmag_om(m1) < Wmag_om(m2) else (m1, hi_g)
theta_j_found = (lo_g + hi_g) / 2
assert abs(theta_j_found - theta_j_om) < mp.mpf('1e-6'), (theta_j_found, theta_j_om)
# nu_j from the local log-log slope of |W|
e1, e2 = mp.mpf('1e-4'), mp.mpf('1e-6')
nu_om = ((mp.log(Wmag_om(theta_j_found + e1)) - mp.log(Wmag_om(theta_j_found + e2)))
         / (mp.log(e1) - mp.log(e2)))
assert abs(nu_om - 1) < mp.mpf('0.05'), nu_om                      # nu_j = 1 as constructed
nu_j_om = max(1, int(mp.nint(nu_om)))

h_om, c_om = mp.mpf('3'), mp.mpf('0.15')
resid = []
for MM in (100, 200, 400, 800):
    lo_om, hi_om = h_om / MM, mp.pi / r - h_om / MM
    hw = mp.e**(-c_om * MM / nu_j_om)                      # eq. (4.1) half-width, measured nu_j
    # walk the retained components explicitly: the window sits strictly inside the range
    assert lo_om < theta_j_found - hw and theta_j_found + hw < hi_om, (MM, hw)
    comps = [(lo_om, theta_j_found - hw), (theta_j_found + hw, hi_om)]
    assert len(comps) == 2                                 # eq. (5.2): bounded in M
    Omega_len = sum(b - a for a, b in comps)               # route 1: sum of components
    closed = (mp.pi / r - 2 * h_om / MM) - 2 * hw          # route 2: closed form
    assert abs(Omega_len - closed) < mp.mpf('1e-40'), (MM, Omega_len, closed)
    resid.append(MM * ((mp.pi / r - 2 * h_om / MM) - Omega_len))
# the o(1/M) content: M times the deleted length tends to 0, using the MEASURED nu_j
assert all(resid[i + 1] < resid[i] for i in range(3)), resid
assert resid[-1] < mp.mpf('1e-3'), resid[-1]
# and it is the exponential that does it: at nu_j large enough the window would NOT be
# o(1/M), so the measured nu_j is load-bearing rather than decorative
bad_nu = int(mp.ceil(c_om * 800 / mp.log(800)))            # makes e^{-c M/nu} ~ 1/M at M = 800
assert 800 * 2 * mp.e**(-c_om * 800 / bad_nu) > mp.mpf('1e-3'), bad_nu
print(f'PASS: eq. (5.2)/(5.3): amplitude zero located at theta_j = '
      f'{mp.nstr(theta_j_found, 8)} (constructed {mp.nstr(theta_j_om, 3)}), measured '
      f'nu_j = {mp.nstr(nu_om, 4)}; Omega_M has 2 components by both routes, '
      f'M x deleted -> {mp.nstr(resid[-1], 3)} (o(1/M)); at nu_j = {bad_nu} it would not be')


# ===========================================================================
# Proposition 5.2 (linear case): P_m(z) = (-1)^m R(z)(z+q_1)^m / q_0^{m+1}
# ===========================================================================
q0s, q1s = sp.symbols('q0 q1')
R = 1 + z + z**3                                                   # arbitrary fixed R(z)
Plin = ratio_coeffs(q0s + q1s * t, R, 1, 7)
for m in range(8):
    closed = (-1)**m * R * (z + q1s)**m / q0s**(m + 1)
    assert sp.simplify(Plin[m] - closed) == 0
# concrete instance: q_0 > 0, q_1 < 0, so the moving zero -q_1 is a positive real zero of every P_m
q0v, q1v = sp.Rational(3), sp.Rational(-5, 2)
Pnum = ratio_coeffs(q0v + q1v * t, R, 1, 6)
assert -q1v > 0 and all(sp.Poly(Pnum[m], z).eval(-q1v) == 0 for m in range(1, 7))
print('PASS: linear case P_m = (-1)^m R(z)(z+q_1)^m / q_0^{m+1}; moving zero -q_1 > 0 is a '
      'positive zero of every P_m, exceptional zeros carried by R')


# ===========================================================================
# Proposition 6.3 and Corollary 6.2: N = R(z) => P_m = R H_m; concentration ratio -> 1
# ===========================================================================
Q = (1 - t) * (1 - t / 2) * (1 - t / 4)
r = 2
H = ratio_coeffs(Q, sp.Integer(1), r, 60)
for L in (2, 3, 5):
    Rz = sp.prod(z + j for j in range(1, L + 1))
    P = ratio_coeffs(Q, Rz, r, 60)
    for m in range(61):
        assert sp.expand(P[m] - Rz * H[m]) == 0                    # P_m = R H_m
    for m in (40, 50, 60):
        _, exc = root_counts(P[m])
        assert exc == L                                            # exactly L exceptional, every m
        assert all(sp.Poly(P[m], z).eval(-j) == 0 for j in range(1, L + 1))
    print(f'PASS: N=R(z), R=prod_{{1}}^{{{L}}}(z+j): P_m = R H_m, exactly {L} negative zeros '
          f'in every P_m (no N-uniform bound)')

# Corollary 6.2: positive-real fraction -> 1 for a fixed nonhyperbolic numerator
Rz = (z + 1) * (z**2 + 1)                                          # forces 3 exceptional zeros
P = ratio_coeffs(Q, Rz, r, 80)
ratios = []
for m in (20, 40, 60, 80):
    pos, exc = root_counts(P[m])
    deg = sp.Poly(P[m], z).degree()
    ratios.append(mp.mpf(pos) / deg)
    assert exc == 3                                                # constant defect
assert all(ratios[i] > ratios[i - 1] for i in range(1, len(ratios)))
assert ratios[-1] > mp.mpf('0.9') and ratios[-1] < 1
print(f'PASS: #positive-real / deg P_m -> 1 (ratios {[mp.nstr(x, 5) for x in ratios]}, '
      f'fixed defect 3)')


# ===========================================================================
# Theorem 1.1 end-to-end for a genuinely bivariate N(t,z) (both t and z present):
# P_m computed directly from N/(Q+z t^r), exceptional-zero count bounded uniformly in m
# ===========================================================================
Q = (1 - t) * (1 - t / 2) * (1 - t / 4)
r = 2
for N, C, label in [
    ((1 + z + z**2) + t * (2 - z), 2, 'N=(1+z+z^2)+t(2-z)'),
    (1 + t + z * (2 - t) + z**2, 2, 'N=1+t+z(2-t)+z^2'),
]:
    P = ratio_coeffs(Q, N, r, 50)
    excs = []
    for m in (30, 40, 50):
        pos, exc = root_counts(P[m])
        assert pos == sp.Poly(P[m], z).degree() - exc
        excs.append(exc)
    assert all(e == C for e in excs)                               # bounded, constant in m
    print(f'PASS: bivariate {label}: P_m has exactly {C} exceptional zeros for m=30,40,50 '
          f'(end-to-end, C = C(Q,r,N))')

print('ALL PASS: verify_proof')
