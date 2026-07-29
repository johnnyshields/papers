#!/usr/bin/env python3
r"""Paper section 2 (Laurent reduction and eventual degree).

Everything is re-derived from the generating function
        N(t,z)/(Q(t)+z t^r) = sum_{m>=0} P_m(z) t^m
via the exact coefficient recurrence, so the identities are pinned to the
objects that define them rather than transcribed.

Exact symbolic certificates (sympy):
  * Proposition 2.1: N |-> (P_0,...,P_{d-1}) is the lower-triangular system with
    constant diagonal d_0 = Q(0); it is a bijection onto R[z]^d.
  * Lemma 2.2 (Laurent-Gauss reduction): A(t) = t^{rE} N(t,-Q/t^r) is a polynomial,
    eq. (2.1); the division identity N = D S + t^{-rE} A, eq. (2.2); and the reduced
    coefficient formula P_m(z) = [t^{m+rE-mu}] B/D, eq. (2.3), with A = t^mu B and
    B(0) != 0.  The mechanism A = 0 <=> D | N is exhibited on N = D.
  * eq. (2.4): P_m = sum_j b_j H_{m+rE-mu-j}, a fixed finite linear combination of the
    denominator-only sequence H_m of eq. (1.2).
  * Lemma 2.3 (eventual degree): deg F_M = floor(M/r), eq. (2.6).  The z^ell coefficient
    eq. (2.9) is Q(0)^{-(ell+1)} times a polynomial in ell of degree <= s with leading
    coefficient B(0) lambda^s / s! != 0, lambda = -Q'(0)/Q(0), so the top degree is attained.
  * Remark 2.4: deg P_m = m/r + O(1) after the fixed index shift M = m + rE - mu.
  * Scope: max{deg Q, r} > 1 is load-bearing.  At deg Q = r = 1 the eventual degree
    still holds, but I_{Q,r} does not exist and Proposition 5.1's count fails for every
    fixed C_B -- exhibited at the end of this file.
"""
from __future__ import annotations
import sympy as sp

t, z, ell = sp.symbols('t z ell')


def ratio_coeffs(Q, num, r, Mmax):
    r"""[t^0..t^Mmax] of num/(Q + z t^r) as sympy expressions in z (Poincare recurrence).

    The coefficient recurrence of the generating function eq. (1.3),
    num = (Q + z t^r) * sum_m P_m t^m, solved for P_m using only Q(0) != 0
    (Proposition 2.1).  This is the workhorse behind every section-2 identity below.
    """
    Qp = sp.Poly(sp.expand(Q), t)
    q0 = Qp.nth(0)
    assert q0 != 0, 'Q(0) must be nonzero'
    qc = [Qp.nth(i) for i in range(Qp.degree() + 1)]
    Np = sp.Poly(sp.expand(num), t)
    P = []
    for m in range(Mmax + 1):
        rhs = Np.nth(m)
        for i in range(1, len(qc)):
            if m - i >= 0:
                rhs -= qc[i] * P[m - i]
        if m - r >= 0:
            rhs -= z * P[m - r]
        P.append(sp.expand(rhs / q0))
    return P


def zdeg(expr):
    p = sp.Poly(sp.expand(expr), z)
    return -1 if p.is_zero else p.degree()


# ===========================================================================
# Proposition 2.1: numerator <-> initial data is a bijection (triangular solve)
# ===========================================================================
# Generic proper numerator over R[z]: Q of degree 2, r = 3, so d = max(deg Q, r) = 3.
# The map (P_0,P_1,P_2) |-> (N_0,N_1,N_2) is lower triangular with diagonal d_0 = Q(0).
q0s, q1s, q2s = sp.symbols('q0 q1 q2')
Qg = q0s + q1s * t + q2s * t**2
rg = 3
d = max(sp.Poly(Qg, t).degree(), rg)
assert d == 3
Dg = Qg + z * t**rg
dj = [sp.Poly(sp.expand(Dg), t).nth(j) for j in range(d)]      # d_0,d_1,d_2 (z enters only at j=r=3)
assert dj[0] == q0s
Pg = list(sp.symbols('P0 P1 P2'))
Ng = [sum(dj[j] * Pg[m - j] for j in range(m + 1)) for m in range(d)]
L = sp.Matrix(d, d, lambda i, j: dj[i - j] if i >= j else 0)
assert sp.simplify(sp.Matrix(Ng) - L * sp.Matrix(Pg)) == sp.zeros(d, 1)
assert L.det() == q0s**d                                          # det is q0^d
assert sp.Poly(L.det(), z).degree() == 0                          # z-free, so a unit of R[z]
assert sp.simplify(sp.Matrix(Pg) - L.inv() * sp.Matrix(Ng)) == sp.zeros(d, 1)
print('PASS: N -> (P_0,...,P_{d-1}) is triangular with diagonal Q(0); bijection onto R[z]^d')

# The case r < d, where z genuinely enters the system.  Above, r = 3 = d put the
# z-carrying coefficient d_r outside the indices 0..d-1, so L was z-free and
# "invertible over R[z]" was checked where R[z] plays no role.  Take deg Q = 3,
# r = 2: then d = 3 and d_2 = q_2 + z, so L and L^{-1} genuinely carry z.
q3s = sp.Symbol('q3')
Qg2 = q0s + q1s * t + q2s * t**2 + q3s * t**3
rg2 = 2
d2 = max(sp.Poly(Qg2, t).degree(), rg2)
assert d2 == 3 and rg2 < d2
dj2 = [sp.Poly(sp.expand(Qg2 + z * t**rg2), t).nth(j) for j in range(d2)]
assert dj2[0] == q0s and dj2[2] == q2s + z                        # z enters at j = r = 2
L2 = sp.Matrix(d2, d2, lambda i, j: dj2[i - j] if i >= j else 0)
assert sp.Poly(sp.expand(L2.det()), z).degree() == 0              # det still z-free
assert sp.expand(L2.det()) == q0s**d2
Ng2 = [sum(dj2[j] * Pg[m - j] for j in range(m + 1)) for m in range(d2)]
assert sp.simplify(sp.Matrix(Ng2) - L2 * sp.Matrix(Pg)) == sp.zeros(d2, 1)
assert sp.simplify(sp.Matrix(Pg) - L2.inv() * sp.Matrix(Ng2)) == sp.zeros(d2, 1)
Linv2 = sp.simplify(L2.inv())
assert any(sp.Poly(sp.expand(e), z).degree() > 0 for e in Linv2)   # L^{-1} really carries z
print('PASS: r < d case (deg Q=3, r=2): d_r = q_2 + z enters L, L^{-1} carries z, '
      'det = Q(0)^d still a unit of R[z]')

# Cross-check against the series recurrence on a concrete proper numerator.
Qc = sp.expand((1 - t) * (1 - 2 * t))
Nc = (1 + z + z**2) + t * (2 - z)
P = ratio_coeffs(Qc, Nc, 2, 6)
dc = max(sp.Poly(Qc, t).degree(), 2)
for m in range(dc):
    lhs = sum(sp.Poly(sp.expand(Qc + z * t**2), t).nth(j) * P[m - j] for j in range(m + 1))
    assert sp.expand(lhs - sp.Poly(Nc, t).nth(m)) == 0
for m in range(dc, 7):                                           # homogeneous tail
    lhs = sum(sp.Poly(sp.expand(Qc + z * t**2), t).nth(j) * P[m - j]
              for j in range(min(m, dc) + 1))
    assert sp.expand(lhs) == 0
print('PASS: coefficient recurrence reproduces the initial-data system and its tail')


# ===========================================================================
# Lemma 2.2: Laurent-Gauss reduction  N = D S + t^{-rE} A,  P_m = [t^{m+rE-mu}] B/D
# ===========================================================================
def laurent_reduce(Q, N, r):
    E = sp.Poly(sp.expand(N), z).degree()
    A = sp.expand(sp.cancel(t**(r * E) * N.subs(z, -Q / t**r)))
    Ap = sp.Poly(A, t)
    assert all(e >= 0 for (e,), _ in Ap.terms()), 'A must be an ordinary polynomial'   # eq. (2.1)
    assert A != 0
    mu = min(e for (e,), _ in Ap.terms())
    B = sp.expand(sp.cancel(A / t**mu))
    assert sp.Poly(B, t).nth(0) != 0
    return E, A, mu, B


def max_t_exp(expr):
    r"""Largest power of t in a (possibly Laurent) polynomial in t over R[z]."""
    exps = []
    for term in sp.Add.make_args(sp.expand(expr)):
        _, tt = term.as_independent(t)
        exps.append(0 if tt == 1 else int(tt.as_base_exp()[1]))
    return max(exps)


Qc = sp.expand((1 - t) * (1 - 2 * t))
Nc = (1 + z + z**2) + t * (2 - z)
r = 2
D = Qc + z * t**r
E, A, mu, B = laurent_reduce(Qc, Nc, r)

S = sp.cancel((Nc - t**(-r * E) * A) / D)
assert sp.cancel(Nc - (D * S + t**(-r * E) * A)) == 0            # eq. (2.2)
# S in R[t,t^{-1},z] is the substantive half of eq. (2.2): assert it directly by
# checking the denominator of S is a pure t-monomial (a unit of R[t,t^{-1}]).
Sden = sp.denom(sp.cancel(sp.together(S)))
assert sp.simplify(Sden / t**sp.degree(sp.Poly(Sden, t), t)).is_number, Sden
assert sp.Poly(Sden, z).degree() == 0, Sden                      # no z in the denominator
cutoff = max_t_exp(S)
print(f'PASS: A(t) = t^(rE) N(t,-Q/t^r) polynomial, A = t^{mu} B with B(0) = {sp.Poly(B, t).nth(0)}')
print(f'PASS: N = D S + t^(-rE) A holds (Laurent correction S has top t-exponent {cutoff})')

# Question 7.1: deg A <= deg_t N + E max{deg Q, r}
for (Qe, Ne, re) in [(Qc, Nc, r),
                     ((1 - t)**2 * (1 - t / 3), 1 + t + z * (2 - t) + z**2 + z**3 * t, 3),
                     ((1 - t) * (1 - t / 2) * (1 - t / 4), z**2 * (1 + t) + z * (3 - t**2) + 5, 1)]:
    Ee = sp.Poly(Ne, z).degree()
    Ae = sp.expand(sp.cancel(t**(re * Ee) * Ne.subs(z, -Qe / t**re)))
    bound = sp.Poly(Ne, t).degree() + Ee * max(sp.Poly(sp.expand(Qe), t).degree(), re)
    assert sp.Poly(Ae, t).degree() <= bound
print('PASS: deg[t^(rE) N(t,-Q/t^r)] <= deg_t N + E max{deg Q, r} (Question 7.1)')

Mmax = max(24, cutoff + 8)
P = ratio_coeffs(Qc, Nc, r, Mmax)
F = ratio_coeffs(Qc, B, r, Mmax + r * E - mu)
assert mu == 0, mu                                               # this N gives no factorization
for m in range(cutoff + 1, Mmax + 1):
    assert sp.expand(P[m] - F[m + r * E - mu]) == 0             # eq. (2.3)
print(f'PASS: P_m = [t^(m+rE-mu)] B/D for m = {cutoff+1},...,{Mmax} (mu = 0)')

# eq. (2.3) with mu > 0, so the A = t^mu B factorization is actually exercised and the
# shift m -> m + rE - mu is not just m -> m + rE.  Every case above has mu = 0, which left
# the factorization step and the -mu in the shift untested.
for (Qm, Nm, rm) in (((1 - t) * (1 - 2 * t), t * (1 + z), 2),
                     ((1 - t) * (1 - 2 * t), z * t + z**2 * t**2, 2),
                     ((1 - t)**2 * (1 - t / 3), 1 + t + z * (2 - t) + z**2 + z**3 * t, 3)):
    Qm = sp.expand(Qm)
    Em, Am, mum, Bm = laurent_reduce(Qm, Nm, rm)
    assert mum > 0, (Nm, mum)                                    # the point of this block
    assert sp.expand(Am - t**mum * Bm) == 0                      # A = t^mu B
    assert sp.Poly(Bm, t).nth(0) != 0                            # B(0) != 0
    Dm = Qm + z * t**rm
    Sm = sp.cancel((Nm - t**(-rm * Em) * Am) / Dm)
    assert sp.cancel(Nm - (Dm * Sm + t**(-rm * Em) * Am)) == 0    # eq. (2.2) at mu > 0
    cut_m = max_t_exp(Sm)
    # clamp at 0: S's top t-exponent can be negative (it is -2 for the r=3 case below), and
    # a negative start index would silently wrap round the coefficient list in Python
    m_from = max(0, cut_m + 1)
    Mm = max(24, cut_m + 8)
    Pm_ = ratio_coeffs(Qm, Nm, rm, Mm)
    Fm_ = ratio_coeffs(Qm, Bm, rm, Mm + rm * Em)     # + mum extra, for the no--mu comparison
    for m in range(m_from, Mm + 1):
        assert sp.expand(Pm_[m] - Fm_[m + rm * Em - mum]) == 0    # eq. (2.3)
    # and the -mu really matters: dropping it breaks the identity
    bad_shift = [m for m in range(m_from, Mm + 1)
                 if sp.expand(Pm_[m] - Fm_[m + rm * Em]) != 0]
    assert bad_shift, (Nm, 'shift without -mu accidentally agreed')
    print(f'PASS: eq. (2.3) at mu = {mum} (E = {Em}, r = {rm}): '
          f'P_m = [t^(m+rE-mu)] B/D for m = {m_from},...,{Mm}; '
          f'omitting -mu fails at {len(bad_shift)} of those indices')

# A = 0 <=> D | N: taking N = D (improper) collapses A to zero.
E0 = sp.Poly(sp.expand(D), z).degree()
A_improper = sp.expand(sp.cancel(t**(r * E0) * D.subs(z, -Qc / t**r)))
assert A_improper == 0
print('PASS: A = 0 exactly when D | N (checked on N = D); proper N gives A != 0')


# ===========================================================================
# Lemma 2.3, eq. (2.6): deg F_M = floor(M/r), and the exact z^ell coefficient law
# ===========================================================================
# The threshold below is a FIXED constant.  Reading it off the failures instead --
# last_bad = max(bad), then asserting the law on range(last_bad+1, Mtop+1) -- is a
# tautology: that range excludes every failure by construction, so it passes on a degree
# list wrong at every index.
for (Q, r, B, Mtop) in [
    (sp.expand((1 - t) * (1 - 2 * t) * (1 - 3 * t)), 2, 1 + 2 * t + t**2, 40),
    (sp.expand((1 - t)**2 * (1 - 4 * t)), 3, 2 - t + 3 * t**2, 45),
    (sp.expand(1 - t), 1, 1 + 2 * t + t**2, 30),                # r = 1, deg Q = 1
]:
    F = ratio_coeffs(Q, B, r, Mtop)
    bad = [m for m in range(Mtop + 1) if zdeg(F[m]) != m // r]
    # Lemma 2.3 claims eq. (2.6) for all SUFFICIENTLY LARGE M, not for every M.  Asserting
    # `not bad` is stronger than the paper and passed only by luck of these examples: with
    # Q = 1-t, B = 1-2t, r = 2 the law fails at M = 3 (deg F_3 = 0, not 1), and with
    # B = 1-3t at M = 5 -- both exhibited below.  Assert the paper's form instead, with the
    # threshold FIXED rather than read off `bad`: reading it off (last_bad = max(bad), then
    # asserting above it) is a tautology, since the range then excludes every failure by
    # construction and the assert cannot fire for any data.
    M_LO = 12                                                      # fixed, not derived from bad
    assert Mtop > M_LO + 5, Mtop
    tail_bad = [m for m in range(M_LO, Mtop + 1) if zdeg(F[m]) != m // r]
    assert not tail_bad, (sp.Poly(Q, t).degree(), r, tail_bad)     # eq. (2.6) for M >= M_LO
    assert len(bad) <= 1, (sp.Poly(Q, t).degree(), r, bad)         # finitely many exceptions
    print(f'PASS: deg F_M = floor(M/r) for every M in [{M_LO},{Mtop}]  '
          f'(deg Q={sp.Poly(Q, t).degree()}, r={r}); exceptions below {M_LO}: {bad}')

# "Sufficiently large" is load-bearing: two admissible (Q, B, r) where a small M fails.
# The mechanism is eq. (2.9): the z^ell coefficient is (-1)^ell [t^s] B/Q^{ell+1} with
# ell = floor(M/r), s = M - r*ell, and for Q = 1-t, B = 1-ct that coefficient is
# C(ell+s,s) - c*C(ell+s-1,s-1), which vanishes for small (ell,s) at suitable c.
for (Qw, Bw, rw, Mw) in ((1 - t, 1 - 2 * t, 2, 3), (1 - t, 1 - 3 * t, 2, 5)):
    Fw = ratio_coeffs(Qw, Bw, rw, Mw)
    assert zdeg(Fw[Mw]) < Mw // rw, (Qw, Bw, rw, Mw, zdeg(Fw[Mw]))
    Fw2 = ratio_coeffs(Qw, Bw, rw, 30)
    assert all(zdeg(Fw2[m]) == m // rw for m in range(Mw + 1, 31)), (Qw, Bw, rw)
    print(f'PASS: eq. (2.6) FAILS at M={Mw} for Q={Qw}, B={Bw}, r={rw} '
          f'(deg {zdeg(Fw[Mw])} < {Mw // rw}) but holds for every M in [{Mw + 1},30] -- '
          f'so "sufficiently large" cannot be dropped')


def leading_zcoeff_poly_in_ell(Q, B, smax):
    r"""Q(0)^{ell+1} [t^s]( B/Q^{ell+1} ) as a function of ell; assert it is a
    polynomial in ell of degree <= s with leading coefficient
    B(0) lambda^s / s!, and that this leading coefficient is NONZERO -- the step
    that yields attainment of the degree bound (eq. (2.9))."""
    Q0 = Q.subs(t, 0)
    lam = -sp.diff(Q, t).subs(t, 0) / Q0
    B0 = B.subs(t, 0)
    Qn = sp.expand(Q / Q0)                                        # Qn(0) = 1
    for s in range(smax + 1):
        logser = sp.series(sp.log(Qn), t, 0, s + 1).removeO()
        powser = sp.series(sp.exp(-(ell + 1) * logser), t, 0, s + 1).removeO()
        Bser = sp.series(B, t, 0, s + 1).removeO()
        cs = sp.expand(sp.expand(Bser * powser).coeff(t, s))       # = Q(0)^{ell+1}[t^s]B/Q^{ell+1}
        poly = sp.Poly(cs, ell)
        assert poly.degree() <= s
        lead = sp.simplify(B0 * lam**s / sp.factorial(s))
        assert sp.simplify(poly.LC() - lead) == 0
        assert lead != 0, (s, lead)                                # attainment: B(0) lambda^s != 0
    print(f'PASS: [t^s] leading z^ell coeff is poly_ell of deg<={smax}, lead '
          f'B(0)lambda^s/s! != 0 (attainment) (Q={sp.factor(Q)})')


leading_zcoeff_poly_in_ell((1 - t)**3, 2 - t + 3 * t**2, 4)
leading_zcoeff_poly_in_ell((1 - t / 2) * (1 - t / 3)**2, 1 + 5 * t, 4)
leading_zcoeff_poly_in_ell((1 - t) * (1 - t / 4), 7 + t + t**2 + t**3 + t**4, 5)

# lambda = -Q'(0)/Q(0) = sum_j 1/x_j (over the positive zeros, with multiplicity)
for xs in ([1, 2, 4], [sp.Rational(1, 2), 3, 3], [1, 1, 5, 5]):
    Ql = sp.prod(1 - t / x for x in xs)
    lam = -sp.diff(Ql, t).subs(t, 0) / Ql.subs(t, 0)
    assert sp.simplify(lam - sum(sp.Integer(1) / x for x in xs)) == 0
print('PASS: lambda = -Q\'(0)/Q(0) = sum_j 1/x_j')

# eq. (2.7)/(2.8): F_M(z) = sum_{0<=j<=M/r} (-z)^j [t^{M-rj}] B/Q^{j+1}
# eq. (2.9):       [z^ell] F_M = (-1)^ell [t^s] B/Q^{ell+1}, ell = floor(M/r), s = M - r*ell
Qc = (1 - t) * (1 - t / 2)
Bc = 1 + 2 * t + t**3
r = 2
F = ratio_coeffs(Qc, Bc, r, 25)
for M in (10, 15, 21, 25):
    expansion = sum((-z)**j * sp.series(Bc / Qc**(j + 1), t, 0, M - r * j + 1).removeO().coeff(t, M - r * j)
                    for j in range(M // r + 1))
    assert sp.expand(F[M] - expansion) == 0                        # eq. (2.7)/(2.8)
    qq, s = M // r, M - r * (M // r)
    lead = sp.Poly(F[M], z).nth(qq)
    ts = sp.series(Bc / Qc**(qq + 1), t, 0, s + 1).removeO().coeff(t, s)
    assert sp.expand(lead - (-1)**qq * ts) == 0                    # eq. (2.9)
print('PASS: F_M = sum (-z)^j [t^{M-rj}] B/Q^{j+1}, and [z^q]F_M = (-1)^q [t^s] B/Q^{q+1}')


# ===========================================================================
# Remark 2.4: deg P_m = m/r + O(1) with the fixed shift M = m + rE - mu
# ===========================================================================
Qc = sp.expand((1 - t) * (1 - 2 * t))
Nc = (1 + z + z**2) + t * (2 - z)
r = 2
E, A, mu, B = laurent_reduce(Qc, Nc, r)
P = ratio_coeffs(Qc, Nc, r, 30)
for m in range(cutoff + 1, 31):
    assert zdeg(P[m]) == (m + r * E - mu) // r
print(f'PASS: deg P_m = floor((m+rE-mu)/r) eventually (rE-mu = {r*E-mu} fixed)')


# ===========================================================================
# eq. (2.4): P_m = sum_j b_j H_{m+rE-mu-j}, with 1/(Q+z t^r) = sum_m H_m t^m
# ===========================================================================
# The reduced coefficient is a FIXED finite linear combination of the
# denominator-only sequence of eq. (1.2).  Both sides are compared exactly as
# polynomials in z.  The loop must start past deg S: eq. (2.4) is expanded from
# eq. (2.3), which itself holds only for m > deg S.
for (Qe, Ne, re) in [
    (sp.expand((1 - t) * (1 - 2 * t)), (1 + z + z**2) + t * (2 - z), 2),
    (sp.expand((1 - t)**2 * (1 - t / 3)), 1 + t + z * (2 - t) + z**2, 3),
    (sp.expand((1 - t) * (1 - t / 2) * (1 - t / 4)), z**2 * (1 + t) + 5, 1),
]:
    Ee, Ae, mue, Be = laurent_reduce(Qe, Ne, re)
    De = Qe + z * t**re
    Se = sp.cancel((Ne - t**(-re * Ee) * Ae) / De)
    cut = max_t_exp(Se)
    shift = re * Ee - mue
    bcoef = sp.Poly(Be, t).all_coeffs()[::-1]                      # b_0, b_1, ...
    Mhi = 22
    Pe = ratio_coeffs(Qe, Ne, re, Mhi)
    He = ratio_coeffs(Qe, sp.Integer(1), re, Mhi + shift)          # eq. (1.2)
    for m in range(max(cut + 1, 0), Mhi + 1):
        rhs = sum(bcoef[j] * He[m + shift - j]
                  for j in range(len(bcoef)) if 0 <= m + shift - j <= Mhi + shift)
        assert sp.expand(Pe[m] - rhs) == 0, (re, m)                # eq. (2.4)
    print(f'PASS: P_m = sum_j b_j H_(m+rE-mu-j) for m = {max(cut+1,0)},...,{Mhi} '
          f'(deg Q={sp.Poly(Qe, t).degree()}, r={re}, shift={shift})')


# ===========================================================================
# Scope: max{deg Q, r} > 1 is load-bearing (the standing hypothesis of section 1)
# ===========================================================================
# At deg Q = r = 1 the eventual degree of eq. (2.6) still holds, but g = -Q/t^r
# has NO positive critical point, so t_a, a and I_{Q,r} do not exist, and the
# count of Proposition 5.1 fails for every fixed C_B.  Witness:
#     Q = 1 - t, r = 1, B = 1 + 2t + 5t^2
#     F_M = (1-z)^{M-2} [ (1-z)^2 + 2(1-z) + 5 ],
# so deg F_M = M while the distinct-zero set is {1, 2-2i, 2+2i}: bounded by 3.
Qw, rw, Bw = sp.expand(1 - t), 1, 1 + 2 * t + 5 * t**2
assert max(sp.Poly(Qw, t).degree(), rw) == 1                       # the EXCLUDED case
Fw = ratio_coeffs(Qw, Bw, rw, 14)
deficits = []
for M in range(3, 15):
    closed = sp.expand((1 - z)**(M - 2) * ((1 - z)**2 + 2 * (1 - z) + 5))
    assert sp.expand(Fw[M] - closed) == 0, M                        # closed form
    assert zdeg(Fw[M]) == M                                         # deg F_M = M = floor(M/r)
    distinct = sp.Poly(Fw[M], z).all_roots()
    assert len(set(distinct)) == 3, (M, len(set(distinct)))          # {1, 2 +- 2i}
    deficits.append(M // rw - len(set(distinct)))
# the deficit floor(M/r) - #distinct GROWS, so no fixed C_B can absorb it
assert deficits == sorted(deficits) and deficits[-1] > deficits[0] + 8, deficits
assert deficits[-1] == 14 - 3, deficits[-1]
# and I_{Q,r} does not exist: g' = -(t Q' - r Q)/t^{r+1} has no positive zero
gw = -Qw / t**rw
assert sp.simplify(sp.diff(gw, t) - 1 / t**2) == 0
assert [c for c in sp.solve(sp.Eq(sp.diff(gw, t), 0), t) if c.is_real and c > 0] == []
print(f'PASS: max(deg Q,r) > 1 is load-bearing: at deg Q = r = 1 the deficit '
      f'floor(M/r) - #distinct grows {deficits[0]} -> {deficits[-1]} (no fixed C_B), '
      f'and g\' has no positive zero so I_(Q,r) does not exist')

print('ALL PASS: verify_reduction')
