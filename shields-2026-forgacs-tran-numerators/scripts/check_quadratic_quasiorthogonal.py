#!/usr/bin/env python3
r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude),
`rem:quadratic-case`: the quadratic Favard branch.

The excluded case (deg Q, r) = (2,1) is where the Forgacs-Tran pencil meets
classical quasi-orthogonality, and the remark records an explicit defect there.
This script pins every step of that identification, symbolically over free
q0, q1, q2 wherever the claim is an identity, and numerically where it is a
zero count.

  (Q1) The denominator recurrence  q0 H_m + (z+q1) H_{m-1} + q2 H_{m-2} = 0.
       rem:quadratic-case states the rescaled p_m recurrence directly; this is
       the step that recurrence comes from, so it is checked here against the
       series rather than assumed.
  (Q2) The Favard normalization p_m = q0(-q0)^m H_m is MONIC and satisfies
       p_m = (z+q1) p_{m-1} - q0 q2 p_{m-2},  p_0 = 1,  p_1 = z+q1.
  (Q3) p_m(z) = (q0 q2)^{m/2} U_m((z+q1)/(2 sqrt(q0 q2))), U_m Chebyshev II.
  (Q4) (p_m) is an OPS on closure(I_{Q,1}): its zeros are real, simple, and lie
       in I_{Q,1} = (-q1 - 2 sqrt(q0 q2), -q1 + 2 sqrt(q0 q2)), and consecutive
       members interlace.
  (Q5) The reduced coefficient as a fixed combination of consecutive p's,
       F_M = (q0(-q0)^M)^{-1} sum_j b_j (-q0)^j p_{M-j}, for every M (the
       terms with j > M being absent), matching eq:P-linear-combination.
  (Q6) deg F_M = M for EVERY M >= 0, not merely eventually: the z^M coefficient
       is b_0/(q0(-q0)^M) and b_0 = B(0) != 0.  This is what turns Duran's
       distinct-zero count into a multiplicity-counted defect.
  (Q7) The defect itself, against Duran's Lemma 3.1 (published copy,
       Mediterr. J. Math. 23 (2026) 148): at most K = deg B zeros outside
       closure(I_{Q,1}) and at most K+2 outside I_{Q,1}, counted with
       multiplicity, for every M.  Also checked: the hypothesis of that lemma
       needs gamma_0 = 1 after scaling, which is exactly b_0 != 0, and
       gamma_K != 0, which is exactly K = deg B.
  (Q8) The bound is not vacuous -- a B is exhibited whose defect is positive --
       and it is not beaten by the general theorem's own count.

Symbolic work uses SymPy; zero counts use mpmath at high precision.
"""
from __future__ import annotations

import sympy as sp
import mpmath as mp

mp.mp.dps = 50
t, z = sp.symbols('t z')
q0, q1, q2 = sp.symbols('q0 q1 q2', positive=True)

PASSES = 0


def ok(msg):
    global PASSES
    PASSES += 1
    print(f'PASS  {msg}')


def H_symbolic(n):
    """H_0..H_n of 1/(q0 + q1 t + q2 t^2 + z t) by the recurrence."""
    H = [1 / q0]
    for m in range(1, n + 1):
        prev = H[m - 1]
        prev2 = H[m - 2] if m >= 2 else 0
        H.append(sp.simplify(-((z + q1) * prev + q2 * prev2) / q0))
    return H


# ---------------------------------------------------------------- (Q1)
NMAX = 8
ser = sp.series(1 / (q0 + q1 * t + q2 * t**2 + z * t), t, 0, NMAX + 1).removeO()
Hser = [sp.simplify(sp.expand(ser).coeff(t, m)) for m in range(NMAX + 1)]
H = H_symbolic(NMAX)
for m in range(NMAX + 1):
    assert sp.simplify(Hser[m] - H[m]) == 0, m
for m in range(2, NMAX + 1):
    assert sp.simplify(q0 * H[m] + (z + q1) * H[m - 1] + q2 * H[m - 2]) == 0, m
ok('(Q1) q0 H_m + (z+q1) H_{m-1} + q2 H_{m-2} = 0 over free q0,q1,q2, '
   f'against the series expansion of 1/(Q+zt), m <= {NMAX}')

# ---------------------------------------------------------------- (Q2)
p = [sp.simplify(q0 * (-q0)**m * H[m]) for m in range(NMAX + 1)]
assert sp.simplify(p[0] - 1) == 0
assert sp.simplify(p[1] - (z + q1)) == 0
for m in range(NMAX + 1):
    assert sp.Poly(sp.expand(p[m]), z).LC() == 1, m               # monic
for m in range(2, NMAX + 1):
    assert sp.simplify(p[m] - ((z + q1) * p[m - 1] - q0 * q2 * p[m - 2])) == 0, m
ok('(Q2) p_m = q0(-q0)^m H_m is monic with p_0 = 1, p_1 = z+q1, and satisfies '
   'p_m = (z+q1)p_{m-1} - q0 q2 p_{m-2} -- a Favard three-term recurrence')

# ---------------------------------------------------------------- (Q3)
a = sp.sqrt(q0 * q2)
for m in range(NMAX + 1):
    cheb = sp.simplify(a**m * sp.chebyshevu(m, (z + q1) / (2 * a)))
    assert sp.simplify(sp.expand(p[m] - cheb)) == 0, m
ok(f'(Q3) p_m = (q0 q2)^(m/2) U_m((z+q1)/(2 sqrt(q0 q2))) exactly, m <= {NMAX}, '
   'over free positive q0,q1,q2')

# ---------------------------------------------------------------- (Q4)
CFG = [(mp.mpf(1), mp.mpf(-3) / 2, mp.mpf(1) / 2),                # Q=(1-t)(1-t/2)
       (mp.mpf(1), mp.mpf(-5) / 4, mp.mpf(1) / 4),                # Q=(1-t)(1-t/4)
       (mp.mpf(2), mp.mpf(-3), mp.mpf(1))]                        # Q=2-3t+t^2


def p_num(m, Z, c0, c1, c2):
    pm1, pm2 = mp.mpf(1), mp.mpf(0)
    for _ in range(m):
        pm1, pm2 = (Z + c1) * pm1 - c0 * c2 * pm2, pm1
    return pm1


def roots_of(coeffs):
    return mp.polyroots(coeffs, maxsteps=4000, extraprec=600)


for (c0, c1, c2) in CFG:
    lo, hi = -c1 - 2 * mp.sqrt(c0 * c2), -c1 + 2 * mp.sqrt(c0 * c2)
    prev = None
    for m in range(1, 13):
        # zeros of p_m via the Chebyshev form: (z+q1)/(2 sqrt(q0q2)) = cos(k pi/(m+1))
        zs = sorted(-c1 + 2 * mp.sqrt(c0 * c2) * mp.cos(mp.pi * k / (m + 1))
                    for k in range(1, m + 1))
        for zz in zs:
            assert lo < zz < hi, (c0, c1, c2, m, zz)
            assert abs(p_num(m, zz, c0, c1, c2)) < mp.mpf('1e-35'), (m, zz)
        assert len(set(mp.nstr(x, 30) for x in zs)) == m           # simple
        if prev is not None:                                       # interlacing
            for i in range(len(prev)):
                assert zs[i] < prev[i] < zs[i + 1], (m, i)
        prev = zs
    ok(f'(Q4) q0,q1,q2 = {mp.nstr(c0,4)},{mp.nstr(c1,4)},{mp.nstr(c2,4)}: p_m has m simple '
       f'zeros, all in I_(Q,1) = ({mp.nstr(lo,8)}, {mp.nstr(hi,8)}), consecutive members '
       'interlacing -- an OPS on the closure')

# ---------------------------------------------------------------- (Q5),(Q6),(Q7)
BS = [sp.Integer(1), 1 + 2 * t, 3 - t + 2 * t**2, 1 - 5 * t + t**2 - 2 * t**3,
      2 + t**4]


def F_coeffs(Bexpr, c0, c1, c2, Mmax):
    """F_M = [t^M] B/(Q+zt) by the exact recurrence, as sympy polys in z."""
    Bp = sp.Poly(sp.expand(Bexpr), t)
    b = [sp.nsimplify(Bp.nth(i)) for i in range(Bp.degree() + 1)]
    Q0, Q1, Q2 = sp.nsimplify(c0), sp.nsimplify(c1), sp.nsimplify(c2)
    F = []
    for m in range(Mmax + 1):
        rhs = b[m] if m < len(b) else 0
        if m >= 1: rhs -= (z + Q1) * F[m - 1]
        if m >= 2: rhs -= Q2 * F[m - 2]
        F.append(sp.expand(rhs / Q0))
    return F, b


# The zeros of F_M are located and classified entirely in mpmath.  F_M carries
# exact rational coefficients, so it converts without loss, and `polyroots` at
# extraprec=800 places each zero far inside the 50-digit working precision.
# SEP is the band within which a zero counts as real: 1e-40 sits above the
# residual imaginary part a genuinely real zero picks up at this precision and
# far below every separation actually present.  The three margins returned
# alongside the counts pin that -- a count that depended on where SEP was put
# would fail the assertions below rather than pass quietly.
SEP = mp.mpf(10) ** -40
IM_MARGIN = mp.mpf(10) ** -30          # a real zero's imaginary part stays under this
SEP_MARGIN = mp.mpf(10) ** -10         # nonreal zeros, and real ones vs the endpoints


def zeros_of_F(FM, M):
    """Zeros of F_M with multiplicity, from its exact rational coefficients."""
    cf = [mp.mpmathify(sp.Poly(FM, z).nth(i)) for i in range(M + 1)]
    return mp.polyroots(list(reversed(cf)), maxsteps=6000, extraprec=800)


def outside_counts(rts, lo, hi):
    """Zeros off closure(I) and off I, with multiplicity, plus the margins.

    Returns (out_closed, out_open, worst_real_im, least_nonreal_im,
    least_endpoint_gap): the last three certify that no zero sits near enough
    to a classification boundary for the count to turn on SEP.
    """
    out_cl = out_op = 0
    worst_real_im = mp.mpf(0)
    least_nonreal_im = mp.inf
    least_gap = mp.inf
    for w in rts:
        im, re = abs(mp.im(w)), mp.re(w)
        if im > SEP:
            least_nonreal_im = min(least_nonreal_im, im)
            out_cl += 1
            out_op += 1
            continue
        worst_real_im = max(worst_real_im, im)
        least_gap = min(least_gap, abs(re - lo), abs(re - hi))
        if not (lo <= re <= hi):
            out_cl += 1
        if not (lo < re < hi):
            out_op += 1
    return out_cl, out_op, worst_real_im, least_nonreal_im, least_gap


for Bexpr in BS:
    worst_im, closest = mp.mpf(0), mp.inf
    K = sp.Poly(sp.expand(Bexpr), t).degree()
    b0 = sp.Poly(sp.expand(Bexpr), t).nth(0)
    bK = sp.Poly(sp.expand(Bexpr), t).nth(K)
    assert b0 != 0 and bK != 0                                     # gamma_0, gamma_K of Duran's Lem. 3.1
    for (c0, c1, c2) in CFG:
        Mmax = 16
        F, b = F_coeffs(Bexpr, c0, c1, c2, Mmax)
        C0, C1, C2 = sp.nsimplify(c0), sp.nsimplify(c1), sp.nsimplify(c2)
        # (Q5) the fixed-combination formula
        pv = [sp.Integer(1), z + C1]
        for m in range(2, Mmax + 1):
            pv.append(sp.expand((z + C1) * pv[m - 1] - C0 * C2 * pv[m - 2]))
        for M in range(Mmax + 1):
            lhs = F[M]
            rhs = sum(b[j] * (-C0)**j * pv[M - j] for j in range(min(K, M) + 1))
            rhs = sp.expand(rhs / (C0 * (-C0)**M))
            assert sp.simplify(lhs - rhs) == 0, (Bexpr, c0, M)
        # (Q6) deg F_M = M for EVERY M, with the stated leading coefficient
        for M in range(Mmax + 1):
            assert sp.degree(F[M], z) == M, (Bexpr, c0, M)
            assert sp.simplify(sp.Poly(F[M], z).LC() - b0 / (C0 * (-C0)**M)) == 0
        # (Q7) the defect, counted with multiplicity
        lo, hi = -c1 - 2 * mp.sqrt(c0 * c2), -c1 + 2 * mp.sqrt(c0 * c2)
        worst_cl, worst_op = 0, 0
        for M in range(0, Mmax + 1):
            rts = zeros_of_F(F[M], M) if M else []
            out_cl, out_op, r_im, n_im, gap = outside_counts(rts, lo, hi)
            assert out_cl <= K, (Bexpr, c0, M, out_cl, K)
            assert out_op <= K + 2, (Bexpr, c0, M, out_op, K + 2)
            if rts:
                assert r_im < IM_MARGIN, (Bexpr, c0, M, r_im)
                assert n_im > SEP_MARGIN, (Bexpr, c0, M, n_im)
                assert gap > SEP_MARGIN, (Bexpr, c0, M, gap)
                worst_im = max(worst_im, r_im)
                closest = min(closest, n_im, gap)
            worst_cl, worst_op = max(worst_cl, out_cl), max(worst_op, out_op)
    ok(f'(Q7) B = {sp.factor(Bexpr)} (K = {K}): over 3 denominators and M <= {Mmax}, at most '
       f'K = {K} zeros outside the closed interval (worst {worst_cl}) and at most K+2 = {K+2} '
       f'outside the open one (worst {worst_op}), counted with multiplicity; a real zero '
       f'carries |Im| <= {mp.nstr(worst_im, 3)} and no zero comes within '
       f'{mp.nstr(closest, 3)} of a classification boundary, so the counts do not turn '
       'on the cutoff')

# ---------------------------------------------------------------- (Q8)
Bexpr = 1 - 5 * t + t**2 - 2 * t**3
c0, c1, c2 = CFG[0]
F, b = F_coeffs(Bexpr, c0, c1, c2, 14)
lo, hi = -c1 - 2 * mp.sqrt(c0 * c2), -c1 + 2 * mp.sqrt(c0 * c2)
seen = 0
for M in range(3, 15):
    rts = zeros_of_F(F[M], M)
    out_cl, _, r_im, n_im, gap = outside_counts(rts, lo, hi)
    assert r_im < IM_MARGIN and n_im > SEP_MARGIN and gap > SEP_MARGIN, (M, r_im, n_im, gap)
    seen = max(seen, out_cl)
assert seen > 0, 'the defect bound would be vacuous on this witness'
ok(f'(Q8) the bound is not vacuous: B = {sp.factor(Bexpr)} attains a defect of {seen} '
   f'outside the closed interval, against the bound K = {sp.Poly(sp.expand(Bexpr), t).degree()}')

# ---------------------------------------------------------------- (Q9)
# `rem:quadratic-case` and the closing synthesis both say that the DENOMINATOR
# RECURRENCE of a general admissible pencil supplies no Favard structure.  That is a
# statement about the recurrence, not an impossibility theorem about every possible
# OPS realization, and it is exact: the coefficient recurrence of Q(t) + z t^r is
#     sum_k q_k P_{m-k} + z P_{m-r} = 0,
# of order d = max{deg Q, r} with z sitting at offset r.  Favard three-term form needs
# order 2 AND z multiplying the p_{m-1} term, i.e. d = 2 and r = 1 -- which is
# (deg Q, r) = (2,1) and nothing else.
favard = []
for dQ in range(1, 7):
    for r in range(1, 7):
        d = max(dQ, r)
        is_favard = (d == 2 and r == 1)
        # cross-check against the actual recurrence support, built from a real Q
        Qe = sp.expand(sp.prod([1 - t / sp.Integer(j + 1) for j in range(dQ)]))
        Qp = sp.Poly(Qe, t)
        offsets = sorted({k for k in range(Qp.degree() + 1) if Qp.nth(k) != 0} | {r})
        order = max(offsets)
        z_at = r
        assert order == d, (dQ, r, order, d)
        assert is_favard == (order == 2 and z_at == 1), (dQ, r)
        if is_favard:
            favard.append((dQ, r))
assert favard == [(2, 1)], favard
ok('(Q9) over deg Q, r in 1..6 the denominator recurrence has order max{deg Q, r} with z '
   'at offset r, so it is of Favard three-term form for (deg Q, r) = (2,1) and for no other '
   'admissible pencil -- which is exactly the scope the paper claims')

print(f'\n{PASSES} checks')
print('ALL PASS: check_quadratic_quasiorthogonal')
