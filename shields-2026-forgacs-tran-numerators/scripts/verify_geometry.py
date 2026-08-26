#!/usr/bin/env python3
r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude).

Symbolic work uses SymPy; numerical work uses mpmath at arbitrary precision
(no floating-point arithmetic in the verification loops).  Roots of the
denominator D(t,z) = Q(t) + z t^r are found with mpmath.polyroots.

  * `eq:ab-def`: the interval I_{Q,r} = (a,b).  Lower endpoint a = g(t_a) by bisection,
    cross-checked against the critical-point route t_a Q'(t_a) = r Q(t_a); upper endpoint
    b = +inf precisely when r > 1, and b = g(t_b) finite for r = 1 (t_b < 0 the unique
    negative critical point of g(t) = -Q(t)/t^r), with z(theta) -> b as theta -> pi.
  * `thm:FT-geometry`, `eq:principal-pair`: the two minimum-modulus denominator zeros form a
    conjugate pair t_+- = tau e^{+-i theta}, and every other zero has strictly
    larger modulus (verified on a z-grid for r = 2, 3, where I_{Q,r} = (a,+inf)).
  * `thm:FT-geometry`, `eq:endpoint-linear-gap`: the endpoint linear modulus gap.  Lower endpoint
    (repeated smallest zero, mult rho): |zeta_k| = 1 + [(cos(pi/rho)-Re omega_k)/
    sin(pi/rho)] theta + O(theta^2), omega_k the rho-th roots of -1; the linear
    coefficient vanishes for the two principal roots and is positive otherwise.
    Upper endpoint (r > 1): the same law with the r-th roots of -1 and eta = pi/r - theta.
    Coefficients are recovered by Richardson extrapolation of (|zeta|-1)/(angular distance).
  * `eq:contour-separated-expansion`, `eq:simple-residue-amplitude` with Gamma enclosing
    EVERY finite root, where the expansion degenerates to the d-term residue sum
        F_M(z) = -sum_j B(t_j)/(t_j^{M+1}(Q'(t_j)+r z t_j^{r-1})).
    That sum equals [t^M] B/D exactly for M > deg B - d and differs by the
    polynomial-part coefficient [t^M]( B div D ) below the threshold -- so the
    threshold is a property of that maximal choice of Gamma, not of the lemma,
    which holds for every M >= 0 once Gamma retains only the competing roots.
  * `eq:principal-decomposition`: tau^{M+1} F_M(z(theta)) = 2 Re( W e^{-i(M+1)theta} ) + R_M, with
    W = -B(t_+)/(Q'(t_+)+r z t_+^{r-1}) and R_M the grouped nonprincipal contribution.
  * `thm:FT-geometry` and `lem:contour-separation` at the degree-drop parameter
    z_inf = -q_d, where deg Q = r and one root leaves every bounded set.  In the
    reciprocal coordinate that root has order u_inf^{M+d-1-deg B} at z_inf, hence a
    vanishing contribution once M > deg B - d + 1; the paper needs none of that,
    because the root sits OUTSIDE the fixed separating circle and is absorbed into
    E_M.  Both routes are run, and agree.
  * `eq:Dprime-identity`: D'(t_j) = Q'(t_j) - r Q(t_j)/t_j at a denominator root -- the general-t_j
    form is section `sec:dominance`'s, restated for t_+ alone inside `lem:amplitude-divisor`'s proof.  And the branch
    map theta |-> t_+(theta) is injective (arg t_+ strictly monotone in z), so B(t_+)
    -- hence W -- has at most deg B zeros on (0, pi/r).
  * `lem:amplitude-divisor`, `eq:W-endpoint-form` upper-endpoint form (r > 1): t_+ -> 0, so Q'(t_+) - r Q(t_+)/t_+
    is a SIMPLE POLE (|D'(t_+) * t_+| -> r Q(0)); the rewritten quotient
    W = -t_+ B(t_+)/(t_+ Q'(t_+) - r Q(t_+)) has denominator -> -r Q(0) != 0, and with
    B(0) != 0 and t_+ = eta T(eta) (T(0) != 0) gives W = eta V(eta), V(0) != 0, i.e. p = 1.
  * `lem:amplitude-divisor`, `eq:W-endpoint-form` endpoint form: with k the multiplicity of the endpoint
    collision (k = max{rho,2} lower, k = 2 finite upper) and B vanishing at the endpoint
    limit to order nu, |W| ~ delta^p with p = nu - (k-1), which may be negative -- and is
    negative generically, p = -1 at an ordinary double collision with B nonvanishing.
    Tested at all four regimes the paper distinguishes: k = rho at the lower endpoint,
    k = 2 at rho = 1, k = 2 at the finite (r = 1) upper endpoint, and p = 1 for r > 1.
  * `lem:amplitude-divisor`, `eq:W-endpoint-form` finite-endpoint local parameter: the regularity of t_+ is
    proved through a REAL one-sided y >= 0 with z - z_e = eps y^k, eps = sgn(z - z_e)
    on the interior side (+1 lower, -1 finite upper), the sign absorbed into
    Lambda = (-eps t^r/G(t))^{1/k} so the prefactor keeps omega^k = 1.  Checks that
    Lambda is nonvanishing (t_e != 0, G(t_e) != 0), that the k leading coefficients
    omega Lambda(t_e) are distinct (so gamma fixes the branch -- what makes the
    conjugation argument bite), that the branch set is conjugation-closed with
    gamma real <=> branch real, and that delta = +-Im log(t_+/t_e) has
    delta'(0) = |Im(gamma_0/t_e)| != 0.  Both rejected routes are asserted REFUTED at
    every finite upper endpoint: a complex v with v^k = z - z_e is imaginary there,
    with d t/d v REAL for a NONREAL branch, and putting the sign in the
    prefactor instead would need mu^k = -1 (at k = 2, mu = +-i, not a kth root of 1).
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

mp.mp.dps = 50
t, z = sp.symbols('t z')


# --- mpmath denominator helpers ------------------------------------------------
def d_roots(Qlow, r, zval):
    r"""Zeros of the denominator D(t,z) = Q(t) + z t^r (`thm:FT-geometry`), Qlow = coeffs of Q
    low->high, returned as an mpmath complex list."""
    d = max(len(Qlow) - 1, r)
    c = [mp.mpf(0)] * (d + 1)
    for i, co in enumerate(Qlow):
        c[i] += mp.mpf(co)
    c[r] += mp.mpf(zval)
    return mp.polyroots(list(reversed(c)), maxsteps=3000, extraprec=300)


def pval(coeffs_low, x):
    return sum(mp.mpf(c) * x**i for i, c in enumerate(coeffs_low))


def dval(coeffs_low, x):                                          # Q'(x)
    return sum(mp.mpf(coeffs_low[i]) * i * x**(i - 1) for i in range(1, len(coeffs_low)))


def principal(rts):
    o = sorted(rts, key=lambda w: abs(w))
    for w in o:
        if abs(mp.im(w)) > mp.mpf('1e-25'):
            return w
    return o[0]


def qlow(expr):
    p = sp.Poly(sp.expand(expr), t)
    return [p.nth(i) for i in range(p.degree() + 1)]


# ===========================================================================
# `thm:FT-geometry`, `eq:principal-pair`: minimum-modulus conjugate pair, strict gap to the rest
# ===========================================================================
Q0 = sp.expand((1 - t) * (1 - t / 2) * (1 - t / 4))              # positive zeros 1,2,4
Qc = qlow(Q0)
for r in (2, 3):                                                  # b = +inf, whole ray is interior
    zs = [mp.mpf(s) for s in ('0.05', '0.2', '1', '3', '10', '50')]
    for zval in zs:
        o = sorted(d_roots(Qc, r, zval), key=lambda w: abs(w))
        t1, t2, t3 = o[0], o[1], o[2]
        assert abs(t1 - mp.conj(t2)) < mp.mpf('1e-30'), (r, zval)   # conjugate pair
        assert abs(mp.im(t1)) > mp.mpf('1e-20')                     # genuinely complex
        assert abs(t3) / abs(t2) > 1 + mp.mpf('1e-6'), (r, zval)    # strict modulus gap
    print(f'PASS: r={r}: two min-modulus zeros are a conjugate pair tau e^(+-i theta), '
          f'strict gap to the third')


# ===========================================================================
# `eq:ab-def`: the interval I_{Q,r} = (a,b), a = g(t_a), g(t) = -Q(t)/t^r
# ===========================================================================
def has_conjugate_pair(Qc, r, zval):
    o = sorted(d_roots(Qc, r, zval), key=lambda w: abs(w))
    return abs(mp.im(o[0])) > mp.mpf('1e-15')


def lower_endpoint_bisect(Qc, r, zhi=mp.mpf('1e6')):
    r"""Smallest z>0 at which the min-modulus pair becomes complex = lower endpoint a."""
    lo, hi = mp.mpf(0), zhi
    assert has_conjugate_pair(Qc, r, hi)
    for _ in range(200):
        mid = (lo + hi) / 2
        if has_conjugate_pair(Qc, r, mid):
            hi = mid
        else:
            lo = mid
    return hi


def t_a_of(Qc_, Qexpr_, r_):
    r"""The paper's t_a: the SMALLEST positive critical point of g = -Q/t^r (`eq:ab-def`).

    Selection is by POSITION, which is what the paper specifies, not by the sign of
    g(t_a): Q = (1-t)(1-t/2)(1-t/4) has two positive critical points (at r = 2, 1.2997 with
    g = +0.0419 and 2.9185 with g = -0.0280), and selecting on g > 0 would agree only by
    accident here and would exclude outright every Q with a repeated smallest zero, where
    the paper gives a = g(t_a) = 0 (`thm:FT-geometry`, proof).  Roots stay in mpmath at full precision;
    realness is decided at 1e-30, not at a float64 threshold.
    """
    hlow = qlow(sp.expand(t * sp.diff(Qexpr_, t) - r_ * Qexpr_))
    while len(hlow) > 1 and hlow[-1] == 0:
        hlow.pop()
    rts_ = mp.polyroots([mp.mpf(sp.Rational(c)) for c in reversed(hlow)],
                        maxsteps=3000, extraprec=400)
    pos = sorted(mp.re(w) for w in rts_
                 if abs(mp.im(w)) < mp.mpf('1e-30') and mp.re(w) > mp.mpf('1e-30'))
    assert pos, 'no positive critical point of g'
    return pos


Q0expr = (1 - t) * (1 - t / 2) * (1 - t / 4)
Qc = qlow(Q0expr)
# critical points of g: t Q'(t) - r Q(t) = 0, then a = -Q(t_a)/t_a^r
for r in (2, 3):
    a_bis = lower_endpoint_bisect(Qc, r)
    pos_all = t_a_of(Qc, Q0expr, r)
    assert len(pos_all) >= 2, pos_all   # this Q really has a second positive critical point
    ta = pos_all[0]                                                # the SMALLEST
    a_crit = -sum(mp.mpf(Qc[i]) * ta**i for i in range(len(Qc))) / ta**r
    assert abs(a_bis - a_crit) < mp.mpf('1e-20'), (r, a_bis, a_crit)
    # "smallest" is load-bearing: the next positive critical point gives a different value,
    # so a rule selecting any positive critical point would not pin a
    a_other = -sum(mp.mpf(Qc[i]) * pos_all[1]**i for i in range(len(Qc))) / pos_all[1]**r
    assert abs(a_other - a_crit) > mp.mpf('0.01'), (a_other, a_crit)
    # z(theta) -> a as theta -> 0+ (approach the lower endpoint from inside I)
    z_small = a_bis * (1 + mp.mpf('1e-3'))
    assert abs(mp.arg(principal(d_roots(Qc, r, z_small)))) < mp.mpf('0.05')
    print(f'PASS: r={r}: lower endpoint a = {mp.nstr(a_bis, 8)} = g(t_a), t_a = '
          f'{mp.nstr(ta, 8)} the SMALLEST of {len(pos_all)} positive critical points '
          f'(the next, {mp.nstr(pos_all[1], 6)}, would give {mp.nstr(a_other, 6)}); '
          f'z(theta) -> a as theta -> 0')


# The same rule at a repeated smallest zero -- the case a g>0 filter would exclude
# outright.  rho >= 2 forces t_a = x_1 and a = g(x_1) = 0 (`thm:FT-geometry`, proof), which is the
# hypothesis section `sec:dominance` consumes when it takes z(theta) -> 0 at the lower endpoint.
for Qe_rep in ((1 - t)**2 * (1 - t / 3), (1 - t)**3, (1 - t)**3 * (1 - t / 4)):
    Qc_rep = qlow(Qe_rep)
    for r_rep in (1, 2, 3):
        ta_rep = t_a_of(Qc_rep, Qe_rep, r_rep)[0]
        assert abs(ta_rep - 1) < mp.mpf('1e-25'), (Qe_rep, r_rep, ta_rep)   # t_a = x_1 = 1
        a_rep = -sum(mp.mpf(Qc_rep[i]) * ta_rep**i
                     for i in range(len(Qc_rep))) / ta_rep**r_rep
        assert abs(a_rep) < mp.mpf('1e-25'), (Qe_rep, r_rep, a_rep)         # a = 0 exactly
print('PASS: rho >= 2 gives t_a = x_1 and a = g(x_1) = 0 exactly '
      '(3 polynomials x r = 1,2,3), so z(theta) -> 0 at the lower endpoint')


# Upper endpoint: b = +inf precisely when r > 1; for r = 1, b = g(t_b) is finite,
# t_b < 0 the UNIQUE negative critical point of g(t) = -Q(t)/t^r.  Note that t = 0 is
# never a critical point (rQ - tQ' is nonzero there), so a "largest nonpositive" reading
# of the rule would be wrong, and for r > 1 it would return a spurious finite b whenever
# deg Q > r.  Both endpoints are zeros of t^{r-1}(rQ - tQ').
def interior_z(Qc, r):
    r"""Some z with a complex principal pair: a point strictly inside I_{Q,r}."""
    zval = mp.mpf('1e-3')
    while zval < mp.mpf('1e8'):
        if has_conjugate_pair(Qc, r, zval):
            return zval
        zval *= mp.mpf('1.2')
    raise RuntimeError('no interior point of I_{Q,r} found')


def upper_endpoint_bisect(Qc, r):
    r"""Largest z with a complex min-modulus pair = finite upper endpoint b (r = 1)."""
    lo = interior_z(Qc, r)
    hi = lo * 10
    while has_conjugate_pair(Qc, r, hi):
        hi *= 10
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if has_conjugate_pair(Qc, r, mid) else (lo, mid)
    return lo


# r > 1: b = +inf (the min-modulus pair stays complex at arbitrarily large z)
for r in (2, 3):
    assert has_conjugate_pair(qlow(Q0expr), r, mp.mpf('1e12'))
print('PASS: r>1: min-modulus pair still complex at z = 1e12, so b = +inf')

# r = 1, deg Q >= 2 (the boundary case max{deg Q, r} > 1): b = g(t_b) finite.
for Q1expr in [(1 - t) * (1 - t / 2), (1 - t) * (1 - t / 3) * (1 - t / 5)]:
    Qc1 = qlow(Q1expr)
    b_bis = upper_endpoint_bisect(Qc1, 1)
    # Roots in mpmath at full precision, realness decided at 1e-30: the uniqueness assert
    # below is what pins "the UNIQUE negative critical point" of `eq:ab-def`, so it must not
    # rest on a double-precision imaginary part.
    hlow_b = qlow(sp.expand(t * sp.diff(Q1expr, t) - Q1expr))        # t g'(t) numerator at r = 1
    while len(hlow_b) > 1 and hlow_b[-1] == 0:
        hlow_b.pop()
    negs_b = [mp.re(w) for w in mp.polyroots(
        [mp.mpf(sp.Rational(c)) for c in reversed(hlow_b)], maxsteps=3000, extraprec=400)
        if abs(mp.im(w)) < mp.mpf('1e-30') and mp.re(w) < -mp.mpf('1e-30')]
    assert len(negs_b) == 1, ('negative critical point of g is not unique', negs_b)
    t_b = negs_b[0]
    assert t_b < 0
    b_crit = -sum(mp.mpf(Qc1[i]) * t_b**i for i in range(len(Qc1))) / t_b
    assert b_bis < mp.mpf('1e5')                                    # finite
    assert abs(b_bis - b_crit) < mp.mpf('1e-6'), (b_bis, b_crit)
    # z(theta) -> b as theta -> pi/r = pi: the principal pair collides on the negative axis at t_b
    z_near = b_bis * (1 - mp.mpf('1e-4'))
    assert abs(mp.arg(principal(d_roots(Qc1, 1, z_near)))) > mp.pi - mp.mpf('0.05')
    print(f'PASS: r=1, Q={sp.factor(Q1expr)}: finite b = {mp.nstr(b_bis, 8)} = g(t_b), '
          f't_b = {mp.nstr(t_b, 6)} < 0, z(theta) -> b as theta -> pi')


# ===========================================================================
# `thm:FT-geometry`, `eq:endpoint-linear-gap`: endpoint linear modulus gaps (Richardson extrapolation)
# ===========================================================================
def richardson0(data):
    r"""Linear extrapolation to argument 0 of (x_k, y_k) using the two finest points."""
    (x1, y1), (x2, y2) = data[-2], data[-1]
    return y2 + (y2 - y1) * (0 - x2) / (x2 - x1)


# Lower endpoint: pure repeated zero Q = (1-t)^rho, so the whole root set clusters at t=1.
rho = 3
omk = [mp.expj((2 * k - 1) * mp.pi / rho) for k in range(1, rho + 1)]
pred_low = sorted((mp.cos(mp.pi / rho) - mp.re(w)) / mp.sin(mp.pi / rho) for w in omk)
Qrho = qlow((1 - t)**rho)
for r in (1, 2):
    prin, nonprin = [], []
    for k in range(4, 11):
        zval = mp.mpf(10)**(-k)
        rts = d_roots(Qrho, r, zval)
        pr = principal(rts); tau = abs(pr); th = abs(mp.arg(pr))
        coeffs = sorted((abs(w) / tau - 1) / th for w in rts)     # every root is in the cluster
        prin.append((th, coeffs[0])); nonprin.append((th, coeffs[-1]))
    n_ex, p_ex = richardson0(nonprin), richardson0(prin)
    assert abs(n_ex - pred_low[-1]) < mp.mpf('1e-4'), (r, n_ex)   # nonprincipal -> positive coeff
    assert n_ex > mp.mpf('1'), n_ex                               # strictly positive gap
    assert abs(p_ex) < mp.mpf('1e-4'), (r, p_ex)                  # principal coeff -> 0
    print(f'PASS: lower endpoint rho=3, r={r}: nonprincipal coeff -> {mp.nstr(n_ex, 7)} '
          f'(= {mp.nstr(pred_low[-1], 7)}), principal -> 0')

# Upper endpoint (r > 1): r-th roots of -1; genuine nonprincipal members exist for r >= 3.
Q1 = qlow(1 - t)
for r in (2, 3, 4):
    ek = [mp.expj((2 * k - 1) * mp.pi / r) for k in range(1, r + 1)]
    pred_up = sorted((mp.cos(mp.pi / r) - mp.re(w)) / mp.sin(mp.pi / r) for w in ek)
    prin, nonprin = [], []
    for k in range(3, 9):
        zval = mp.mpf(10)**k
        rts = d_roots(Q1, r, zval)
        pr = principal(rts); tau = abs(pr); th = abs(mp.arg(pr)); eta = mp.pi / r - th
        small = sorted(rts, key=lambda w: abs(w))[:r]
        coeffs = sorted((abs(w) / tau - 1) / eta for w in small)
        prin.append((eta, coeffs[0])); nonprin.append((eta, coeffs[-1]))
    p_ex = richardson0(prin)
    assert abs(p_ex) < mp.mpf('1e-3'), (r, p_ex)                  # principal coeff -> 0
    if pred_up[-1] > mp.mpf('1e-6'):                              # r >= 3 has a nonprincipal root
        n_ex = richardson0(nonprin)
        assert abs(n_ex - pred_up[-1]) < mp.mpf('2e-3'), (r, n_ex)
        assert n_ex > mp.mpf('1'), n_ex
        print(f'PASS: upper endpoint r={r}: nonprincipal coeff -> {mp.nstr(n_ex, 7)} '
              f'(= {mp.nstr(pred_up[-1], 7)}), principal -> 0')
    else:
        print(f'PASS: upper endpoint r={r}: both small roots principal (coeff -> 0)')


# ===========================================================================
# The all-roots degeneration of `eq:contour-separated-expansion`, and its threshold M > deg B - d
# ===========================================================================
def FM_exact(Bexpr, Qexpr, r, z0, M):
    r"""[t^M] Bexpr/(Qexpr + z0 t^r) by the exact recurrence at rational z0."""
    Qp = sp.Poly(sp.expand(Qexpr), t); q0 = Qp.nth(0)
    qc = [Qp.nth(i) for i in range(Qp.degree() + 1)]
    Bp = sp.Poly(sp.expand(Bexpr), t)
    P = []
    for m in range(M + 1):
        rhs = Bp.nth(m)
        for i in range(1, len(qc)):
            if m - i >= 0:
                rhs -= qc[i] * P[m - i]
        if m - r >= 0:
            rhs -= z0 * P[m - r]
        P.append(sp.nsimplify(rhs / q0))
    return P[M]


Qexpr = (1 - t) * (1 - t / 2)
Bexpr = 1 + 2 * t + t**3 + 3 * t**5
r = 2
d = max(sp.Poly(sp.expand(Qexpr), t).degree(), r)
z0 = sp.Rational(3)
Bc, Qc = qlow(Bexpr), qlow(Qexpr)
degB = sp.Poly(sp.expand(Bexpr), t).degree()

# polynomial part of B/D (numeric z0): degree deg B - d, contributes to [t^M] for M <= deg B - d
D0 = sp.Poly(sp.expand(Qexpr + z0 * t**r), t)
quotient, _ = sp.div(sp.Poly(sp.expand(Bexpr), t), D0, t)
assert quotient.degree() == degB - d
rts = d_roots(Qc, r, z0)
for M in range(0, 10):
    residue_sum = -sum(pval(Bc, w) / (w**(M + 1) * (dval(Qc, w) + r * mp.mpf(z0) * w**(r - 1)))
                       for w in rts)
    fm = mp.mpf(str(FM_exact(Bexpr, Qexpr, r, z0, M)))
    polypart = mp.mpf(str(quotient.nth(M))) if M <= quotient.degree() else mp.mpf(0)
    assert abs(mp.re(residue_sum) - (fm - polypart)) < mp.mpf('1e-30'), M
    assert abs(mp.im(residue_sum)) < mp.mpf('1e-30')
    if M > degB - d:
        assert polypart == 0 and abs(mp.re(residue_sum) - fm) < mp.mpf('1e-30')
    else:
        assert polypart != 0                                       # formula genuinely fails here
print(f'PASS: F_M = residue sum + [t^M](B div D); pure residue formula holds iff M > deg B - d = {degB-d}')


# ===========================================================================
# Principal decomposition, `eq:principal-decomposition`
# ===========================================================================
for M in (5, 8, 13):                                               # M > deg B - d = 3
    for zval in (mp.mpf('0.7'), mp.mpf('4')):
        rts = d_roots(Qc, r, zval)
        pr = principal(rts); tau = abs(pr); th = mp.arg(pr)
        def Dp(w):
            return dval(Qc, w) + r * zval * w**(r - 1)
        W = -pval(Bc, pr) / Dp(pr)
        principal_pair = sorted(rts, key=lambda w: abs(w))[:2]
        nonprincipal = [w for w in rts if all(abs(w - p) > mp.mpf('1e-20') for p in principal_pair)]
        R_M = tau**(M + 1) * sum(-pval(Bc, w) / (w**(M + 1) * Dp(w)) for w in nonprincipal)
        lhs = tau**(M + 1) * mp.re(-sum(pval(Bc, w) / (w**(M + 1) * Dp(w)) for w in rts))
        rhs = 2 * mp.re(W * mp.expj(-(M + 1) * th)) + mp.re(R_M)
        assert abs(lhs - rhs) < mp.mpf('1e-28'), (M, zval, lhs - rhs)
print('PASS: tau^(M+1) F_M(z(theta)) = 2 Re(W e^(-i(M+1)theta)) + R_M')


# ===========================================================================
# `lem:contour-separation`, `eq:contour-separated-expansion`: a grouped cluster is holomorphic through a collision (individual
# residues singular), and O_K(q^M) after tau^{M+1} scaling when the cluster is exterior
# ===========================================================================
Qc_col = qlow((1 - t) * (1 - t / 2) * (1 - t / 5) * (1 - t / 6))   # outer pair (~5,6) collides at small z
r = 2


def outer_pair(zval):
    return sorted(d_roots(Qc_col, r, zval), key=lambda w: abs(w))[2:4]


def outer_complex(zval):
    return abs(mp.im(outer_pair(zval)[0])) > mp.mpf('1e-14')


def Dp_col(w, zval):
    return dval(Qc_col, w) + r * zval * w**(r - 1)


lo, hi = mp.mpf('0.001'), mp.mpf('0.005')
assert outer_complex(hi) and not outer_complex(lo)
for _ in range(150):
    mid = (lo + hi) / 2
    (lo, hi) = (lo, mid) if outer_complex(mid) else (mid, hi)
z_c = hi
assert abs(mp.im(sorted(d_roots(Qc_col, r, z_c), key=lambda w: abs(w))[0])) < mp.mpf('1e-10')  # principal still real
M = 25


def grouped(zval):
    return sum(-1 / (w**(M + 1) * Dp_col(w, zval)) for w in outer_pair(zval))


def indiv_max(zval):
    return max(abs(1 / (w**(M + 1) * Dp_col(w, zval))) for w in outer_pair(zval))


grp = [abs(grouped(z_c * (1 + d))) for d in (mp.mpf('-1e-3'), mp.mpf('1e-3'))]
assert abs(grp[0] - grp[1]) < mp.mpf('0.02') * grp[0]              # grouped continuous across z_c
ind = [indiv_max(z_c * (1 + d)) for d in (mp.mpf('1e-3'), mp.mpf('1e-5'), mp.mpf('1e-7'))]
assert ind[1] > 2 * ind[0] and ind[2] > 2 * ind[1]                # individual terms diverge ~ delta^{-1/2}
assert ind[2] > 10 * abs(grouped(z_c * (1 + mp.mpf('1e-7'))))     # grouped stays far below the singular parts
print(f'PASS: grouped cluster regular through the nonprincipal collision z_c = {mp.nstr(z_c, 6)} '
      f'(individual residues diverge)')

z_in = mp.mpf('0.3')                                              # inside I: outer pair is an exterior cluster
tau = abs(principal(d_roots(Qc_col, r, z_in)))
dec = [abs(sum(-1 / (w**(MM + 1) * Dp_col(w, z_in)) for w in outer_pair(z_in))) * tau**(MM + 1)
       for MM in (20, 40, 60, 80)]
assert all(dec[i + 1] < dec[i] for i in range(3)) and dec[-1] < dec[0] * mp.mpf('1e-6')
# the decay rate is the paper's tau/R_0, not merely "geometric": fit it and compare
q_fit = (dec[3] / dec[2])**(mp.mpf(1) / 20)
R0_cl = min(abs(w) for w in outer_pair(z_in))
assert abs(q_fit - tau / R0_cl) < mp.mpf('0.02') * (tau / R0_cl), (q_fit, tau / R0_cl)
print(f'PASS: exterior cluster contribution is O(q^M) after tau^(M+1) scaling, with the '
      f'fitted q = {mp.nstr(q_fit, 5)} matching tau/R_0 = {mp.nstr(tau / R0_cl, 5)}')


# ===========================================================================
# The E_M term of `eq:contour-separated-expansion` itself: the CONTOUR formula for a cluster's contribution to F_M,
#     -(1/2 pi i) oint_Gamma B(t) / ( t^{M+1} (Q(t) + z t^r) ) dt,
# with a NONCONSTANT B.  The block above tests a residue-sum surrogate at B = 1, which
# supports holomorphy but is not the integral.  Here the integral is evaluated on a circle enclosing exactly the outer
# cluster and compared against that cluster's residue sum, and then shown continuous
# THROUGH the collision -- with the difference driven to 0 under refinement rather than
# accepted at a fixed 2% tolerance.
# ===========================================================================
Bcl = qlow(1 + 2 * t + 3 * t**3)
M_cl = 12


def contour_cluster(zval, Mv=M_cl, npts=400):
    r"""-(1/2 pi i) oint_Gamma B/(t^{M+1}(Q+z t^r)) dt on a circle enclosing the outer pair."""
    pr_ = outer_pair(zval)
    ctr = (pr_[0] + pr_[1]) / 2
    sep = max(abs(w - ctr) for w in pr_)
    # membership by distance: `w not in pr_` is unreliable for mpmath values and would
    # leave the cluster's own roots in `others`, corrupting the separation radius
    others = [w for w in d_roots(Qc_col, r, zval)
              if all(abs(w - o) > mp.mpf('1e-25') for o in pr_)]
    inner = min(abs(w - ctr) for w in others)
    # the contour must also exclude the order-(M+1) pole of the integrand at t = 0
    lim = min(inner, abs(ctr))
    rad = (sep + lim) / 2
    assert sep < rad < lim, (sep, rad, lim)

    def integrand(th_):
        w = ctr + rad * mp.e**(mp.mpc(0, 1) * th_)
        dw = mp.mpc(0, 1) * rad * mp.e**(mp.mpc(0, 1) * th_)
        return pval(Bcl, w) / (w**(Mv + 1) * (pval(Qc_col, w) + zval * w**r)) * dw

    val = mp.quad(integrand, mp.linspace(0, 2 * mp.pi, npts))
    return -val / (2 * mp.pi * mp.mpc(0, 1))


# away from the collision the cluster roots are simple, so the contour integral must equal the
# residue sum of `eq:simple-residue-amplitude` restricted to that cluster
# The contour has to enclose the whole cluster while excluding both the other roots and the
# t = 0 pole, so it exists only while the pair stays tight: at z = 1 the pair's half-spread
# (8.34) already exceeds the distance to the nearest other root (6.09).  Test where the
# contour is legitimate -- which is exactly the clustered regime `lem:contour-separation` is about.
z_ok = (mp.mpf('0.01'), mp.mpf('0.05'), mp.mpf('0.3'))
for z_ct in z_ok:
    res_sum = -sum(pval(Bcl, w) / (w**(M_cl + 1) * Dp_col(w, z_ct)) for w in outer_pair(z_ct))
    ctr_val = contour_cluster(z_ct)
    assert abs(ctr_val - res_sum) < mp.mpf('1e-15') * (1 + abs(res_sum)), \
        (z_ct, ctr_val, res_sum)
print(f'PASS: `eq:contour-separated-expansion` contour term = the cluster residue sum of `eq:simple-residue-amplitude` at z = '
      f'0.01, 0.05, 0.3 with a nonconstant B (relative agreement < 1e-15)')

# and it is holomorphic THROUGH the collision: the contour value converges as z -> z_c
# from both sides, while the individual residues diverge
at_zc = contour_cluster(z_c)
assert abs(at_zc) > 0, at_zc                          # evaluable AT the collision
rel = []
for dl in (mp.mpf('1e-2'), mp.mpf('1e-3'), mp.mpf('1e-4')):
    lo_v = contour_cluster(z_c * (1 - dl))
    hi_v = contour_cluster(z_c * (1 + dl))
    rel.append(abs(hi_v - lo_v) / abs(at_zc))         # relative, since |contour| ~ R_0^{-(M+1)}
# continuity, at the linear rate a holomorphic function must have: 10x in delta -> 10x here
assert all(rel[i + 1] < rel[i] / 3 for i in range(len(rel) - 1)), rel
slope_ct = (mp.log(rel[-1]) - mp.log(rel[0])) / (mp.log(mp.mpf('1e-4')) - mp.log(mp.mpf('1e-2')))
assert abs(slope_ct - 1) < mp.mpf('0.05'), slope_ct
assert rel[-1] < mp.mpf('1e-3'), rel
# by contrast the individual residues have no limit at z_c: they diverge
assert indiv_max(z_c * (1 + mp.mpf('1e-7'))) > 10 * indiv_max(z_c * (1 + mp.mpf('1e-3')))
print(f'PASS: `eq:contour-separated-expansion` is holomorphic through the nonprincipal collision: the two-sided '
      f'contour difference is {mp.nstr(rel[0], 3)} -> {mp.nstr(rel[-1], 3)} relative as '
      f'delta shrinks 1e-2 -> 1e-4 (log-log slope {mp.nstr(slope_ct, 4)} = 1), the contour '
      f'is evaluable AT z_c, and the individual residues diverge there')


# ===========================================================================
# The escaping root at the degree-drop parameter: reciprocal-coordinate threshold M > deg B - d + 1
# ===========================================================================
u = sp.symbols('u')
Qdd = (1 - t)**3
r_dd = 3
Bdd = 1 + t**5
d_dd = max(sp.Poly(sp.expand(Qdd), t).degree(), r_dd)              # = 3
degB_dd = sp.Poly(Bdd, t).degree()                                # = 5
qd = sp.Poly(sp.expand(Qdd), t).LC()                              # leading coeff of Q = -1
z_inf = -qd                                                      # = 1
Dhat = sp.expand(u**d_dd * Qdd.subs(t, 1 / u) + z)                # reciprocal coordinate
Bhat = sp.expand(u**degB_dd * Bdd.subs(t, 1 / u))
assert Dhat.subs({u: 0, z: z_inf}) == 0
assert sp.diff(Dhat, u).subs({u: 0, z: z_inf}) == sp.Poly(sp.expand(Qdd), t).all_coeffs()[1]  # q_{d-1} != 0
threshold = degB_dd - d_dd + 1                                    # = 3
for M in range(threshold, threshold + 3):
    expo = M + d_dd - 1 - degB_dd
    contrib = sp.limit((u**expo * Bhat / sp.diff(Dhat, u)).subs(z, z_inf), u, 0)
    if M > threshold:
        assert contrib == 0, (M, contrib)
    else:
        assert contrib != 0, (M, contrib)                         # M = deg B - d + 1: nonzero
print(f'PASS: escaping-root contribution vanishes at z_inf iff M > deg B - d + 1 = {threshold} '
      f'(M={threshold} gives {sp.limit((u**0 * Bhat / sp.diff(Dhat, u)).subs(z, z_inf), u, 0)})')

# Near z_inf the escaping root satisfies tau(z)|u_inf| <= sigma < 1, so after multiplication
# by tau^{M+1} its contribution is O(q^M) (with B = 1 here).  This is `lem:contour-separation`
# read on the escaping root alone: tau/|t_esc| <= sigma is exactly rho <= sigma R_Gamma for a
# circle the root lies outside.
Qc_dd = qlow(Qdd)
for zval in (mp.mpf('0.9'), mp.mpf('1.1')):                        # z_inf = 1
    rts = d_roots(Qc_dd, r_dd, zval)
    esc = max(rts, key=lambda w: abs(w))                          # escaping (largest modulus) root
    tau = abs(principal(rts))
    q = tau * abs(1 / esc)
    assert q < 1, (zval, q)
    scaled = [abs(1 / (esc**(M + 1) * (dval(Qc_dd, esc) + r_dd * zval * esc**(r_dd - 1)))) * tau**(M + 1)
              for M in (20, 40, 60)]
    assert scaled[1] < scaled[0] and scaled[2] < scaled[1]        # geometric decay
    assert scaled[2] < q**55                                      # bounded by q^M
    print(f'PASS: escaping root at z={mp.nstr(zval, 3)}: tau|u_inf| = {mp.nstr(q, 4)} < 1, '
          f'tau^(M+1) x contribution = O(q^M)')


# ===========================================================================
# `eq:Dprime-identity` at every denominator root: D'(t_j) = Q'(t_j) - r Q(t_j)/t_j (the general-t_j
# form belongs to section `sec:dominance`; `lem:amplitude-divisor`'s proof restates it for t_+ only), and `lem:amplitude-divisor`'s
# injectivity of theta |-> t_+(theta)
# ===========================================================================
Qc = qlow((1 - t) * (1 - t / 2) * (1 - t / 4))
r = 2
for zval in (mp.mpf('0.2'), mp.mpf('1'), mp.mpf('5')):
    for w in d_roots(Qc, r, zval):                                # every root is a denominator root
        lhs = dval(Qc, w) + r * zval * w**(r - 1)
        rhs = dval(Qc, w) - r * pval(Qc, w) / w
        assert abs(lhs - rhs) < mp.mpf('1e-30')
print('PASS: D\'(t_j) = Q\'(t_j) - r Q(t_j)/t_j at every denominator root')

args = []
for zval in [mp.mpf(s) for s in ('0.05', '0.1', '0.3', '1', '3', '10', '30', '100')]:
    args.append(abs(mp.arg(principal(d_roots(Qc, r, zval)))))
assert all(args[i] > args[i - 1] for i in range(1, len(args)))    # strictly monotone in z
assert 0 < args[0] and args[-1] < mp.pi / r
print('PASS: arg t_+(theta) strictly monotone in z (injective branch) => W has <= deg B zeros')


# ===========================================================================
# `lem:amplitude-divisor`, `eq:W-local-zero`: at an amplitude zero W = (theta-theta_j)^nu U_j (U_j != 0),
# and psi = arg W has bounded derivative through it (the real nu/(theta-theta_j) term of
# W'/W does not enter Im(W'/W) = psi').
# ===========================================================================
Qc = qlow((1 - t) * (1 - t / 2) * (1 - t / 4))
r = 2
theta_j = mp.mpf('0.8')
lo, hi = mp.mpf('0.05'), mp.mpf('100')
for _ in range(160):                                              # z_j with arg t_+(z_j) = theta_j
    mid = mp.sqrt(lo * hi)
    (lo, hi) = (mid, hi) if abs(mp.arg(principal(d_roots(Qc, r, mid)))) < theta_j else (lo, mid)
z_j = mp.sqrt(lo * hi)
tp = principal(d_roots(Qc, r, z_j))
Bc = [mp.re(tp)**2 + mp.im(tp)**2, -2 * mp.re(tp), mp.mpf(1)]      # real B with roots t_+, conj(t_+)
assert abs(sum(Bc[i] * tp**i for i in range(3))) < mp.mpf('1e-30')  # W(theta_j) = 0 exactly


def W_th(zval):
    pr = principal(d_roots(Qc, r, zval))
    return -sum(Bc[i] * pr**i for i in range(3)) / (dval(Qc, pr) + r * zval * pr**(r - 1)), abs(mp.arg(pr))


# `eq:W-local-zero`: |W| ~ |theta - theta_j|^nu with nu = 1; W/(theta-theta_j) -> nonzero limit
lp = []
for d in (mp.mpf('0.02'), mp.mpf('0.01'), mp.mpf('0.005'), mp.mpf('0.0025')):
    W, th = W_th(z_j * (1 + d))
    lp.append((abs(th - theta_j), abs(W)))
slopes = [(mp.log(lp[i + 1][1]) - mp.log(lp[i][1])) / (mp.log(lp[i + 1][0]) - mp.log(lp[i][0]))
          for i in range(len(lp) - 1)]
assert abs(slopes[-1] - 1) < mp.mpf('0.02')                       # nu = 1
assert lp[-1][1] / lp[-1][0] > mp.mpf('0.01')                     # U_j(theta_j) != 0
print(f'PASS: at an amplitude zero |W| ~ |theta-theta_j|^nu, nu = {mp.nstr(slopes[-1], 5)} '
      f'(local factorization `eq:W-local-zero`)')

# `eq:W-local-zero` at nu_j = 2, where the multiplicity is genuinely > 1.  With nu_j = 1 the
# exponent is indistinguishable from its absence, and so is the /nu_j in `eq:amplitude-deletion`'s
# deletion half-width e^{-cM/nu_j}: only at nu_j >= 2 does dividing by it widen the window.
tp_re, tp_im = mp.re(tp), mp.im(tp)
quad = [tp_re**2 + tp_im**2, -2 * tp_re, mp.mpf(1)]                # (t-t_+)(t-conj t_+)
Bc2 = [sum(quad[i] * quad[k - i] for i in range(max(0, k - 2), min(k, 2) + 1))
       for k in range(5)]                                          # its square: nu_j = 2
assert abs(sum(Bc2[i] * tp**i for i in range(5))) < mp.mpf('1e-28')          # W(theta_j) = 0
assert Bc2[0] > 0                                                  # B(0) != 0, admissible


def W_th2(zval):
    pr = principal(d_roots(Qc, r, zval))
    return (-sum(Bc2[i] * pr**i for i in range(5))
            / (dval(Qc, pr) + r * zval * pr**(r - 1)), abs(mp.arg(pr)))


lp2 = []
for d in (mp.mpf('0.02'), mp.mpf('0.01'), mp.mpf('0.005'), mp.mpf('0.0025')):
    W2, th2 = W_th2(z_j * (1 + d))
    lp2.append((abs(th2 - theta_j), abs(W2)))
slopes2 = [(mp.log(lp2[i + 1][1]) - mp.log(lp2[i][1])) / (mp.log(lp2[i + 1][0]) - mp.log(lp2[i][0]))
           for i in range(len(lp2) - 1)]
assert abs(slopes2[-1] - 2) < mp.mpf('0.02'), slopes2              # nu_j = 2
assert lp2[-1][1] / lp2[-1][0]**2 > mp.mpf('0.01')                 # U_j(theta_j) != 0
# and the /nu_j in `eq:amplitude-deletion` is load-bearing: at nu_j = 2 the window must be WIDER, because
# |W| ~ delta^2 needs delta >= e^{-cM/2} to clear a remainder of size e^{-cM}
c_w, M_w = mp.mpf('0.15'), 200
assert mp.e**(-c_w * M_w / 2) > mp.e**(-c_w * M_w)                 # wider at nu_j = 2
assert (mp.e**(-c_w * M_w / 2))**2 >= mp.e**(-c_w * M_w)           # clears the remainder
assert (mp.e**(-c_w * M_w))**2 < mp.e**(-c_w * M_w)                # omitting /nu_j would not
print(f'PASS: `eq:W-local-zero` at nu_j = 2 (B with a DOUBLE branch root): |W| ~ delta^'
      f'{mp.nstr(slopes2[-1], 5)}, U_j(theta_j) != 0; and `eq:amplitude-deletion`\'s /nu_j is needed -- '
      f'at nu_j = 2 the half-width e^(-cM/2) squares to >= e^(-cM) while e^(-cM) does not')

# `eq:phase-derivative-bound`: psi' stays bounded approaching theta_j from both sides (no 1/(theta-theta_j) blow-up)
psi_slopes = []
for side in (+1, -1):
    ds = [mp.mpf('0.03'), mp.mpf('0.02'), mp.mpf('0.013'), mp.mpf('0.008'), mp.mpf('0.005')]
    pts = [W_th(z_j * (1 + side * d)) for d in ds]
    psi_slopes += [abs(mp.arg(pts[i + 1][0] / pts[i][0]) / (pts[i + 1][1] - pts[i][1]))
                   for i in range(len(pts) - 1)]
assert max(psi_slopes) < mp.mpf('50')                             # bounded, no singular contribution
print(f'PASS: |psi\'| bounded through the amplitude zero (max {mp.nstr(max(psi_slopes), 5)}), '
      f'the real nu/(theta-theta_j) term does not enter psi\'')

# ===========================================================================
# `lem:amplitude-divisor`, `eq:W-endpoint-form`: upper-endpoint amplitude form for r > 1.
# There t_+ -> 0, so the derivative factor Q'(t_+) - r Q(t_+)/t_+ has a SIMPLE
# POLE: |D'(t_+) * t_+| -> r Q(0).  The quotient
# W = -t_+ B(t_+)/(t_+ Q'(t_+) - r Q(t_+)) has denominator -> -r Q(0) != 0, and
# since B(0) != 0 and t_+ = eta T(eta) (T(0) != 0), W = eta V(eta) with
# V(0) != 0 -- i.e. the endpoint exponent is p = 1.
# ===========================================================================
Qc_ue = qlow((1 - t) * (1 - t / 2) * (1 - t / 4))                 # Q(0) = 1 > 0
Q0_ue = pval(Qc_ue, mp.mpf(0))
Bc_ue = [mp.mpf(1), mp.mpf(0), mp.mpf(1)]                         # B = 1 + t^2, B(0) = 1 != 0
for r in (2, 3):
    rows = []
    for k in range(4, 12):                                        # z -> +inf drives theta -> pi/r
        zval = mp.mpf(10)**k
        pr = principal(d_roots(Qc_ue, r, zval))
        th = abs(mp.arg(pr)); eta = mp.pi / r - th
        deriv = dval(Qc_ue, pr) + r * zval * pr**(r - 1)          # Q'(t_+) + r z t_+^{r-1}
        rewritten = pr * dval(Qc_ue, pr) - r * pval(Qc_ue, pr)    # t_+ Q'(t_+) - r Q(t_+)
        W = -pval(Bc_ue, pr) / deriv
        rows.append((eta, abs(deriv), abs(deriv * pr), abs(rewritten), abs(W)))
    assert rows[-1][1] > mp.mpf('1e3')                            # |D'(t_+)| -> infinity: a pole
    assert abs(rows[-1][2] - r * Q0_ue) < mp.mpf('1e-3')          # |D'(t_+) * t_+| -> r Q(0)
    assert abs(rows[-1][3] - r * Q0_ue) < mp.mpf('1e-3')          # rewritten denom -> r Q(0) != 0
    slope = ((mp.log(rows[-1][4]) - mp.log(rows[-3][4]))
             / (mp.log(rows[-1][0]) - mp.log(rows[-3][0])))
    assert abs(slope - 1) < mp.mpf('0.02')                        # |W| ~ eta^1  => p = 1
    assert rows[-1][4] / rows[-1][0] > mp.mpf('0.01')             # W/eta -> V(0) != 0
    print(f'PASS: upper endpoint r={r}: D\'(t_+) is a pole (|D\'*t_+| -> r Q(0) = '
          f'{mp.nstr(r * Q0_ue, 6)}), rewritten denom -> -r Q(0) != 0, |W| ~ eta^'
          f'{mp.nstr(slope, 5)} => p = 1')


# ===========================================================================
# `lem:amplitude-divisor`, `eq:W-endpoint-form`: endpoint amplitude form W = delta^p V(delta) with
#     p = nu - (k-1),   k = the multiplicity of the endpoint collision,
# k = max{rho,2} at the lower endpoint and k = 2 at the finite (r = 1) upper
# endpoint.  B vanishing at the endpoint limit to order nu gives B(t_+) ~ delta^nu,
# while the derivative factor Q'(t_+) - r Q(t_+)/t_+ = -t_+^r g'(t_+) vanishes to
# order k-1, so |W| ~ delta^{nu-(k-1)}.  The integer p may be negative
# (|W| -> infinity), as the paper notes -- and it IS negative generically, since
# p = -1 whenever the collision is an ordinary double one with B nonvanishing.
#
# The exponent is nu - (k-1) with k = max{rho,2}, NOT nu - (rho-1): the two agree only when
# rho >= 2.  At rho = 1 the derivative factor still vanishes to order 1, and at the r = 1
# upper endpoint k = 2 regardless of rho, so both cases are tested separately below.
# ===========================================================================

# --- lower endpoint, repeated smallest zero (rho >= 2): k = rho ---
for rho, nu in ((3, 0), (3, 1), (3, 2), (2, 3)):
    Qc_le = qlow((1 - t)**rho)                                     # x1 = 1, multiplicity rho
    Bc_le = qlow((1 - t)**nu * (2 + t))                            # ord_{x1} B = nu, B(0) != 0
    assert Bc_le[0] != 0
    p_pred = nu - (max(rho, 2) - 1)
    for r in (1, 2):
        rows = []
        for k in range(5, 12):                                    # z -> 0+ drives theta -> 0 (lower endpoint)
            pr = principal(d_roots(Qc_le, r, mp.mpf(10)**(-k)))
            th = abs(mp.arg(pr))
            W = -pval(Bc_le, pr) / (dval(Qc_le, pr) + r * mp.mpf(10)**(-k) * pr**(r - 1))
            rows.append((th, abs(W)))
        slope = ((mp.log(rows[-1][1]) - mp.log(rows[-2][1]))
                 / (mp.log(rows[-1][0]) - mp.log(rows[-2][0])))
        assert abs(slope - p_pred) < mp.mpf('0.05'), (rho, nu, r, slope, p_pred)
    print(f'PASS: lower endpoint rho={rho} (k=rho), ord B = nu={nu}: |W| ~ theta^p '
          f'with p = nu-(k-1) = {p_pred} (measured {mp.nstr(slope, 5)})')


def endpoint_amplitude_slope(Qc_x, r, z_of, Bc_of, ks):
    r"""log-log slope of |W| against the angular distance, along z_of(k)."""
    rows = []
    for k in ks:
        zv = z_of(k)
        pr = principal(d_roots(Qc_x, r, zv))
        th = abs(mp.arg(pr))
        delta = th if th < mp.pi / (2 * r) else mp.pi / r - th
        W = -pval(Bc_of(pr), pr) / (dval(Qc_x, pr) + r * zv * pr**(r - 1))
        rows.append((delta, abs(W)))
    return ((mp.log(rows[-1][1]) - mp.log(rows[-2][1]))
            / (mp.log(rows[-1][0]) - mp.log(rows[-2][0])))


# --- lower endpoint, SIMPLE smallest zero (rho = 1): k = 2, so p = nu - 1.
# The naive p = nu - (rho-1) = nu would be one too large; this is the case that
# would have caught the paper's error.  Here t_a > x1 with Q(t_a) != 0 and
# a = g(t_a) > 0, so the endpoint is approached as z -> a+.
for Qexpr in [(1 - t) * (1 - t / 2) * (1 - t / 4), (1 - t) * (1 - t / 3)]:
    Qc_s = qlow(Qexpr)
    for r in (1, 2):
        if max(sp.Poly(Qexpr, t).degree(), r) <= 1:
            continue
        # for r = 1 the default bracket 1e6 lies ABOVE the finite b, where the pair
        # is real again, so bracket with a point known to be inside I_{Q,r}
        a_s = lower_endpoint_bisect(Qc_s, r, zhi=interior_z(Qc_s, r))
        t_a_s = principal(d_roots(Qc_s, r, a_s * (1 + mp.mpf('1e-30'))))
        t_a_s = mp.re(t_a_s)                                      # real double root at z = a
        assert t_a_s > 0 and abs(pval(Qc_s, t_a_s)) > mp.mpf('1e-6')   # rho = 1 => Q(t_a) != 0
        for nu in (0, 1):
            # B with a zero of order nu at t_a (numeric coefficients), B(0) != 0
            Bc = [mp.mpf(1)] if nu == 0 else [-t_a_s, mp.mpf(1)]
            assert abs(pval(Bc, mp.mpf(0))) > mp.mpf('1e-12')
            slope = endpoint_amplitude_slope(
                Qc_s, r, lambda k: a_s * (1 + mp.mpf(10)**(-k)),
                lambda pr: Bc, range(6, 13))
            p_pred = nu - 1                                       # k = 2
            assert abs(slope - p_pred) < mp.mpf('0.06'), (Qexpr, r, nu, slope, p_pred)
            assert abs(slope - nu) > mp.mpf('0.5')                # refutes p = nu
        print(f'PASS: lower endpoint rho=1 (k=2), r={r}: |W| ~ delta^(nu-1); the naive '
              f'p = nu-(rho-1) = nu is refuted (measured {mp.nstr(slope, 5)} for nu=1)')


# --- finite upper endpoint (r = 1): k = 2, so p = nu_b - 1, with nu_b the order of
# B at t_b.  rho plays no role here, since k = 2 at a finite upper endpoint.
for Qexpr in [(1 - t) * (1 - t / 2), (1 - t)**3 * (1 - t / 4)]:
    Qc_u = qlow(Qexpr)
    b_u = upper_endpoint_bisect(Qc_u, 1)
    t_b_u = mp.re(principal(d_roots(Qc_u, 1, b_u * (1 - mp.mpf('1e-30')))))
    assert t_b_u < 0
    for nu_b in (0, 1):
        Bc = [mp.mpf(1)] if nu_b == 0 else [-t_b_u, mp.mpf(1)]
        assert abs(pval(Bc, mp.mpf(0))) > mp.mpf('1e-12')          # B(0) != 0
        slope = endpoint_amplitude_slope(
            Qc_u, 1, lambda k: b_u * (1 - mp.mpf(10)**(-k)), lambda pr: Bc, range(6, 13))
        assert abs(slope - (nu_b - 1)) < mp.mpf('0.06'), (Qexpr, nu_b, slope)
    print(f'PASS: finite upper endpoint r=1 (k=2): |W| ~ delta^(nu_b-1), independent '
          f'of rho (measured {mp.nstr(slope, 5)} for nu_b=1)')


# ===========================================================================
# `lem:amplitude-divisor`, upper endpoint for r > 1: t_+ = eta T(eta) with T of class C^1 and
#     T(0) = r e^{i pi/r} / (lambda sin(pi/r)),   lambda = -Q'(0)/Q(0),
# via eta = -(1/r) arg Q(t_+) and eta'(0) = (lambda/r) Q(0)^{1/r} sin(pi/r) > 0
# in the local parameter w = z^{-1/r} (the paper renamed this from varsigma,
# which was sigma's variant glyph beside sigma's own use in the same section).
# ===========================================================================
for Qexpr, r in [((1 - t) * (1 - t / 2) * (1 - t / 3), 2), ((1 - t) * (1 - t / 2), 3),
                 ((1 - t)**2 * (1 - t / 3), 4)]:
    Qc_i = qlow(Qexpr)
    Q0_i = mp.mpf(sp.Poly(Qexpr, t).nth(0))
    lam = -mp.mpf(sp.Poly(sp.diff(Qexpr, t), t).nth(0)) / Q0_i
    assert lam > 0
    eta_closed = (lam / r) * Q0_i**(mp.mpf(1) / r) * mp.sin(mp.pi / r)
    T_closed = r * mp.exp(1j * mp.pi / r) / (lam * mp.sin(mp.pi / r))
    assert eta_closed > 0
    for e in (8 * r, 10 * r):
        zv = mp.mpf(10)**e
        rts = d_roots(Qc_i, r, zv)
        small = sorted(rts, key=lambda w: abs(w))[:r]              # only r roots collapse to 0
        pr = min(small, key=lambda w: abs(mp.arg(w) - mp.pi / r))
        w_par = zv**(-mp.mpf(1) / r)
        eta = mp.pi / r - mp.arg(pr)
        # eta = -(1/r) arg Q(t_+)
        assert abs(-mp.arg(pval(Qc_i, pr)) / r - eta) < mp.mpf('1e-20')
        assert abs(eta / w_par - eta_closed) / eta_closed < mp.mpf('1e-6')
        assert abs(pr / eta - T_closed) / abs(T_closed) < mp.mpf('1e-6')
    print(f'PASS: upper endpoint r={r}: eta = -(1/r) arg Q(t_+), '
          f"eta'(0) = {mp.nstr(eta_closed, 8)}, T(0) = {mp.nstr(T_closed, 8)} != 0")


# ===========================================================================
# `thm:FT-geometry`: the circle comparison is stated ONCE in the paper, for real
# t_e != 0 with Q(t_e) + z_e t_e^r = 0, and applied at t_e = t_a > 0 (z_e = a)
# and at t_e = t_b < 0 (z_e = b, r = 1):
#     |t-x_j|^2 - |t_e-x_j|^2 = 2 x_j (t_e - Re t)   has the sign of t_e,
# so |Q(t)| != |Q(t_e)| = |z_e| |t_e|^r = |z_e t^r| and t is not a zero of
# Q(t) + z_e t^r.  Both directions are instances of the one sign rule: the
# lower endpoint gives |Q(t)| > |Q(t_a)|, the upper gives |Q(t)| < |Q(t_b)|.
# Sign rule: |Re t| <= |t| = |t_e| with equality only for real t, and t != t_e,
# so t_e - Re t is nonzero with the sign of t_e.
# Also: the collision at t_b is exactly double (Q''(t_b) != 0, zeros of Q'' positive).
# ===========================================================================
# --- the unified claim at the LOWER endpoint, t_e = t_a > 0, z_e = a ---------
for Qexpr, r_lo in [((1 - t) * (1 - t / 2) * (1 - t / 4), 1),
                    ((1 - t) * (1 - t / 3) * (1 - t / 5), 1),
                    ((1 - t) ** 2 * (1 - t / 3), 1),
                    ((1 - t) ** 2 * (1 - t / 3), 2),
                    ((1 - t) ** 3 * (1 - t / 4), 3),
                    ((1 - t) * (1 - t / 7), 4)]:
    Qc_l = qlow(Qexpr)
    roots_x = []
    for rt, m in sp.roots(sp.Poly(Qexpr, t)).items():
        roots_x += [mp.mpf(sp.nsimplify(rt))] * m
    assert all(x > 0 for x in roots_x)
    # t_a = smallest positive critical point of g = -Q/t^r; a = g(t_a)
    S_l = sp.expand(r_lo * Qexpr - t * sp.diff(Qexpr, t))
    hlow_l = qlow(S_l)
    while len(hlow_l) > 1 and hlow_l[-1] == 0:
        hlow_l.pop()
    crit = [mp.re(w) for w in mp.polyroots(                          # mpmath, not complex()
        [mp.mpf(sp.Rational(c)) for c in reversed(hlow_l)], maxsteps=3000, extraprec=400)
        if abs(mp.im(w)) < mp.mpf('1e-30') and mp.re(w) > mp.mpf('1e-30')]
    assert crit, (Qexpr, r_lo)
    t_a_l = min(crit)
    a_l = -pval(Qc_l, t_a_l) / t_a_l ** r_lo
    # `eq:ab-def` with the dichotomy in `thm:FT-geometry`'s proof: a >= 0 always, and a = 0 EXACTLY when the
    # smallest zero of Q is repeated (rho >= 2), where also t_a = x_1.  A bare `a_l >= 0`
    # is wrong here: at rho >= 2 the true value is 0 and roundoff puts it either side
    # (measured -6.7e-52 for (1-t)^2(1-t/3)).  Split on rho instead.
    rho_l = sum(1 for x in roots_x if abs(x - min(roots_x)) < mp.mpf('1e-30'))
    tol_l = mp.mpf('1e-40')
    assert t_a_l > 0
    if rho_l >= 2:
        assert abs(t_a_l - min(roots_x)) < mp.mpf('1e-25'), (Qexpr, r_lo, t_a_l)   # t_a = x_1
        assert abs(a_l) < tol_l, (Qexpr, r_lo, a_l)                               # a = 0
        a_l = mp.mpf(0)                                                # exact value, not roundoff
    else:
        assert a_l > tol_l, (Qexpr, r_lo, a_l)                                    # a > 0
    assert abs(pval(Qc_l, t_a_l) + a_l * t_a_l ** r_lo) < mp.mpf('1e-35')
    Qta = pval(Qc_l, t_a_l)
    # the "= |z_e| |t_e|^r" step of the unified statement
    assert abs(abs(Qta) - abs(a_l) * t_a_l ** r_lo) < mp.mpf('1e-35')
    w_ident, w_gap, w_nozero = mp.mpf(0), -mp.inf, mp.inf
    for j in range(1, 721):
        w = t_a_l * mp.exp(1j * 2 * mp.pi * j / 720)
        if abs(w - t_a_l) < mp.mpf('1e-25'):
            continue
        for x in roots_x:
            w_ident = max(w_ident, abs((abs(w - x) ** 2 - abs(t_a_l - x) ** 2)
                                       - 2 * x * (t_a_l - mp.re(w))))
            assert 2 * x * (t_a_l - mp.re(w)) > 0             # sign of t_e, t_e > 0
        Qw = pval(Qc_l, w)
        w_gap = max(w_gap, -(abs(Qw) - abs(Qta)))             # want |Q(t)| > |Q(t_a)|
        w_nozero = min(w_nozero, abs(abs(Qw) - abs(a_l * w ** r_lo)))
    assert w_ident < mp.mpf('1e-30'), w_ident
    assert w_gap < 0, w_gap                                   # STRICT
    assert w_nozero > mp.mpf('1e-8'), w_nozero                # no zero on the circle
    print(f'PASS: lower endpoint |t|=t_a: unified identity exact to '
          f'{mp.nstr(w_ident, 3)}, sign(t_e)>0 gives |Q(t)|-|Q(t_a)| >= '
          f'{mp.nstr(-w_gap, 3)} > 0, no zero on the circle (r={r_lo})')

# --- the same claim at the UPPER endpoint, t_e = t_b < 0, z_e = b, r = 1 -----
for Qexpr in [(1 - t) * (1 - t / 2), (1 - t) * (1 - t / 3) * (1 - t / 5),
              (1 - t)**2 * (1 - t / 3), (1 - t)**3 * (1 - t / 4)]:
    Qc_c = qlow(Qexpr)
    roots_x = []
    for rt, m in sp.roots(sp.Poly(Qexpr, t)).items():
        roots_x += [mp.mpf(sp.nsimplify(rt))] * m
    assert all(x > 0 for x in roots_x)
    b_c = upper_endpoint_bisect(Qc_c, 1)
    t_b_c = mp.re(principal(d_roots(Qc_c, 1, b_c * (1 - mp.mpf('1e-30')))))
    assert t_b_c < 0
    Qtb = pval(Qc_c, t_b_c)
    worst_gap, worst_zero, worst_ident = -mp.inf, mp.inf, mp.mpf(0)
    for j in range(1, 361):
        w = abs(t_b_c) * mp.exp(1j * 2 * mp.pi * j / 360)
        if abs(w - t_b_c) < mp.mpf('1e-20'):
            continue
        for x in roots_x:
            worst_ident = max(worst_ident,
                              abs((abs(w - x)**2 - abs(t_b_c - x)**2)
                                  - 2 * x * (t_b_c - mp.re(w))))
            assert 2 * x * (t_b_c - mp.re(w)) < 0                  # the sign claim
        Qw = pval(Qc_c, w)
        worst_gap = max(worst_gap, abs(Qw) - abs(Qtb))
        worst_zero = min(worst_zero, abs(abs(Qw) - abs(b_c * w)))
    assert worst_ident < mp.mpf('1e-20'), worst_ident
    assert worst_gap < 0, worst_gap                               # STRICT
    assert worst_zero > mp.mpf('1e-6'), worst_zero                # no zero on the circle
    Q2c = qlow(sp.diff(Qexpr, t, 2))
    if len(Q2c) > 1:
        # the zeros of Q'' are positive (`thm:FT-geometry`, proof); mpmath, not complex()
        q2t = list(Q2c)
        while len(q2t) > 1 and q2t[-1] == 0:
            q2t.pop()
        assert all(mp.re(w) > 0 for w in mp.polyroots(
            [mp.mpf(sp.Rational(c)) for c in reversed(q2t)], maxsteps=3000, extraprec=400)
            if abs(mp.im(w)) < mp.mpf('1e-30'))
    assert abs(pval(Q2c, t_b_c)) > mp.mpf('1e-6')                  # => collision exactly double
    print(f'PASS: r=1 upper endpoint |t|=|t_b|: reversed identity exact to '
          f'{mp.nstr(worst_ident, 3)}, |Q(t)|-|Q(t_b)| <= {mp.nstr(worst_gap, 3)} < 0, '
          f'no zero on the circle, collision exactly double')




# ===========================================================================
# `eq:endpoint-fixed-gap`: the FIXED modulus gap for zeros OUTSIDE the endpoint cluster
# ===========================================================================
# `eq:endpoint-linear-gap` gives only |zeta_j| >= 1 + c*delta, a gap that COLLAPSES as delta -> 0.
# At theta ~ h/M that yields e^{-ch}, a constant, against |W| ~ theta^p -> 0, so it
# is insufficient for the zeros outside the cluster; `eq:endpoint-fixed-gap` supplies a FIXED gap
# for those.  Critically, `eq:endpoint-linear-gap` is VACUOUS at rho = 2 (see the next block), so
# `eq:endpoint-fixed-gap` carries the entire lower-endpoint nonprincipal estimate there.
#
# The test needs Q with a repeated smallest zero AND a further zero -- a pure
# (1-t)^rho has every zero in the cluster and cannot exhibit `eq:endpoint-fixed-gap` at all.
for (Qexpr_fg, r_fg, x2_over_x1) in [
    ((1 - t)**2 * (1 - t / 3), 2, mp.mpf(3)),                     # rho=2, x2=3
    ((1 - t)**2 * (1 - t / 4), 2, mp.mpf(4)),                     # rho=2, x2=4
    ((1 - t)**3 * (1 - t / 5), 2, mp.mpf(5)),                     # rho=3, x2=5
]:
    Qc_fg = qlow(sp.expand(Qexpr_fg))
    seq = []
    for k in range(3, 10):
        zval = mp.mpf(10)**(-k)
        rts = d_roots(Qc_fg, r_fg, zval)
        pr = principal(rts)
        tau = abs(pr)
        mods = sorted(abs(w) / tau for w in rts)
        # cluster members sit at |zeta| -> 1; the outside zero at |zeta| -> x2/x1
        outside = [m for m in mods if m > (1 + x2_over_x1) / 2]
        assert outside, (r_fg, k, mods)
        seq.append((zval, min(outside)))
    gaps = [g for _, g in seq]
    # (i) the gap does NOT collapse: bounded away from 1 uniformly
    assert min(gaps) > 1 + (x2_over_x1 - 1) / 2, gaps
    # (ii) it converges to the fixed ratio x2/x1 predicted by `eq:endpoint-fixed-gap`'s proof
    assert abs(gaps[-1] - x2_over_x1) < mp.mpf('0.02'), (gaps[-1], x2_over_x1)
    # (iii) and it is NOT of the collapsing form 1 + c*theta: the increment over the
    #       last decade is far smaller than the distance from 1
    assert abs(gaps[-1] - gaps[-2]) < (gaps[-1] - 1) / 100, (gaps[-2], gaps[-1])
    print(f'PASS: `eq:endpoint-fixed-gap` fixed non-cluster gap: |zeta| -> {mp.nstr(gaps[-1], 8)} '
          f'= x2/x1 = {mp.nstr(x2_over_x1, 4)} (Q={sp.factor(Qexpr_fg)}, r={r_fg}), '
          f'bounded away from 1, not 1 + c*theta')


# ===========================================================================
# `eq:endpoint-linear-gap` is VACUOUS at rho = 2 -- why `eq:endpoint-fixed-gap` is load-bearing
# ===========================================================================
# The linear coefficient (cos(pi/rho) - Re omega_k)/sin(pi/rho) vanishes for EVERY
# index when rho = 2, and the two principal indices exhaust the cluster, so `eq:endpoint-linear-gap`
# constrains no root at all.  For rho >= 3 it covers exactly rho - 2 roots.
for rho_v in (2, 3, 4, 5, 6):
    omk_v = [mp.expj((2 * k - 1) * mp.pi / rho_v) for k in range(1, rho_v + 1)]
    coeffs_v = [(mp.cos(mp.pi / rho_v) - mp.re(w)) / mp.sin(mp.pi / rho_v) for w in omk_v]
    zero_v = [i for i, c in enumerate(coeffs_v) if abs(c) < mp.mpf('1e-25')]
    pos_v = [i for i, c in enumerate(coeffs_v) if c > mp.mpf('1e-25')]
    assert len(zero_v) == 2, (rho_v, zero_v)                      # exactly the principal pair
    assert len(pos_v) == rho_v - 2, (rho_v, pos_v)                 # rho-2 governed roots
    if rho_v == 2:
        assert pos_v == [], pos_v                                  # `eq:endpoint-linear-gap` covers NOTHING
print('PASS: `eq:endpoint-linear-gap` governs exactly rho-2 cluster roots; at rho=2 it is vacuous '
      '(strictly-positive set empty), so `eq:endpoint-fixed-gap` carries the whole nonprincipal estimate')


# ===========================================================================
# `eq:W-def`: the principal pair is simple -- g'(t_+) != 0 for EVERY theta
# ===========================================================================
# The denominator of `eq:W-def` equals -t_+^r g'(t_+).  A double principal root would
# force t_+ Q'(t_+) = r Q(t_+), i.e. t_+ Q'/Q = r, a REAL value.  But for Im t > 0,
#     Im( t Q'(t)/Q(t) ) = Im sum_j t/(t-x_j) = -Im(t) sum_j x_j/|t-x_j|^2 < 0,
# so this cannot happen anywhere in the open upper half-plane.
xs_sym = sp.symbols('X1:6', positive=True)
for n_sym in range(1, 6):
    Qs = sp.prod([(1 - t / xx) for xx in xs_sym[:n_sym]])
    lhs = sp.simplify(t * sp.diff(Qs, t) / Qs)
    rhs = sum(t / (t - xx) for xx in xs_sym[:n_sym])
    assert sp.simplify(sp.together(lhs - rhs)) == 0, n_sym          # t Q'/Q = sum t/(t-x_j)
    us, vs = sp.symbols('u v', real=True)
    im_expr = sp.simplify(sp.im(sp.expand(rhs.subs(t, us + sp.I * vs))))
    claimed = -vs * sum(xx / ((us - xx)**2 + vs**2) for xx in xs_sym[:n_sym])
    assert sp.simplify(sp.expand(im_expr - claimed)) == 0, n_sym    # the sign identity
print('PASS: Im(t Q\'/Q) = -Im(t) sum_j x_j/|t-x_j|^2 (exact, n=1..5), so it is < 0 '
      'in the open upper half-plane')

# The two identities `eq:W-def` and `eq:W-on-g` rest on:
#     Q'(t) + r z t^{r-1} = -t^r g'(t)   at z = -Q(t)/t^r,   and   t Q'(t) - r Q(t) = -t^{r+1} g'(t).
# Both are exact in t over a free Q, checked symbolically here.
zsym = sp.Symbol('zsym')
for n_id in range(1, 5):
    Qi = sp.prod([(1 - t / xx) for xx in xs_sym[:n_id]])
    for r_id in (1, 2, 3, 4):
        g_id = -Qi / t**r_id
        # second identity: t Q' - r Q = -t^{r+1} g'
        assert sp.simplify(sp.expand(
            (t * sp.diff(Qi, t) - r_id * Qi) + t**(r_id + 1) * sp.diff(g_id, t))) == 0, \
            (n_id, r_id, 'tQ - rQ identity')
        # first identity, on the denominator-zero locus z = -Q/t^r
        assert sp.simplify(sp.expand(
            (sp.diff(Qi, t) + r_id * (-Qi / t**r_id) * t**(r_id - 1))
            + t**r_id * sp.diff(g_id, t))) == 0, (n_id, r_id, 'D-prime identity')
print("PASS: `eq:W-def` denominator identities exact over a free Q (n=1..4, r=1..4): "
      "Q'(t) + r z t^(r-1) = -t^r g'(t) at z = -Q/t^r, and t Q'(t) - r Q(t) = -t^(r+1) g'(t)")

# numerically along the actual branch: sweep z through I_{Q,r} (identified by the
# presence of a min-modulus conjugate pair) and check both the sign claim and that
# the derivative factor of `eq:W-def` stays bounded away from zero.
for (Qexpr_s, r_s) in [((1 - t), 3), ((1 - t)**2, 2), ((1 - t)**2 * (1 - t / 3), 2),
                       ((1 - t)**3, 3), ((1 - t) * (1 - t / 2) * (1 - t / 4), 2)]:
    Qc_s = qlow(sp.expand(Qexpr_s))
    worst_s, nsamp = None, 0
    for e10 in range(-6, 7):
        for mant in (mp.mpf(1), mp.mpf(3)):
            zv = mant * mp.mpf(10)**e10
            # skip the degree-drop parameter z_inf = -q_d, where the
            # leading t-coefficient of Q + z t^r vanishes and D drops degree.
            d_s = max(len(Qc_s) - 1, r_s)
            lead_s = (mp.mpf(Qc_s[d_s]) if d_s < len(Qc_s) else mp.mpf(0))                 + (zv if r_s == d_s else mp.mpf(0))
            if abs(lead_s) < mp.mpf('1e-25'):
                continue
            if not has_conjugate_pair(Qc_s, r_s, zv):
                continue
            pr = principal(d_roots(Qc_s, r_s, zv))
            if abs(mp.im(pr)) < mp.mpf('1e-25'):
                continue
            # principal() may return either member of the conjugate pair; the sign
            # claim is about the OPEN UPPER half-plane, which is where t_+ lives.
            if mp.im(pr) < 0:
                pr = mp.conj(pr)
            assert mp.im(pr) > 0
            Qv, Qdv = pval(Qc_s, pr), dval(Qc_s, pr)
            assert abs(Qv) > mp.mpf('1e-30'), (Qexpr_s, r_s, zv)    # Q(t_+) != 0 off the real axis
            assert (pr * Qdv / Qv).imag < 0, (Qexpr_s, r_s, zv)     # Im(t Q'/Q) < 0
            dfac = abs(pr * Qdv - r_s * Qv)                         # = |t_+^{r+1} g'(t_+)|
            worst_s = dfac if worst_s is None else min(worst_s, dfac)
            nsamp += 1
    assert nsamp >= 5, (Qexpr_s, r_s, nsamp)
    assert worst_s > mp.mpf('1e-20'), (Qexpr_s, r_s, worst_s)
    print(f'PASS: `eq:W-def` well defined ({nsamp} branch samples): '
          f'min |t_+ Q\'(t_+) - r Q(t_+)| = {mp.nstr(worst_s, 6)} > 0 '
          f'(Q={sp.factor(Qexpr_s)}, r={r_s})')


# ===========================================================================
# `eq:principal-finite-endpoint-regularity`: t_+ = t_+(0^+) + gamma_+ delta + O(delta^2), gamma_+ != 0  (C^1)
# and the real-singular-part mechanism behind the phase bound `eq:phase-derivative-bound`
# ===========================================================================
# The paper asks only for C^1 regularity of t_+ at a finite endpoint -- NOT
# analyticity (Forgacs-Tran's Lemma 2 is analytic on the OPEN interval and its
# Jacobian degenerates at theta = 0).  What the phase bound consumes is:
#   (i)  a first-order expansion with gamma_+ != 0, so that w = t_+ - t_+(0^+)
#        behaves like gamma_+ delta (log-log slope 1, not 1/2 and not 2); and
#   (ii) that a factor vanishing to order k contributes k*w'/w = k/delta + O(1)
#        to W'/W, whose singular part is REAL and therefore drops out of
#        Im(W'/W) = psi'.  So psi' stays bounded even though |W| -> 0 or infinity.
for (Qexpr_c1, r_c1, x1_c1) in [((1 - t)**2 * (1 - t / 3), 2, mp.mpf(1)),
                                ((1 - t)**3 * (1 - t / 5), 2, mp.mpf(1)),
                                ((1 - t)**2, 3, mp.mpf(1))]:
    Qc_c1 = qlow(sp.expand(Qexpr_c1))
    ths, ws = [], []
    for k in range(4, 11):
        zv = mp.mpf(10)**(-k)
        rts = d_roots(Qc_c1, r_c1, zv)
        pr = principal(rts)
        if mp.im(pr) < 0:
            pr = mp.conj(pr)
        th = mp.arg(pr)
        if th <= 0:
            continue
        ths.append(th); ws.append(pr - x1_c1)
    assert len(ths) >= 5, (Qexpr_c1, len(ths))
    # (i) |w| ~ |gamma_+| * delta : log-log slope 1
    sl = (mp.log(abs(ws[-1])) - mp.log(abs(ws[-2]))) / (mp.log(ths[-1]) - mp.log(ths[-2]))
    assert abs(sl - 1) < mp.mpf('0.02'), (Qexpr_c1, sl)
    gam = [w / th for w, th in zip(ws, ths)]
    assert abs(gam[-1]) > mp.mpf('1e-6'), gam[-1]                  # gamma_+ != 0
    assert abs(gam[-1] - gam[-2]) < abs(gam[-1]) / 50, (gam[-2], gam[-1])   # converges
    # (ii) the O(delta^2) remainder: (w - gamma_+ delta)/delta^2 stays bounded
    g0 = gam[-1]
    rem = [abs(w - g0 * th) / th**2 for w, th in zip(ws, ths)]
    assert max(rem[-4:]) < mp.mpf('50') * (abs(g0) + 1), rem[-4:]
    print(f'PASS: `eq:principal-finite-endpoint-regularity` C^1 expansion: |t_+ - x_1| ~ delta^{mp.nstr(sl, 5)}, '
          f'gamma_+ -> {mp.nstr(g0, 6)} != 0, O(delta^2) remainder bounded '
          f'(Q={sp.factor(Qexpr_c1)}, r={r_c1})')

    # the mechanism: Re(W'/W) blows up like p/delta while Im(W'/W) = psi' stays bounded
    Bc_c1 = qlow(sp.expand((1 - t)**2 * (2 + t)))       # nu = 2, so p = nu-(k-1), k = max{rho,2}
    def W_of_z(zv, Qc=Qc_c1, Bc=Bc_c1, r=r_c1):
        rts = d_roots(Qc, r, zv)
        pr = principal(rts)
        if mp.im(pr) < 0:
            pr = mp.conj(pr)
        return -pval(Bc, pr) / (dval(Qc, pr) + r * zv * pr**(r - 1)), mp.arg(pr)
    logder, magpairs = [], []
    for k in range(4, 9):
        z1, z2 = mp.mpf(10)**(-k), mp.mpf(10)**(-k) * mp.mpf('1.0001')
        W1, th1 = W_of_z(z1)
        W2, th2 = W_of_z(z2)
        if th1 <= 0 or th2 <= 0 or abs(th2 - th1) < mp.mpf('1e-40'):
            continue
        d_log = (mp.log(W2) - mp.log(W1)) / (th2 - th1)             # W'/W in theta
        logder.append((min(th1, th2), d_log))
        magpairs.append((th1, abs(W1)))
    assert len(logder) >= 3, logder
    # p = the endpoint exponent, read off as the log-log slope of |W| vs delta
    p_meas = ((mp.log(magpairs[-1][1]) - mp.log(magpairs[-2][1]))
              / (mp.log(magpairs[-1][0]) - mp.log(magpairs[-2][0])))
    # THE MECHANISM: the singular part of W'/W is delta -> p/delta, and it is REAL.
    # (p may be 0, in which case W'/W is simply bounded -- the assert covers both.)
    re_scaled = [mp.re(d) * th for th, d in logder]
    assert abs(re_scaled[-1] - p_meas) < mp.mpf('0.05') + abs(p_meas) / 20, \
        (p_meas, re_scaled[-1])
    # Im part -- which IS psi' -- stays bounded as delta -> 0, and in particular
    # carries NO 1/delta singularity: delta * Im(W'/W) -> 0.
    im_vals = [abs(mp.im(d)) for _, d in logder]
    im_scaled = [abs(mp.im(d) * th) for th, d in logder]
    assert max(im_vals) < mp.mpf('1e3'), im_vals
    assert im_scaled[-1] < mp.mpf('0.01'), im_scaled                # no real 1/delta in Im
    print(f'PASS: `eq:phase-derivative-bound` mechanism: p = {mp.nstr(p_meas, 4)}, '
          f'delta*Re(W\'/W) -> {mp.nstr(re_scaled[-1], 4)} = p (singular part REAL), '
          f'while psi\' = Im(W\'/W) stays bounded ({mp.nstr(max(im_vals), 4)}) with '
          f'delta*Im -> {mp.nstr(im_scaled[-1], 3)}')


# ===========================================================================
# `lem:amplitude-divisor`, `eq:W-endpoint-form`: the finite-endpoint LOCAL PARAMETER.
#
# The endpoint regularity of t_+ is proved through a REAL one-sided parameter
# y >= 0 with z - z_e = eps y^k, eps = sgn(z - z_e) on the interior side, the
# sign absorbed into the analytic factor Lambda = (-eps t^r/G(t))^{1/k} so that
# the prefactor keeps omega^k = 1.  Here G is the cofactor of the near-endpoint
# factorization Q(t) + z_e t^r = (t - t_e)^k G(t), G(t_e) != 0 -- NOT the Laurent
# division quotient S(t,z) of `lem:laurent-reduction`, which is a different function.
#
# The tests pin every step AND assert that the two rejected alternatives are
# refuted, so a regression to either fails loudly:
#   (i)  a COMPLEX parameter v with v^k = z - z_e is imaginary at the finite
#        upper endpoint (eps = -1), where d t/d v comes out REAL for a
#        NONREAL branch -- so "a branch with real leading coefficient is real"
#        has no content there.  (This rejected v is local to this block and is
#        NOT the paper's w = z^{-1/r}, which parameterizes the r > 1
#        upper endpoint, where t_+ -> 0 rather than to a finite t_e.)
#   (ii) absorbing the sign into the prefactor instead would need mu^k = -1,
#        which at k = 2 is mu = +-i, not a kth root of unity.
# ===========================================================================
def q_from_roots(xs):
    r"""Q(t) = prod_j (1 - t/x_j), coefficients low->high, so Q(0) = 1 > 0."""
    c = [mp.mpf(1)]
    for x in xs:
        nxt = [mp.mpf(0)] * (len(c) + 1)
        for i, co in enumerate(c):
            nxt[i] += co
            nxt[i + 1] += -co / mp.mpf(x)
        c = nxt
    return c


def crit_low(Qlow, r):
    r"""r Q(t) - t Q'(t), coefficients low->high: entry i is (r - i) Q_i."""
    return [(r - i) * co for i, co in enumerate(Qlow)]


def endpoint_data(Qlow, r, side):
    r"""(t_e, z_e, eps, k, G(t_e)) at a finite endpoint of I_{Q,r}.

    Lower: t_a = smallest positive zero of r Q - t Q'.  Upper (r = 1 only):
    t_b = the unique negative zero.  k = multiplicity of t_e as a zero of the
    limiting denominator Q + z_e t^r, and G(t_e) = D^{(k)}(t_e)/k! its cofactor
    in Q(t) + z_e t^r = (t - t_e)^k G(t).
    """
    cr = crit_low(Qlow, r)
    while len(cr) > 1 and abs(cr[-1]) < mp.mpf('1e-40'):
        cr = cr[:-1]
    rts = mp.polyroots(list(reversed(cr)), maxsteps=3000, extraprec=300)
    real = [mp.re(w) for w in rts if abs(mp.im(w)) < mp.mpf('1e-30')]
    if side == 'lower':
        cand = sorted(w for w in real if w > mp.mpf('1e-30'))
        assert cand, 'no positive critical point of g'
        t_e = cand[0]
    else:
        assert r == 1, 'the finite upper endpoint occurs only at r = 1'
        cand = [w for w in real if w < -mp.mpf('1e-30')]
        assert len(cand) == 1, ('negative critical point of g is not unique', cand)
        t_e = cand[0]
    z_e = -pval(Qlow, t_e) / t_e**r
    eps = mp.mpf(1) if side == 'lower' else mp.mpf(-1)
    # D(t) = Q(t) + z_e t^r, low->high; differentiate until nonzero at t_e
    dg = max(len(Qlow) - 1, r)
    D = [mp.mpf(0)] * (dg + 1)
    for i, co in enumerate(Qlow):
        D[i] += co
    D[r] += z_e
    scale = max(abs(c) for c in D)
    kk, Dk = 0, D
    while abs(pval(Dk, t_e)) < mp.mpf('1e-35') * max(1, scale):
        kk += 1
        Dk = [Dk[i] * i for i in range(1, len(Dk))]
    G_te = pval(Dk, t_e) / mp.factorial(kk)
    return t_e, z_e, eps, kk, G_te


R9_CONFIGS = [                       # (label, zeros of Q with multiplicity, r)
    ('Q=(1-t)(1-t/2)(1-t/3), r=2', [1, 2, 3], 2),        # rho = 1, lower k = 2
    ('Q=(1-t)(1-t/2),        r=1', [1, 2], 1),           # rho = 1, both k = 2
    ('Q=(1-t)^2,             r=1', [1, 1], 1),           # the refuting example
    ('Q=(1-t)^3(1-t/4),      r=1', [1, 1, 1, 4], 1),     # k = 3 lower, k = 2 upper
    ('Q=(1-t)^3,             r=2', [1, 1, 1], 2),        # k = 3 lower
]

n_fin = n_realbranch = n_upper = 0
for lbl, xs, rr in R9_CONFIGS:
    Qlow = q_from_roots(xs)
    for side in ('lower', 'upper'):
        if side == 'upper' and rr != 1:
            continue
        t_e, z_e, eps, kk, G_te = endpoint_data(Qlow, rr, side)
        n_fin += 1

        # --- the sign of z - z_e on the interior side, and t_e real nonzero
        assert eps == (1 if side == 'lower' else -1)
        assert abs(t_e) > mp.mpf('1e-20')
        assert (t_e > 0) if side == 'lower' else (t_e < 0)
        # --- Lambda is analytic and nonvanishing at t_e: needs t_e != 0, G(t_e) != 0
        assert abs(G_te) > mp.mpf('1e-20'), (lbl, side, 'G(t_e) = 0')
        lam_A = mp.root(mp.mpc(-eps * t_e**rr / G_te), kk)    # sign INSIDE (Route A)
        lam_B = mp.root(mp.mpc(-t_e**rr / G_te), kk)          # sign OUTSIDE (rejected)
        assert abs(lam_A) > mp.mpf('1e-20')
        # --- the k values omega*Lambda(t_e) are DISTINCT, so gamma fixes the branch
        vals = [mp.expj(2 * mp.pi * j / kk) * lam_A for j in range(kk)]
        gaps = [abs(vals[i] - vals[j]) for i in range(kk) for j in range(i + 1, kk)]
        assert min(gaps) > mp.mpf('1e-20'), (lbl, side, 'repeated leading coefficient')

        s = mp.mpf('1e-10')
        z_in = z_e + eps * s**kk
        br = sorted(d_roots(Qlow, rr, z_in), key=lambda w: abs(w - t_e))[:kk]

        n_real_gamma = n_real_br = 0
        for w in br:
            gam = (w - t_e) / s
            # Route A keeps omega^k = 1; Route B would need mu^k = eps
            om, mu = gam / lam_A, gam / lam_B
            assert abs(om**kk - 1) < mp.mpf('1e-8'), (lbl, side, 'Route A omega^k != 1')
            assert abs(mu**kk - eps) < mp.mpf('1e-8'), (lbl, side, 'Route B mu^k != eps')
            # conjugation maps branches to branches
            assert min(abs(mp.conj(w) - u) for u in br) < mp.mpf('1e-25'), \
                (lbl, side, 'branch set not conjugation-closed')
            # gamma real  <=>  branch real  (exactly, both directions)
            g_re = abs(mp.im(gam)) < mp.mpf('1e-14') * max(1, abs(gam))
            t_re = abs(mp.im(w)) < mp.mpf('1e-24') * max(1, abs(w))
            assert g_re == t_re, (lbl, side, 'reality equivalence fails')
            n_real_gamma += g_re
            n_real_br += t_re
        assert n_real_gamma == n_real_br
        n_realbranch += (n_real_br > 0)

        # --- the principal branch: Im gamma_0 != 0, and delta'(0) != 0
        # Select it as the minimum-modulus cluster root in the OPEN UPPER half-plane.
        # The file's principal() keys on |Im| > tol, which at a coalescing pair of
        # equal modulus can return the lower-half-plane conjugate and send delta < 0.
        upper = sorted((w for w in br if mp.im(w) > mp.mpf('1e-30')), key=abs)
        assert upper, (lbl, side, 'no cluster root in the upper half-plane')
        tp = upper[0]
        gam0 = (tp - t_e) / s
        assert abs(mp.im(gam0)) > mp.mpf('1e-10') * abs(gam0), \
            (lbl, side, 'principal gamma is real')
        th = mp.arg(tp)
        delta = th if side == 'lower' else mp.pi - th
        sgn = 1 if side == 'lower' else -1
        # delta = +- Im log(t_+/t_e), the branch of log analytic at 1
        assert abs(sgn * mp.im(mp.log(tp / t_e)) - delta) < mp.mpf('1e-25') * delta, \
            (lbl, side, 'delta != +-Im log(t_+/t_e)')
        pred = abs(mp.im(gam0 / t_e))
        assert pred > mp.mpf('1e-10'), (lbl, side, "delta'(0) = 0")
        assert abs(delta / s - pred) < mp.mpf('1e-6') * pred, \
            (lbl, side, "delta'(0) != |Im(gamma_0/t_e)|")

        # --- REFUTATION of the rejected complex parameter, at eps = -1
        if eps == -1:
            n_upper += 1
            vs = mp.sqrt(mp.mpc(z_in - z_e))            # the rejected complex v, k = 2
            assert abs(mp.re(vs)) < mp.mpf('1e-30') * abs(vs), \
                (lbl, 'v should be purely imaginary here')
            dtdvs = (tp - t_e) / vs
            # a REAL derivative for a NONREAL branch, so "real leading coefficient
            # implies real branch" carries no information here
            assert abs(mp.im(dtdvs)) < mp.mpf('1e-6') * abs(dtdvs), \
                (lbl, 'd t/d v should be real at the finite upper endpoint')
            assert abs(mp.im(tp)) > mp.mpf('1e-12'), (lbl, 'branch should be nonreal')
            # and Route B is refuted: mu^k = -1, so mu is NOT a kth root of unity
            mu0 = gam0 / lam_B
            assert abs(mu0**kk - 1) > mp.mpf('0.5'), (lbl, 'Route B mu^k should not be 1')

assert n_fin == 8, n_fin                  # 5 lower + 3 finite upper (the r = 1 rows)
assert n_upper == 3, n_upper
assert n_realbranch > 0, 'the reality implication never fires (test is vacuous)'
print(f'PASS: `eq:W-endpoint-form` finite-endpoint local parameter over {n_fin} endpoints '
      f'({n_upper} finite upper): eps = +-1 by side, Lambda nonvanishing, the k '
      f'leading coefficients distinct, conjugation-closed with gamma real <=> branch '
      f'real (nonvacuous at {n_realbranch}), Im gamma_0 != 0, '
      f"delta = +-Im log(t_+/t_e) and delta'(0) = |Im(gamma_0/t_e)| != 0; "
      f'the complex-v and sign-in-prefactor routes both REFUTED at '
      f'every finite upper endpoint')


# ===========================================================================
# `rem:quadratic-case`: deg Q = 2, r = 1.
#
# The case (deg Q, r) = (2,1) is the one Forgacs2017RationalDenominator excludes -- tau is constant
# there -- so the paper carries it itself, and every clause is elementary and
# exact.  Checked symbolically over generic q0, q2 > 0 and q1 < 0 (written as
# q1 = -q1n with q1n > 0), not just at one numeric Q:
#   (i)   the two zeros of Q + z t have product q0/q2, so tau = sqrt(q0/q2);
#   (ii)  t_pm = tau e^{+-i theta} are zeros of Q + z(theta) t for
#         z(theta) = -q1 - 2 sqrt(q0 q2) cos(theta), and tau is CONSTANT in both
#         z and theta -- the reason Forgacs2017RationalDenominator excluded the case;
#   (iii) z is strictly increasing on (0,pi): dz/dtheta = 2 sqrt(q0 q2) sin theta;
#   (iv)  t_a = sqrt(q0/q2) = -t_b and I_{Q,r} = (z(0+), z(pi-))
#              = (-q1 - 2 sqrt(q0 q2), -q1 + 2 sqrt(q0 q2));
#   (v)   the pair exhausts the denominator zeros, so the minimum-modulus claim is
#         immediate and each endpoint collision is exactly double -- which makes
#         `eq:endpoint-linear-gap` and `eq:endpoint-fixed-gap` vacuous here, as the remark states.
# ===========================================================================
_q0, _q2 = sp.symbols('q0 q2', positive=True)
_q1n = sp.Symbol('q1n', positive=True)
_q1 = -_q1n                                                   # q1 < 0 per `rem:quadratic-case`
_t, _z, _th = sp.symbols('t z theta', real=True)
_Q = _q0 + _q1 * _t + _q2 * _t**2
_D = sp.expand(_Q + _z * _t)                                  # r = 1
_tau = sp.sqrt(_q0 / _q2)
_zth = -_q1 - 2 * sp.sqrt(_q0 * _q2) * sp.cos(_th)

# (i) root product q0/q2 = tau^2
_cf = sp.Poly(_D, _t).all_coeffs()
assert sp.simplify(_cf[-1] / _cf[0] - _q0 / _q2) == 0
assert sp.simplify(_tau**2 - _q0 / _q2) == 0

# (ii) t_pm are genuine zeros, and tau does not move
for _root in (_tau * sp.exp(sp.I * _th), _tau * sp.exp(-sp.I * _th)):
    _res = sp.simplify(sp.radsimp(sp.expand_complex(
        sp.expand((_Q + _zth * _t).subs(_t, _root)))))
    assert sp.simplify(_res) == 0, ('`rem:quadratic-case` (ii)', _res)
assert sp.diff(_tau, _th) == 0 and sp.diff(_tau, _z) == 0     # tau constant

# (iii) strict monotonicity of z on (0, pi)
_dz = sp.simplify(sp.diff(_zth, _th))
assert sp.simplify(_dz - 2 * sp.sqrt(_q0 * _q2) * sp.sin(_th)) == 0
for _tv in (sp.Rational(1, 100), sp.pi / 4, sp.pi / 2, sp.pi - sp.Rational(1, 100)):
    assert sp.N(_dz.subs(_th, _tv).subs({_q0: 1, _q2: 4, _q1n: 3})) > 0

# (iv) endpoints: r Q - t Q' = q0 - q2 t^2 at r = 1, so t_a = tau = -t_b
_ep = sp.expand(_Q - _t * sp.diff(_Q, _t))
assert sp.simplify(_ep - (_q0 - _q2 * _t**2)) == 0
_g = -_Q / _t
_a32 = sp.simplify(sp.radsimp(_g.subs(_t, _tau)))
_b32 = sp.simplify(sp.radsimp(_g.subs(_t, -_tau)))
assert sp.simplify(_a32 - (-_q1 - 2 * sp.sqrt(_q0 * _q2))) == 0
assert sp.simplify(_b32 - (-_q1 + 2 * sp.sqrt(_q0 * _q2))) == 0
assert sp.simplify(sp.limit(_zth, _th, 0, '+') - _a32) == 0   # z(0+) = a
assert sp.simplify(sp.limit(_zth, _th, sp.pi, '-') - _b32) == 0   # z(pi-) = b

# (v) two zeros only, and each endpoint collision is exactly double
assert sp.Poly(_D, _t).degree() == 2
for _zv, _tc in ((_a32, _tau), (_b32, -_tau)):
    assert sp.simplify(sp.expand((_Q + _zv * _t) - _q2 * (_t - _tc)**2)) == 0

# concrete admissible instance: Q = (1-t)(1-t/4) has positive real zeros per `eq:Q-hypotheses`
_sub = {_q0: 1, _q2: sp.Rational(1, 4), _q1n: sp.Rational(5, 4)}
assert sp.simplify(_Q.subs(_sub) - sp.expand((1 - _t) * (1 - _t / 4))) == 0
assert all(_rt > 0 for _rt in sp.Poly(_Q.subs(_sub), _t).real_roots())
assert sp.simplify(_tau.subs(_sub) - 2) == 0
assert sp.simplify(_a32.subs(_sub) - sp.Rational(1, 4)) == 0
assert sp.simplify(_b32.subs(_sub) - sp.Rational(9, 4)) == 0
print('PASS: `rem:quadratic-case` (deg Q = 2, r = 1): tau = sqrt(q0/q2) constant in z and theta; '
      'z(theta) = -q1 - 2 sqrt(q0 q2) cos theta strictly increasing; '
      't_a = sqrt(q0/q2) = -t_b; I = (-q1 -+ 2 sqrt(q0 q2)); both collisions exactly '
      'double, so `eq:endpoint-linear-gap`/`eq:endpoint-fixed-gap` are vacuous  [Q=(1-t)(1-t/4): tau=2, I=(1/4, 9/4)]')


# --------------------------------------------------------------------------
# `thm:weighted-dominance`, lower endpoint with a SIMPLE smallest zero.  A root
# escapes to infinity there exactly when deg Q = r and the degree-drop parameter
# z_inf equals a.  The proof retains only the principal pair inside the
# separating circle and absorbs that root into the contour remainder, on the
# strength of `thm:FT-geometry`'s statement that a root leaving every bounded set
# has modulus tending to infinity.  This pins a witness showing the configuration
# is REACHABLE, so that claim is carrying a real case and not an empty one.
print()
_r = 3
_WITNESS_DPS = 80          # the bisection below runs here, not at the file default


def _a_and_zinf(x1, x2, x3, r=_r):
    """(a, z_inf, t_a) for Q = (1-t/x1)(1-t/x2)(1-t/x3) at the given r.

    a = -Q(t_a)/t_a^r at t_a the smallest positive critical point of
    g = -Q/t^r, and z_inf = -q_d is the degree-drop parameter of deg Q = r.
    Everything is mpmath at the ambient precision: the bisection that calls
    this resolves a - z_inf far below what floating point could carry.
    """
    Qc = [mp.mpf(1)]                                  # ascending coefficients of Q
    for x in (mp.mpf(x1), mp.mpf(x2), mp.mpf(x3)):
        Qc = [(Qc[k] if k < len(Qc) else mp.mpf(0))
              - (Qc[k - 1] / x if k else mp.mpf(0)) for k in range(len(Qc) + 1)]
    # r Q - t Q' has coefficients (r - k) q_k, so its degree drops when deg Q = r
    phi = [(r - k) * c for k, c in enumerate(Qc)]
    while len(phi) > 1 and phi[-1] == 0:
        phi.pop()
    crit = mp.polyroots(list(reversed(phi)), maxsteps=400, extraprec=400)
    pos = [mp.re(w) for w in crit
           if abs(mp.im(w)) < mp.mpf(10) ** -(mp.mp.dps // 2) and mp.re(w) > 0]
    assert pos, 'g has no positive critical point on this configuration'
    ta = min(pos)
    Qta = sum(c * ta**k for k, c in enumerate(Qc))
    return -Qta / ta**r, -Qc[-1], ta


with mp.workdps(_WITNESS_DPS):
    _x1, _x2 = mp.mpf(1) / 5, mp.mpf(2) / 5
    _lo, _hi = mp.mpf(1), mp.mpf(12) / 5
    assert _a_and_zinf(_x1, _x2, _lo)[0] - _a_and_zinf(_x1, _x2, _lo)[1] < 0
    assert _a_and_zinf(_x1, _x2, _hi)[0] - _a_and_zinf(_x1, _x2, _hi)[1] > 0
    # 1.4 * 2^-260 is already under one unit in the last place of x_3 at this
    # precision, so the bracket is as tight as the arithmetic can report
    for _ in range(260):
        _m = (_lo + _hi) / 2
        _av, _zv, _ = _a_and_zinf(_x1, _x2, _m)
        if _av - _zv < 0:
            _lo = _m
        else:
            _hi = _m
    _x3 = (_lo + _hi) / 2
    _a, _zinf, _ta = _a_and_zinf(_x1, _x2, _x3)
    _res = abs(_a - _zinf)
    assert _res < mp.mpf(10) ** -60, f'bisection did not converge: {_a} vs {_zinf}'
    assert _x1 < _x2 < _x3, 'the smallest zero must be simple and strictly smallest'
    assert _a > 0, 'a > 0 is what rho = 1 gives'
    print(f'PASS: deg Q = r = 3 with SIMPLE smallest zero and z_inf = a is reachable: '
          f'Q = (1-t/{mp.nstr(_x1, 3)})(1-t/{mp.nstr(_x2, 3)})(1-t/{mp.nstr(_x3, 30)}), '
          f'a = {mp.nstr(_a, 30)} = z_inf to {mp.nstr(_res, 3)}; so the lower-endpoint '
          f'branch of thm:weighted-dominance does meet an escaping root, and the contour '
          f'argument absorbing it into E_M is tested against a real configuration')

# `subsec:linear-case`, and the admissibility paragraph of section `sec:reduction`: the interval exists
# for every admissible pencil because phi = r Q - t Q' has a positive zero, and it fails
# to exist at deg Q = r = 1 because phi collapses there to the nonzero constant Q(0), so
# g has no critical point at all.  Both halves are asserted; the second is the ground for
# prop:linear-case calling the interval undefined.
for _rt, _rr in (((1,), 2), ((2,), 3), ((1, 3), 1), ((sp.Rational(1, 2),) * 2, 2),
                 ((1, 2, 5), 1), ((sp.Rational(1, 4), 4), 5), ((1, 1, 1), 2)):
    _Qe = sp.expand(sp.prod([(1 - t / sp.Rational(x)) for x in _rt]))
    if max(sp.Poly(_Qe, t).degree(), _rr) <= 1:
        continue                                          # not admissible
    _phi = sp.expand(_rr * _Qe - t * sp.diff(_Qe, t))
    _pos = [r_ for r_ in sp.Poly(_phi, t).all_roots() if r_.is_real and r_ > 0]
    assert _pos, f'admissible pencil with no positive zero of r Q - t Q\': {_rt}, r={_rr}'
    # A positive zero of phi is not the claim; a CRITICAL POINT OF g is.  Asserting only
    # the former is vacuous for a positive-rooted Q -- every zero of Q is already positive,
    # so dropping the t Q' term still passes.  Evaluate g' at the zero instead.
    _gp = sp.diff(-_Qe / t**_rr, t)
    assert sp.simplify(_gp.subs(t, min(_pos))) == 0, (_rt, _rr, min(_pos))

_q0 = sp.Rational(3, 2)
_phi_deg = sp.expand(1 * (_q0 * (1 - t / 5)) - t * sp.diff(_q0 * (1 - t / 5), t))
assert _phi_deg == _q0 != 0, f'deg Q = r = 1 should collapse phi to Q(0); got {_phi_deg}'
assert not sp.Poly(_phi_deg, t).all_roots(), 'a nonzero constant has no zero'
print(f'PASS: r Q - t Q\' has a positive zero on every admissible pencil tested, and at '
      f'deg Q = r = 1 it is the nonzero constant Q(0) = {_phi_deg}, so no t_a exists and '
      f'I_{{Q,r}} is undefined there (prop:linear-case)')


print('ALL PASS: verify_geometry')
