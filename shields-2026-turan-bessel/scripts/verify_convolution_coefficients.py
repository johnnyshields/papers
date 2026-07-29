#!/usr/bin/env python3
r"""Paper section 3 (Reciprocal-gamma convolution and coefficient formulas), sec:coefficients.

Verifies, symbolically and exactly:

  * Lemma 3.1 = lem:convolution (asymmetric reciprocal-gamma convolution), eq. (3.1),
    general (alpha,beta);
  * S_m = (2a+m-1)_m / (m! Gamma(a+m)^2) and [lambda^m] Z^2 = S_m (the displays
    after Lemma 3.1);
  * the coefficient formulas of Theorem 3.2 (thm:coefficients):
    alpha_m eq. (3.3), beta_m eq. (3.4), gamma_m^(kappa) eq. (3.5), c_m^(kappa)
    eqs. (3.6)-(3.7), and the sharp endpoint c_m (the kappa=1 display in
    Theorem 3.2), including the two algebraic forms of c_m^(kappa) in eq. (3.7);
  * the convolution moments of the Theorem 3.2 proof: E_delta D = m*delta/(a+m-1)
    eq. (3.12), E(DX) = m/(a+m-1) eq. (3.13), and E D^2 = m(2a+m-2)/(2a+2m-3)
    (the display in the Theorem 3.2 proof).

Every coefficient formula is cross-checked against a direct Maclaurin expansion of
A, B, and C_kappa in lambda, so the closed forms are pinned to the series that
defines them.
"""
from __future__ import annotations
import sympy as sp

a, kap = sp.symbols('a kappa', positive=True)
alp, bet = sp.symbols('alpha beta', positive=True)   # free convolution parameters
lam, g = sp.symbols('lambda g', positive=True)
M_MAX = 6

# ---------------------------------------------------------------------------
# Lemma 3.1  (asymmetric reciprocal-gamma convolution), general (alpha, beta)
# ---------------------------------------------------------------------------
for m in range(M_MAX + 1):
    lhs = sum(
        1/(sp.factorial(i)*sp.factorial(m-i)*sp.gamma(alp+i)*sp.gamma(bet+m-i))
        for i in range(m+1)
    )
    rhs = sp.rf(alp+bet+m-1, m)/(sp.factorial(m)*sp.gamma(alp+m)*sp.gamma(bet+m))
    assert sp.simplify(sp.expand_func(lhs - rhs)) == 0, m
print('PASS: asymmetric reciprocal-gamma convolution (general alpha,beta), m<=%d' % M_MAX)

# ---------------------------------------------------------------------------
# Paper coefficient formulas
# ---------------------------------------------------------------------------
def S(m):
    return sp.rf(2*a+m-1, m)/(sp.factorial(m)*sp.gamma(a+m)**2)

def alpha_m(m):
    return sp.polygamma(1, a+m)                              # eq. (3.3)

def beta_m(m):
    if m == 0:
        return sp.Integer(1)                                # eq. (3.4)
    return (2*a+m-2)/(2*(a+m-1))

def c_kappa(m):                                             # eqs. (3.6)-(3.7)
    if m == 0:
        return sp.Integer(0)
    if m == 1:
        return (kap-1)/2
    return kap*m/2 - m*(2*a+m-2)/(2*(2*a+2*m-3))

def c_sharp(m):                                            # sharp endpoint c_m, kappa=1
    if m in (0, 1):
        return sp.Integer(0)
    return m*(m-1)/(2*(2*a+2*m-3))

def gamma_kappa(m):
    return 1 + g*c_kappa(m)

# Two algebraic forms of c_m^(kappa) for m>=2 (eq. (3.7)) agree, and kappa=1 gives c_m.
for m in range(2, M_MAX + 1):
    form1 = kap*m/2 - m*(2*a+m-2)/(2*(2*a+2*m-3))
    form2 = m*((kap-1)*(2*a+2*m-3) + m-1)/(2*(2*a+2*m-3))
    assert sp.simplify(form1 - form2) == 0, m
    assert sp.simplify(c_kappa(m).subs(kap, 1) - c_sharp(m)) == 0, m
assert sp.simplify(c_kappa(1).subs(kap, 1) - c_sharp(1)) == 0
print('PASS: c_m^(kappa) two forms agree; kappa=1 gives the sharp c_m')

# ---------------------------------------------------------------------------
# Direct Maclaurin coefficients of A, B, C_kappa from the series definition
# ---------------------------------------------------------------------------
def series(coeff):
    return sum(coeff(k)*lam**k/(sp.factorial(k)*sp.gamma(a+k)) for k in range(M_MAX+1))

psi  = lambda k: sp.digamma(a+k)
psi1 = lambda k: sp.polygamma(1, a+k)

Z   = series(lambda k: 1)
Za  = series(lambda k: -psi(k))
Zaa = series(lambda k: psi(k)**2 - psi1(k))
Zt  = series(lambda k: k)
Ztt = series(lambda k: k**2)
Zat = series(lambda k: -k*psi(k))

A       = Za**2 - Z*Zaa
B       = Z**2 + Z*Zat - Za*Zt
C_kap   = Z**2 + g*(kap*Z*Zt - Z*Ztt + Zt**2)

gg = sp.polygamma(1, a)

def coeff(expr, m):
    return sp.expand_func(sp.expand(sp.series(expr, lam, 0, m+1).removeO().coeff(lam, m)))

# The factors are truncated at k <= M_MAX, so every pair (i, j) with i + j = M_MAX is
# present and [lambda^M_MAX] of the product is exact -- the top coefficient is included.
for m in range(M_MAX + 1):
    ca = coeff(A, m).subs(g, gg)
    cb = coeff(B, m).subs(g, gg)
    cc = coeff(C_kap, m).subs(g, gg)
    assert sp.simplify(sp.expand_func(ca - S(m)*alpha_m(m))) == 0, ('A', m)
    assert sp.simplify(sp.expand_func(cb - S(m)*beta_m(m))) == 0, ('B', m)
    assert sp.simplify(sp.expand_func(cc - (S(m)*gamma_kappa(m)).subs(g, gg))) == 0, ('C', m)

    # eq. (3.8): the coefficient matrix of Turan_kappa is S_m M_m^(kappa), with the
    # sqrt(g) sitting off-diagonal.  Assemble it and check it against the entries just
    # verified, so the placement is tested rather than left to the reader.
    Mm = sp.Matrix([[alpha_m(m), sp.sqrt(g)*beta_m(m)],
                    [sp.sqrt(g)*beta_m(m), gamma_kappa(m)]])
    T_m = (S(m)*Mm).subs(g, gg)
    assert sp.simplify(sp.expand_func(T_m[0, 0] - ca)) == 0, ('M11', m)
    assert sp.simplify(sp.expand_func(T_m[1, 1] - cc)) == 0, ('M22', m)
    # the off-diagonal of Turan_kappa is sqrt(g) B, eq. (2.5), not B
    assert sp.simplify(sp.expand_func(T_m[0, 1] - sp.sqrt(gg)*cb)) == 0, ('M12', m)
    assert sp.simplify(sp.expand_func(
        (S(m)**2*(Mm[0, 0]*Mm[1, 1] - Mm[0, 1]**2)).subs(g, gg)
        - (ca*cc - gg*cb**2))) == 0, ('det', m)
print('PASS: [lambda^m] of A, B, C_kappa equal S_m*(alpha_m, beta_m, gamma_m^kappa),')
print('      and eq. (3.8) assembles them as S_m M_m with sqrt(g) off-diagonal')

# ---------------------------------------------------------------------------
# Convolution moments, eqs. (3.12)-(3.13) and the E D^2 display.  Weights are the
# asymmetric law w_i(delta) = 1/(i!(m-i)! Gamma(a+delta+i) Gamma(a-delta+m-i)); D = m-2i.
# ---------------------------------------------------------------------------
delta = sp.symbols('delta', real=True)
for m in range(1, M_MAX + 1):
    w = [1/(sp.factorial(i)*sp.factorial(m-i)*sp.gamma(a+delta+i)*sp.gamma(a-delta+m-i))
         for i in range(m+1)]
    norm = sum(w)
    ED = sum((m-2*i)*wi for i, wi in enumerate(w))/norm            # E_delta D
    ED0 = sp.simplify(sp.expand_func(ED.subs(delta, 0)))
    assert ED0 == 0                                                # symmetric law at delta=0
    dED = sp.simplify(sp.expand_func(sp.diff(ED, delta).subs(delta, 0)))
    assert sp.simplify(dED - m/(a+m-1)) == 0, ('E_deltaD slope', m)  # eq. (3.12) d/ddelta

    # E(DX) and E D^2 at delta=0.  X_i = psi(a+m-i) - psi(a+i), score of w_i.
    w0 = [wi.subs(delta, 0) for wi in w]
    n0 = sum(w0)
    X = [sp.digamma(a+m-i) - sp.digamma(a+i) for i in range(m+1)]
    EDX = sp.simplify(sp.expand_func(sum((m-2*i)*X[i]*w0[i] for i in range(m+1))/n0))
    ED2 = sp.simplify(sp.expand_func(sum((m-2*i)**2*w0[i] for i in range(m+1))/n0))
    assert sp.simplify(EDX - m/(a+m-1)) == 0, ('E(DX)', m)           # eq. (3.13)
    assert sp.simplify(ED2 - m*(2*a+m-2)/(2*a+2*m-3)) == 0, ('E D^2', m)  # E D^2 display
print('PASS: convolution moments E_delta D at delta=0 and its delta-derivative,'
      ' E(DX), E D^2')

# ---------------------------------------------------------------------------
# The restriction |delta| < a of the Theorem 3.2 proof is load-bearing, and it is
# exactly the positivity boundary of the weights: the probabilistic reading needs
# w_i(delta) > 0, which fails as soon as |delta| >= a.  The algebraic identities,
# by contrast, survive past it -- they are identities of entire functions.
# Use the entire reciprocal gamma so the boundary itself is evaluable.
# ---------------------------------------------------------------------------
import mpmath as mp
mp.mp.dps = 30

def w_num(i, m, a0, d):
    return (mp.rgamma(a0 + d + i)*mp.rgamma(a0 - d + m - i)
            / (mp.factorial(i)*mp.factorial(m - i)))

a0, m0 = mp.mpf('0.5'), 2
inside = w_num(2, m0, a0, a0/2)
at_bdy = w_num(2, m0, a0, a0)
outside = w_num(2, m0, a0, 3*a0/2)
assert inside > 0, inside                       # |delta| < a: a genuine law
assert at_bdy == 0, at_bdy                      # |delta| = a: the weight vanishes
assert outside < 0, outside                     # |delta| > a: no longer a law
print('PASS: |delta| < a is exactly where the weights stay positive'
      f' (w = {mp.nstr(inside, 6)}, {mp.nstr(at_bdy, 6)}, {mp.nstr(outside, 6)}'
      ' at delta = a/2, a, 3a/2), so the probabilistic reading needs it')

# but eq. (3.12) is an identity in delta and does not: check it past the boundary
F2 = lambda d: sum(w_num(i, m0, a0, d) for i in range(m0 + 1))
ED = lambda d: sum((m0 - 2*i)*w_num(i, m0, a0, d) for i in range(m0 + 1))/F2(d)
for d in ('0.25', '0.75', '1.5'):
    dd = mp.mpf(d)
    assert abs(ED(dd) - m0*dd/(a0 + m0 - 1)) < mp.mpf('1e-25'), d
print('PASS: eq. (3.12) E_delta D = m delta/(a+m-1) holds exactly in delta, including'
      ' past |delta| = a where the weights are no longer positive')

print('ALL PASS: verify_convolution_coefficients')
