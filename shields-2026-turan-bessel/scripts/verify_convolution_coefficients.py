#!/usr/bin/env python3
r"""Paper section 3 (Reciprocal-gamma convolution and coefficient formulas).

Verifies, symbolically and exactly:

  * Lemma 3.1 (asymmetric reciprocal-gamma convolution), eq. (3.1), general (alpha,beta);
  * S_m = (2a+m-1)_m / (m! Gamma(a+m)^2) and [lambda^m] Z^2 = S_m (the displays
    after Lemma 3.1);
  * the coefficient formulas of Theorem 3.2 (Exact coefficient matrices):
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

for m in range(M_MAX):        # top truncated coefficient of the product is unreliable
    ca = coeff(A, m).subs(g, gg)
    cb = coeff(B, m).subs(g, gg)
    cc = coeff(C_kap, m).subs(g, gg)
    assert sp.simplify(sp.expand_func(ca - S(m)*alpha_m(m))) == 0, ('A', m)
    assert sp.simplify(sp.expand_func(cb - S(m)*beta_m(m))) == 0, ('B', m)
    assert sp.simplify(sp.expand_func(cc - (S(m)*gamma_kappa(m)).subs(g, gg))) == 0, ('C', m)
print('PASS: [lambda^m] of A, B, C_kappa equal S_m*(alpha_m, beta_m, gamma_m^kappa)')

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
print('PASS: convolution moments E_delta D, E(DX), E D^2')

print('ALL PASS: verify_convolution_coefficients')
