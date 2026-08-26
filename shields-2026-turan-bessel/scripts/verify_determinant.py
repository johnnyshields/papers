#!/usr/bin/env python3
r"""Paper section `subsec:finite-defect` (Finite-defect localization), subsec:finite-defect, kappa=1; the
exceptional degree two of section `subsec:endpoint-sufficiency` (subsec:endpoint-sufficiency,
lem:Delta2-positive); and the m=1 anomaly of section `subsec:gram` (subsec:gram: det M_1 and
the threshold a_*).

  * MD(X,Y) = x11 y22 + x22 y11 - 2 x12 y12 is the polarization of det (the display
    opening subsec:finite-defect), and for rank-one X=xx^T, Y=yy^T equals (x1 y2 - x2 y1)^2
    (lem:MD-positive).
  * Delta_n = (1/2) sum_{k=0}^n S_k S_{n-k} MD(M_k, M_{n-k}), eq. (Delta-n-MD), matches the
    direct Maclaurin coefficient [lambda^n] Delta for n = 1..5.
  * MD(M_0, M_1) = (a g - 1)/a^2 (unnumbered display in subsec:finite-defect);
    Delta_1 = 2(a g -1)/(a^3 Gamma(a)^4), eq. (Delta1-sharp); and the lower bound
    Delta_1(a) > 1/(a^4 Gamma(a)^4) (the display closing sec:endpoint).
  * A(a,0)=g/Gamma(a)^2, B(a,0)=C_kappa(a,0)=1/Gamma(a)^2, so Delta^(kappa)(a,0)=0 and the
    series starts at degree one (sec:main, after thm:coefficientwise).
  * det M_1 = ((4a-1)g-4)/(4a^2), eq. (det-M1), and the sharp anomaly threshold
    a_* = 0.3690738484... of subsec:gram (M_1 indefinite for a<a_*, PD for a>a_*).
  * for 0<a<1/2, the sign pattern beta_1 = (2a-1)/(2a) < 0, beta_m > 0 (m>=2), and
    MD(M_1, M_m) = alpha_1(1+g c_m) + alpha_m - 2 g beta_1 beta_m > 0, eq. (M1-Mm-positive).
  * Delta_2(a) > 0 (lem:Delta2-positive, in subsec:endpoint-sufficiency): Delta_2 = Q_*(a,t) / (2 a^6 (a+1)^3 Gamma(a)^4),
    eq. (Delta2-Q), with
        Q_* = 2a^4(a+1)^2 R_a^2 + 2a^2(a+1)^2(8a^2+3a+1) R_a + 2a(a+1)(5a+3), eq. (Qstar-decomp),
        R_a = psi_1(a+1) - 1/(a+1),   t = psi_1(a+1) (lem:Delta2-positive),
    via Delta_2 = S_0 S_2 MD(M_0,M_2) + S_1^2 det M_1 (eq. (Delta2-unsimplified)), its intermediate t-form,
    and the manifestly positive sum-of-squares form of eq. (Qstar-decomp) (||f||^2 = R_a).
  * MD(M_0, M_1^(kappa)) = ((kappa-1)/2 (a g)^2 + a g - 1)/a^2, eq. (MD01-kappa), and the
    monotonicity identity Delta^(kappa) = Delta^(1) + g(kappa-1) A Z Z_Theta (the
    display in the thm:coefficientwise proof).
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp
mp.mp.dps = 40

a, g, kap = sp.symbols('a g kappa', positive=True)
lam = sp.symbols('lambda', positive=True)

# ---------------------------------------------------------------------------
# MD polarization and rank-one wedge form
# ---------------------------------------------------------------------------
x11, x12, x22, y11, y12, y22 = sp.symbols('x11 x12 x22 y11 y12 y22')
X = sp.Matrix([[x11, x12], [x12, x22]])
Y = sp.Matrix([[y11, y12], [y12, y22]])
def MD(P, Q):
    return P[0, 0]*Q[1, 1] + P[1, 1]*Q[0, 0] - 2*P[0, 1]*Q[0, 1]
assert sp.expand((X+Y).det() - X.det() - Y.det() - MD(X, Y)) == 0
u1, u2, v1, v2 = sp.symbols('u1 u2 v1 v2')
xx = sp.Matrix([[u1*u1, u1*u2], [u1*u2, u2*u2]])
yy = sp.Matrix([[v1*v1, v1*v2], [v1*v2, v2*v2]])
assert sp.expand(MD(xx, yy) - (u1*v2 - u2*v1)**2) == 0
print('PASS: MD is the polarization of det; rank-one wedge = (u1 v2 - u2 v1)^2')

# ---------------------------------------------------------------------------
# Coefficient matrices M_m (kappa=1) and the exact Delta_1, MD(M0,M1)
# ---------------------------------------------------------------------------
def S(m):
    return sp.rf(2*a+m-1, m)/(sp.factorial(m)*sp.gamma(a+m)**2)
def alpha_m(m):
    return sp.polygamma(1, a+m)
def beta_m(m):
    return sp.Integer(1) if m == 0 else (2*a+m-2)/(2*(a+m-1))
def c_m(m):
    return sp.Integer(0) if m in (0, 1) else m*(m-1)/(2*(2*a+2*m-3))
def M(m):
    return sp.Matrix([[alpha_m(m), sp.sqrt(g)*beta_m(m)],
                      [sp.sqrt(g)*beta_m(m), 1 + g*c_m(m)]])

gg = sp.polygamma(1, a)
MD01 = sp.expand_func(MD(M(0), M(1)).subs(g, gg))
assert sp.simplify(MD01 - (a*gg - 1)/a**2) == 0
Delta1 = sp.expand_func((S(0)*S(1)*MD(M(0), M(1))).subs(g, gg))
assert sp.simplify(Delta1 - 2*(a*gg - 1)/(a**3*sp.gamma(a)**4)) == 0
print('PASS: MD(M0,M1) = (a g -1)/a^2 and Delta_1 = 2(a g -1)/(a^3 Gamma^4)')

# Quantitative lower bound (the display closing sec:endpoint): Delta_1(a) > 1/(a^4 Gamma(a)^4),
# i.e. a psi_1(a) - 1 > 1/(2a).  Checked numerically across the domain.
for a0 in [mp.mpf(s) for s in ('0.001', '0.05', '0.3', '1', '4', '30')]:
    D1 = 2*(a0*mp.polygamma(1, a0) - 1)/(a0**3*mp.gamma(a0)**4)
    assert D1 > 1/(a0**4*mp.gamma(a0)**4) > 0
print('PASS: Delta_1(a) > 1/(a^4 Gamma(a)^4) (sec:endpoint lower bound)')

# The m=1 anomaly block, eq. (det-M1): det M_1 = ((4a-1) g - 4)/(4 a^2), the S_1^2 det(M_1)
# contribution to Delta_2 = S_0 S_2 MD(M_0,M_2) + S_1^2 det(M_1).
detM1 = sp.expand_func(M(1).det().subs(g, gg))
assert sp.simplify(detM1 - ((4*a - 1)*gg - 4)/(4*a**2)) == 0
print('PASS: det M_1 = ((4a-1) g - 4)/(4 a^2)')

# Sharp anomaly threshold (subsec:gram, after thm:gram).  f(a) = (4a-1) psi_1(a) - 4 carries
# the sign of det M_1; f'(a) = 4 psi_1(a) + (4a-1) psi_2(a) = 2 sum_r (2r+1-2a)/(a+r)^3,
# positive on (0,1/2); f(0+) = -inf, f(1/2) = pi^2/2 - 4 > 0; unique root a_* in (0,1/2).
def f(a0):  return (4*a0 - 1)*mp.polygamma(1, a0) - 4
def fprime_closed(a0):  return 4*mp.polygamma(1, a0) + (4*a0 - 1)*mp.polygamma(2, a0)
def fprime_series(a0):  return 2*mp.nsum(lambda r: (2*r + 1 - 2*a0)/(a0 + r)**3, [0, mp.inf])
for a0 in [mp.mpf(s) for s in ('0.02', '0.1', '0.25', '0.36', '0.49')]:
    assert abs(fprime_closed(a0) - fprime_series(a0)) < mp.mpf('1e-30')
    assert fprime_closed(a0) > 0                                   # f strictly increasing on (0,1/2)
assert f(mp.mpf('1e-6')) < 0 and abs(f(mp.mpf('0.5')) - (mp.pi**2/2 - 4)) < mp.mpf('1e-30')
assert mp.pi**2/2 - 4 > 0
a_star = mp.findroot(f, mp.mpf('0.37'))
# exact to the digits the paper prints: a 1e-9/1e-10 tolerance would accept a
# wrong final digit (|a_* - 0.3690738485| = 8.85e-11)
assert mp.nstr(a_star, 10) == '0.3690738484', mp.nstr(a_star, 20)
assert f(a_star*(1 - mp.mpf('1e-6'))) < 0 < f(a_star*(1 + mp.mpf('1e-6')))
# det M_1 sign: indefinite (det<0) for a<a_*, positive definite (det>0) for a>a_*.
det_M1 = lambda a0: ((4*a0 - 1)*mp.polygamma(1, a0) - 4)/(4*a0**2)
for a0 in [mp.mpf('0.1'), mp.mpf('0.3')]:
    assert det_M1(a0) < 0
for a0 in [mp.mpf('0.4'), mp.mpf('0.5'), mp.mpf('2')]:
    assert det_M1(a0) > 0
print('PASS: anomaly threshold a_* = 0.3690738484..., f increasing, det M_1 sign change')

# Constant terms (sec:main, after thm:coefficientwise): A(a,0)=g/Gamma^2, B(a,0)=C_kappa(a,0)=1/Gamma^2,
# so Delta^(kappa)(a,0)=0 and the Maclaurin series starts at degree one.
A0 = S(0)*alpha_m(0)               # = psi_1(a)/Gamma^2 = g/Gamma^2
B0 = S(0)*beta_m(0)                # = 1/Gamma^2
C0 = S(0)*(1 + g*c_m(0))           # c_0 = 0 -> 1/Gamma^2
assert sp.simplify(A0 - gg/sp.gamma(a)**2) == 0
assert sp.simplify(B0 - 1/sp.gamma(a)**2) == 0
assert sp.simplify(C0 - 1/sp.gamma(a)**2) == 0
assert sp.simplify(A0*C0 - gg*B0**2) == 0        # Delta^(kappa)(a,0) = 0
print('PASS: A(a,0)=g/Gamma^2, B(a,0)=C(a,0)=1/Gamma^2, Delta(a,0)=0 (series starts at degree 1)')

# ---------------------------------------------------------------------------
# Delta_n : MD-sum vs direct Maclaurin coefficient, n = 1..5
# ---------------------------------------------------------------------------
K = 6
def series(coeff):
    return sum(coeff(k)*lam**k/(sp.factorial(k)*sp.gamma(a+k)) for k in range(K+1))
psi  = lambda k: sp.digamma(a+k)
psi1 = lambda k: sp.polygamma(1, a+k)
Z   = series(lambda k: 1)
Za  = series(lambda k: -psi(k))
Zaa = series(lambda k: psi(k)**2 - psi1(k))
Zt  = series(lambda k: k)
Ztt = series(lambda k: k**2)
Zat = series(lambda k: -k*psi(k))
A_ser = Za**2 - Z*Zaa
B_ser = Z**2 + Z*Zat - Za*Zt
C_ser = Z**2 + g*(Z*Zt - Z*Ztt + Zt**2)       # kappa = 1
Delta_ser = A_ser*C_ser - g*B_ser**2

def coeff(expr, n):
    return sp.expand_func(sp.expand(sp.series(expr, lam, 0, n+1).removeO().coeff(lam, n)))
def Delta_MD(n):
    return sp.Rational(1, 2)*sum(S(k)*S(n-k)*MD(M(k), M(n-k)) for k in range(n+1))

for n in range(1, 6):
    direct = coeff(Delta_ser, n).subs(g, gg)
    mdsum  = sp.expand_func(Delta_MD(n)).subs(g, gg)
    assert sp.simplify(sp.expand_func(direct - mdsum)) == 0, n
print('PASS: Delta_n (MD-sum) equals direct [lambda^n] Delta, n=1..5')

# ---------------------------------------------------------------------------
# eq. (M1-Mm-positive): MD(M_1,M_m) > 0 for EVERY a>0 and m>=2.  The display is strict, and
# the paper proves it in two branches:
#   0 < a < 1/2 : beta_1 < 0 < beta_m with every diagonal entry positive;
#   a >= 1/2    : M_1, M_m > 0 by thm:gram, so the STRICT case of lem:MD-positive
#                 applies (that case needs M_1 != 0 and M_m > 0).
# Both branches are asserted below, so weakening either the display or the
# "strict case" attribution in subsec:finite-defect fails here.
# ---------------------------------------------------------------------------
def alpha_n(a0, mm): return mp.polygamma(1, a0 + mm)
def beta_n(a0, mm): return mp.mpf(1) if mm == 0 else (2*a0+mm-2)/(2*(a0+mm-1))
def c_n(a0, mm): return mp.mpf(0) if mm in (0, 1) else mp.mpf(mm*(mm-1))/(2*(2*a0+2*mm-3))
def md_1m(a0, mm):
    g0 = mp.polygamma(1, a0)
    return (alpha_n(a0, 1)*(1 + g0*c_n(a0, mm)) + alpha_n(a0, mm)
            - 2*g0*beta_n(a0, 1)*beta_n(a0, mm))
def det_M_num(a0, mm):
    g0 = mp.polygamma(1, a0)
    return alpha_n(a0, mm)*(1 + g0*c_n(a0, mm)) - g0*beta_n(a0, mm)**2

# branch 1: 0 < a < 1/2, via the beta sign pattern
for a0 in [mp.mpf(s) for s in ('0.001', '0.01', '0.1', '0.25', '0.45', '0.499')]:
    assert beta_n(a0, 1) < 0 and abs(beta_n(a0, 1) - (2*a0-1)/(2*a0)) < mp.mpf('1e-30')
    for mm in range(2, 9):
        assert beta_n(a0, mm) > 0
        assert md_1m(a0, mm) > 0, (a0, mm, md_1m(a0, mm))
print('PASS: beta signs and MD(M_1,M_m) > 0 for 0<a<1/2, m>=2')

# branch 2: a >= 1/2.  The strict case of lem:MD-positive is only available if M_1 and
# M_m are positive DEFINITE there (a_* = 0.369... < 1/2, so M_1 is), which is the
# case subsec:finite-defect invokes, rather than the nonstrict one.
for a0 in [mp.mpf(s) for s in ('0.5', '0.5000001', '0.75', '1', '2', '10', '100', '1000')]:
    assert alpha_n(a0, 1) > 0 and det_M_num(a0, 1) > 0, ('M_1 not PD at', a0)
    for mm in range(2, 9):
        assert alpha_n(a0, mm) > 0 and det_M_num(a0, mm) > 0, ('M_m not PD at', a0, mm)
        assert md_1m(a0, mm) > 0, (a0, mm, md_1m(a0, mm))
print('PASS: M_1, M_m > 0 and MD(M_1,M_m) > 0 for a>=1/2, m>=2 (strict case of lem:MD-positive)')

# The strengthened display is strict but admits NO uniform positive lower bound:
# the m=2 value decays like a^{-3} as a -> oo (9.0e-4, 9.9e-7, 1.0e-9 at a=10,100,
# 1000), so ">0" is the correct strengthening and no positive constant is claimable.
# This matches the caveat before thm:coefficientwise that one threshold serving every a>0
# does not assert a lower bound uniform in a.
tail = [md_1m(mp.mpf(s), 2) for s in ('10', '100', '1000')]
assert all(v > 0 for v in tail)
assert tail[0] > tail[1] > tail[2]
assert tail[2] < mp.mpf('1e-9')
print('PASS: MD(M_1,M_2) > 0 yet decreasing in a -- no uniform positive lower bound')

# ---------------------------------------------------------------------------
# Exceptional degree-two coefficient, eqs. (Delta2-Q), (Qstar-decomp), (Delta2-unsimplified)
# ---------------------------------------------------------------------------
t = sp.polygamma(1, a+1)
Ra = t - 1/(a+1)
Qstar = (2*a**4*(a+1)**2*Ra**2
         + 2*a**2*(a+1)**2*(8*a**2+3*a+1)*Ra
         + 2*a*(a+1)*(5*a+3))
Delta2_paper = Qstar/(2*a**6*(a+1)**3*sp.gamma(a)**4)
Delta2_direct = coeff(Delta_ser, 2).subs(g, gg)
assert sp.simplify(sp.expand_func(Delta2_direct - Delta2_paper)) == 0
print('PASS: Delta_2 = Q_*/(2 a^6 (a+1)^3 Gamma^4)')

# Explicit derivation route, eq. (Delta2-unsimplified): the closed S-values, the
# intermediate MD(M_0,M_2), and Delta_2 = S_0 S_2 MD(M_0,M_2) + S_1^2 det M_1.
assert sp.simplify(S(0) - 1/sp.gamma(a)**2) == 0
assert sp.simplify(S(1) - 2/(a*sp.gamma(a)**2)) == 0
assert sp.simplify(S(2) - (2*a+1)/(a**2*(a+1)*sp.gamma(a)**2)) == 0
MD02 = sp.expand_func(MD(M(0), M(2)).subs(g, gg))
MD02_paper = gg*(1 + gg/(2*a+1)) + sp.polygamma(1, a+2) - 2*gg*a/(a+1)
assert sp.simplify(sp.expand_func(MD02 - MD02_paper)) == 0
Delta2_unsimpl = sp.expand_func((S(0)*S(2)*MD(M(0), M(2)) + S(1)**2*M(1).det()).subs(g, gg))
assert sp.simplify(sp.expand_func(Delta2_unsimpl - Delta2_paper)) == 0
print('PASS: S_0,S_1,S_2, MD(M_0,M_2), and Delta_2 = S_0 S_2 MD(M_0,M_2) + S_1^2 det M_1')

# Intermediate t-form of Q_* (lem:Delta2-positive proof, before substituting t = R_a + 1/(a+1)):
# Q_* = 2a^4(a+1)^2 t^2 + 2a^2(8a^4+17a^3+13a^2+5a+1) t + 2a(-8a^4-10a^3+a^2+7a+3).
t_sym = sp.symbols('t_sym', positive=True)
Q_in_t = (2*a**4*(a+1)**2*t_sym**2
          + 2*a**2*(8*a**4+17*a**3+13*a**2+5*a+1)*t_sym
          + 2*a*(-8*a**4-10*a**3+a**2+7*a+3))
Q_from_Ra = Qstar.subs(t, t_sym)   # Q_* with R_a = t_sym - 1/(a+1)
assert sp.cancel(Q_from_Ra - Q_in_t) == 0
print('PASS: intermediate t-form of Q_* matches the R_a form')

# Sum-of-squares form of eq. (Qstar-decomp): the squared norm of the three-block vector,
# with ||f||^2 = R (a free symbol), reproduces Q_* as a polynomial in R.
R = sp.symbols('R', positive=True)
norm_sq = ((sp.sqrt(2)*a**2*(a+1))**2 * R**2                      # ||f (x) f||^2 = ||f||^4 = R^2
           + (sp.sqrt(2)*a*(a+1)*sp.sqrt(8*a**2+3*a+1))**2 * R    # ||f||^2 = R
           + (sp.sqrt(2*a*(a+1)*(5*a+3)))**2)
Q_in_R = (2*a**4*(a+1)**2*R**2 + 2*a**2*(a+1)**2*(8*a**2+3*a+1)*R + 2*a*(a+1)*(5*a+3))
assert sp.expand(norm_sq - Q_in_R) == 0
blocks = {
    'Qstar_Ra_squared':  2*a**4*(a+1)**2,
    'Qstar_Ra_linear':   2*a**2*(a+1)**2*(8*a**2+3*a+1),
    'Qstar_Ra_constant': 2*a*(a+1)*(5*a+3),
}
for coef in blocks.values():
    assert all(cc > 0 for cc in sp.Poly(sp.expand(coef), a).coeffs())
# Cross-check the exported dependency-free tables against the symbolic derivation.
import json
from pathlib import Path
tables = json.loads(Path(__file__).with_name('exported_coefficients.json').read_text())
for name, coef in blocks.items():
    poly = sp.Poly(sp.expand(coef), a)
    derived = {int(mono[0]): int(cf) for mono, cf in poly.terms()}
    exported = dict(zip(tables[name]['powers_of_a'], tables[name]['coefficients']))
    assert derived == exported, (name, derived, exported)
print('PASS: manifestly positive sum-of-squares form of Q_*; exported tables match')

# ---------------------------------------------------------------------------
# kappa dependence: the monotonicity display and eq. (MD01-kappa)
# ---------------------------------------------------------------------------
# Delta^(kappa) - Delta^(1) = A (C_kappa - C_1) = g(kappa-1) A Z Z_Theta, as an
# identity in the free symbols Z, Zt (=Z_Theta), Ztt, A, B.
Zs, Zts, Ztts, Asym, Bsym = sp.symbols('Zs Zts Ztts Asym Bsym')
C_k = Zs**2 + g*(kap*Zs*Zts - Zs*Ztts + Zts**2)
C_1 = Zs**2 + g*(Zs*Zts - Zs*Ztts + Zts**2)
Dk = Asym*C_k - g*Bsym**2
D1 = Asym*C_1 - g*Bsym**2
assert sp.expand(Dk - D1 - g*(kap-1)*Asym*Zs*Zts) == 0
print('PASS: Delta^(kappa) = Delta^(1) + g(kappa-1) A Z Z_Theta')

# MD(M0, M1^(kappa)) with c_1^(kappa) = (kappa-1)/2.
M1k = sp.Matrix([[alpha_m(1), sp.sqrt(g)*beta_m(1)],
                 [sp.sqrt(g)*beta_m(1), 1 + g*(kap-1)/2]])
MD01k = sp.expand_func(MD(M(0), M1k).subs(g, gg))
target = ((kap-1)/2*(a*gg)**2 + a*gg - 1)/a**2
assert sp.simplify(MD01k - target) == 0
print('PASS: MD(M0, M1^(kappa)) = ((kappa-1)/2 (a g)^2 + a g - 1)/a^2')

# Linear-coefficient closed form of the classification (from eq. (MD01-kappa)):
# the direct series coefficient [lambda^1] Delta^(kappa) equals S_0 S_1 MD(M_0, M_1^(kappa)),
# i.e. (2/(a^3 Gamma^4))[(kappa-1)/2 (a g)^2 + a g - 1].  For kappa<1 this is
# negative for small a (a g -> +inf), the "only if" half of thm:coefficientwise.
Ck_ser = Z**2 + g*(kap*Zt*Z - Z*Ztt + Zt**2)
Delta_k_ser = A_ser*Ck_ser - g*B_ser**2
Delta1_k_direct = coeff(Delta_k_ser, 1).subs(g, gg)
Delta1_k_claim = (2/(a**3*sp.gamma(a)**4))*(sp.Rational(1, 2)*(kap-1)*(a*gg)**2 + a*gg - 1)
assert sp.simplify(sp.expand_func(Delta1_k_direct - Delta1_k_claim)) == 0
print('PASS: Delta_1^(kappa) = (2/(a^3 Gamma^4))[(kappa-1)/2 (a g)^2 + a g - 1]')

# The "only if" half of thm:coefficientwise, demonstrated (not merely the closed form):
# for kappa < 1 the coefficient is negative at small a, since a g -> +inf drives
# the bracket (kappa-1)/2 (a g)^2 + a g - 1 negative.  So the endpoint kappa = 1
# is sharp: no kappa < 1 keeps Delta_1^(kappa) nonnegative for all a > 0.
for aval in (sp.Rational(1, 1000), sp.Rational(1, 100), sp.Rational(1, 10)):
    v = Delta1_k_claim.subs({kap: sp.Rational(1, 2), a: aval}).evalf(30)
    assert v < 0, (aval, v)
print('PASS: kappa<1 fails: Delta_1^(kappa)(a) < 0 at small a (only-if half of thm:coefficientwise)')

print('ALL PASS: verify_determinant')
