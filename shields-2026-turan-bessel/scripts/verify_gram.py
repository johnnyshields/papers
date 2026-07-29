#!/usr/bin/env python3
r"""Paper section 4 (Gram structure and the exceptional matrix M_1), sec:gram.

Result numbers are paired with the paper's labels, which survive renumbering:
Lemma 4.1 = lem:trigamma-bounds, Theorem 4.2 = thm:gram.  The paper writes
q = a + m/2 - 1 for the vector v scale; the code variable is named q to match.

Two exact symbolic certificates (sympy):
  * telescoping cross term  q/(x-1) = beta_m,  eq. (4.6);
  * the sharp Gram-slack simplification in the Theorem 4.2 proof:
        a - 1/2 + m(m-1)/(2(2a+2m-3)) - (a+m/2-1)^2/(a+m-3/2)
            = (m-1)/(2(2a+2m-3)) > 0   (m >= 2);
  * M_0 is the rank-one matrix [[g,sqrt g],[sqrt g,1]] (the display after Theorem 4.2).

High-precision numerics (mpmath):
  * the trigamma integrand bound 1+t/2 < t/(1-e^{-t}) < e^{t/2} and the three bounds of
    Lemma 4.1: psi_1(y) > 1/y + 1/(2y^2), eq. (4.2); psi_1(y) < 1/(y-1/2), eq. (4.3);
    1/psi_1(a) > a-1/2, eq. (4.4);
  * the norms ||u^{(m)}||^2 = psi_1(x) = alpha_m, eq. (4.5), <u,v> = q/(x-1) = beta_m, eq. (4.6),
    ||v^{(m)}||^2 = q^2 psi_1(x-1), eq. (4.7), each summed as an independent l^2 series;
  * rho_m(a) = 1/g + c_m - q^2 psi_1(x-1) > 0, eq. (4.8), for (m>=2, a>0) and (m=1, a>=1/2), and
    Theorem 4.2's Gram identity N_m = Gram(xi_m, eta_m), eq. (4.9), with xi_m=(u,0), eta_m=(v, sqrt(rho_m)).
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

# ===========================================================================
# Exact symbolic certificates
# ===========================================================================
a, r = sp.symbols('a r', positive=True)
m = r + 2                                     # m >= 2 parametrized as r+2, r>0
x = a + m
q = a + m/sp.Integer(2) - 1
beta_m = (2*a + m - 2)/(2*(a + m - 1))
c_m = m*(m-1)/(2*(2*a + 2*m - 3))            # kappa = 1

assert sp.factor(q/(x-1) - beta_m) == 0
print('PASS: telescoping cross term q/(x-1) = beta_m')

slack = a - sp.Rational(1, 2) + c_m - q**2/(x - sp.Rational(3, 2))
assert sp.simplify(slack - (m-1)/(2*(2*a+2*m-3))) == 0
# manifest positivity: numerator m-1 = r+1 > 0, denominator 2a+2m-3 = 2a+2r+1 > 0
assert sp.simplify((m-1) - (r+1)) == 0
print('PASS: sharp Gram-slack = (m-1)/(2(2a+2m-3)) > 0 for m>=2')

gsym = sp.symbols('g', positive=True)
M0 = sp.Matrix([[gsym, sp.sqrt(gsym)], [sp.sqrt(gsym), 1]])
assert M0.det() == 0 and M0[0, 0] > 0
w = sp.Matrix([sp.sqrt(gsym), 1])
assert sp.simplify(M0 - w*w.T) == sp.zeros(2)
print('PASS: M_0 = [[g,sqrt g],[sqrt g,1]] is rank-one PSD')

# ===========================================================================
# High-precision numerics
# ===========================================================================
mp.mp.dps = 40

# --- trigamma integrand and the resulting bounds ---------------------------
for tt in [mp.mpf(s) for s in ('0.01', '0.2', '1', '3', '12')]:
    kernel = tt/(1 - mp.e**(-tt))
    assert 1 + tt/2 < kernel < mp.e**(tt/2)
# eq. (4.1): the integral representation itself, against the defining series
for yy in [mp.mpf(s) for s in ('0.05', '0.3', '1', '4', '25')]:
    quad = mp.quad(lambda tau: mp.e**(-yy*tau)*tau/(1 - mp.e**(-tau)), [0, mp.inf])
    assert abs(quad - mp.polygamma(1, yy)) < mp.mpf('1e-25')*max(1, abs(quad)), yy
print('PASS: psi_1(y) = int_0^inf e^{-y tau} tau/(1-e^{-tau}) dtau, eq. (4.1)')
for yy in [mp.mpf(s) for s in ('0.05', '0.3', '0.7', '1', '4', '25')]:
    tri = mp.polygamma(1, yy)
    assert tri > 1/yy + 1/(2*yy**2)                       # eq. (4.2)
    if yy > mp.mpf('0.5'):
        assert tri < 1/(yy - mp.mpf('0.5'))               # eq. (4.3)
    assert 1/mp.polygamma(1, yy) > yy - mp.mpf('0.5')     # eq. (4.4)
print('PASS: trigamma integrand bound and Lemma 4.1')

# --- l^2 norms summed independently and matched to closed forms ------------
def gram_norms(a0, mm):
    x0 = a0 + mm
    q0 = a0 + mp.mpf(mm)/2 - 1
    unorm = mp.nsum(lambda r_: 1/(x0 + r_)**2, [0, mp.inf])          # ||u||^2
    cross = q0*mp.nsum(lambda r_: 1/((x0 + r_ - 1)*(x0 + r_)), [0, mp.inf])
    vnorm = q0**2*mp.nsum(lambda r_: 1/(x0 + r_ - 1)**2, [0, mp.inf])
    return x0, q0, unorm, cross, vnorm

for a0, mm in [(mp.mpf('0.3'), 2), (mp.mpf('0.3'), 5), (mp.mpf('1.7'), 3),
               (mp.mpf('9'), 4), (mp.mpf('0.5'), 1), (mp.mpf('2.2'), 1)]:
    x0, q0, unorm, cross, vnorm = gram_norms(a0, mm)
    g0 = mp.polygamma(1, a0)
    alpha0 = mp.polygamma(1, a0 + mm)
    beta0 = (2*a0 + mm - 2)/(2*(a0 + mm - 1))
    cm0 = mp.mpf(0) if mm in (0, 1) else mp.mpf(mm*(mm-1))/(2*(2*a0 + 2*mm - 3))
    assert abs(unorm - mp.polygamma(1, x0)) < mp.mpf('1e-30')
    assert abs(unorm - alpha0) < mp.mpf('1e-30')
    assert abs(cross - q0/(x0-1)) < mp.mpf('1e-30')
    assert abs(cross - beta0) < mp.mpf('1e-30')
    assert abs(vnorm - q0**2*mp.polygamma(1, x0-1)) < mp.mpf('1e-30')

    rho = 1/g0 + cm0 - vnorm
    if mm >= 2 or (mm == 1 and a0 >= mp.mpf('0.5')):
        assert rho > 0, (a0, mm, rho)
    # eq. (4.9): N_m = Gram(xi_m, eta_m), xi=(u,0), eta=(v, sqrt rho).
    G11, G12, G22 = unorm, cross, vnorm + rho
    N = mp.matrix([[alpha0, beta0], [beta0, 1/g0 + cm0]])
    err = max(abs(G11-N[0, 0]), abs(G12-N[0, 1]), abs(G22-N[1, 1]))
    assert err < mp.mpf('1e-30') and mp.det(N) > 0, (a0, mm, err)

    # eq. (4.10): M_m = Gram(xi_m, sqrt(g) eta_m), the unnormalized statement.
    rg = mp.sqrt(g0)
    M11, M12, M22 = unorm, rg*cross, g0*(vnorm + rho)
    Mm = mp.matrix([[alpha0, rg*beta0], [rg*beta0, 1 + g0*cm0]])
    errM = max(abs(M11-Mm[0, 0]), abs(M12-Mm[0, 1]), abs(M22-Mm[1, 1]))
    # strictness: positive leading entry and positive determinant give M_m > 0,
    # which is the linear-independence conclusion of the Theorem 4.2 proof.
    assert errM < mp.mpf('1e-28') and Mm[0, 0] > 0 and mp.det(Mm) > 0, (a0, mm, errM)
print('PASS: ||u||^2, <u,v>, ||v||^2 match closed forms; N_m = Gram(xi,eta) eq. (4.9),'
      ' M_m = Gram(xi,sqrt(g) eta) eq. (4.10), rho_m>0, both matrices positive definite')

# --- the m=1 hypothesis a >= 1/2 is load-bearing, not ornamental ------------
# Theorem 4.2 restricts the m=1 Gram construction to a >= 1/2.  Below that the slack
# rho_1(a) = 1/g - (a-1/2)^2 psi_1(a) really does go negative, so eta_1 does not exist
# and the construction genuinely fails -- the hypothesis is not a convenience.
for a0 in [mp.mpf(s) for s in ('0.05', '0.1', '0.2', '0.3')]:
    _, q0, _, _, vnorm = gram_norms(a0, 1)
    rho1 = 1/mp.polygamma(1, a0) - vnorm
    assert rho1 < 0, (a0, rho1)
for a0 in [mp.mpf(s) for s in ('0.5', '1', '2.2', '9')]:
    _, q0, _, _, vnorm = gram_norms(a0, 1)
    rho1 = 1/mp.polygamma(1, a0) - vnorm
    assert rho1 >= 0, (a0, rho1)
print('PASS: rho_1(a) < 0 for small a and >= 0 for a >= 1/2, so Theorem 4.2\'s m=1'
      ' hypothesis a >= 1/2 is load-bearing')

print('ALL PASS: verify_gram')
