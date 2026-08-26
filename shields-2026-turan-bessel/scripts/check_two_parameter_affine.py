#!/usr/bin/env python3
r"""The two-parameter family and its affine determinant identity, built from the
series definition of Z rather than from the paper's coefficient formulas.

Paper labels (numbers move under renumbering, labels do not):
eq:Ckt-def, eq:Tkt, eq:PQdef, eq:affine-two-param (section `sec:main`);
eq:bessel-congruence, eq:Dkappa-tau-Delta (section `sec:scalar`);
eq:Delta0-tau (section `sec:main`).

Everything here is a second, independent route to identities the paper states
symbolically: the coefficient arrays of A, B and C_{kappa,tau} are assembled by
Cauchy convolution of the termwise Maclaurin coefficients of Z, Z_a, Z_aa,
Z_Theta, Z_ThetaTheta and Z_aTheta, with no Chu-Vandermonde input.

  * Delta^(kappa,tau) = Delta + (kappa-1) Q + (tau-1) P with P = A Z^2 and
    Q = g A Z Z_Theta, eq. (affine-two-param), coefficientwise;
  * both P and Q have strictly positive coefficients in every positive degree;
  * [lambda^0] Delta^(kappa,tau) = g(tau-1)/Gamma(a)^4, eq. (Delta0-tau);
  * the two-parameter congruence, in the determinant form
    D_nu^(kappa,tau)(2 sqrt lambda) = 4 Delta^(kappa,tau)(a,lambda)/(g Z^4),
    eq. (Dkappa-tau-Delta), against D_nu^(kappa,tau) evaluated from I_nu itself
    by numerical order and argument differentiation;
  * the slice tau=1 reproduces the one-parameter objects of the endpoint theory.
"""
from __future__ import annotations
import mpmath as mp

mp.mp.dps = 50


def coefficient_arrays(a, N):
    """Termwise Maclaurin coefficients of Z and the derivatives entering A, B, C."""
    z, za, zaa, zt, ztt, zat = ([mp.mpf(0)]*(N+1) for _ in range(6))
    for k in range(N+1):
        base = 1/(mp.factorial(k)*mp.gamma(a+k))
        psi, psi1 = mp.psi(0, a+k), mp.psi(1, a+k)
        z[k], za[k], zaa[k] = base, -psi*base, (psi**2 - psi1)*base
        zt[k], ztt[k], zat[k] = k*base, k*k*base, -k*psi*base
    return z, za, zaa, zt, ztt, zat


def cauchy(u, v, N):
    return [sum(u[i]*v[n-i] for i in range(n+1)) for n in range(N+1)]


def pieces(a, N):
    z, za, zaa, zt, ztt, zat = coefficient_arrays(a, N)
    A = [p - q for p, q in zip(cauchy(za, za, N), cauchy(z, zaa, N))]
    B = [p + q - r for p, q, r in
         zip(cauchy(z, z, N), cauchy(z, zat, N), cauchy(za, zt, N))]
    return A, B, cauchy(z, z, N), cauchy(z, zt, N), cauchy(z, ztt, N), cauchy(zt, zt, N)


def delta_coeffs(a, N, kappa=1, tau=1):
    """[lambda^n] Delta^(kappa,tau) for n <= N, from the definition eq. (Tkt)."""
    g = mp.psi(1, a)
    A, B, Z2, ZZt, ZZtt, Zt2 = pieces(a, N)
    C = [tau*Z2[n] + g*(kappa*ZZt[n] - ZZtt[n] + Zt2[n]) for n in range(N+1)]
    AC, B2 = cauchy(A, C, N), cauchy(B, B, N)
    return [AC[n] - g*B2[n] for n in range(N+1)]


def PQ_coeffs(a, N):
    """[lambda^n] P and [lambda^n] Q of eq. (PQdef)."""
    g = mp.psi(1, a)
    A, _, Z2, ZZt, _, _ = pieces(a, N)
    return cauchy(A, Z2, N), [g*c for c in cauchy(A, ZZt, N)]


def D_from_bessel(nu, z, kappa=1, tau=1):
    """D_nu^(kappa,tau)(z) from I_nu, by numerical order and argument derivatives."""
    g = mp.psi(1, nu+1)
    logI = lambda n_, z_: mp.log(mp.besseli(n_, z_))
    theta = lambda n_, z_: z_*mp.diff(lambda t_: logI(n_, t_), z_)
    G = -mp.diff(lambda n_: logI(n_, z), nu, 2)
    P = mp.diff(lambda n_: theta(n_, z), nu)
    theta2 = z*mp.diff(lambda t_: theta(nu, t_), z)
    H = 2*kappa*(theta(nu, z) - nu) - theta2
    return G*(H + 4*tau/g) - (1 + P)**2


N = 24
GRID = ['0.05', '0.3', '0.5', '1', '2.5', '10']
PARAMS = [(1, 1), (mp.mpf('2.3'), mp.mpf('0.4')), (mp.mpf('-0.7'), mp.mpf('3.1'))]
TOL = mp.mpf(10)**-35

for text in GRID:
    a = mp.mpf(text)
    g, base = mp.psi(1, a), delta_coeffs(a, N)
    p, q = PQ_coeffs(a, N)
    for kappa, tau in PARAMS:
        moved = delta_coeffs(a, N, kappa, tau)
        for n in range(N+1):
            claim = base[n] + (kappa-1)*q[n] + (tau-1)*p[n]
            assert abs(moved[n] - claim) <= TOL*max(abs(moved[n]), mp.mpf(1))
        assert abs(moved[0] - g*(tau-1)/mp.gamma(a)**4) <= TOL*max(abs(moved[0]), mp.mpf(1))
    assert all(p[n] > 0 and q[n] > 0 for n in range(1, N+1))
    assert abs(base[0]) <= TOL*g/mp.gamma(a)**4
print('PASS: Delta^(kappa,tau) = Delta + (kappa-1) Q + (tau-1) P, eq. (affine-two-param),')
print('      coefficientwise on an a-ladder; P and Q strictly positive in positive degree;')
print('      [lambda^0] Delta^(kappa,tau) = g(tau-1)/Gamma(a)^4, eq. (Delta0-tau)')

NSER = 220
for text in ['0.4', '1', '3']:
    a = mp.mpf(text)
    g, nu = mp.psi(1, a), a - 1
    for lam_text in ['0.35', '2.0', '9.0']:
        lam = mp.mpf(lam_text)
        Z = sum(lam**k/(mp.factorial(k)*mp.gamma(a+k)) for k in range(NSER))
        for kappa, tau in [(1, 1), (mp.mpf('1.7'), mp.mpf('0.3')),
                           (mp.mpf('0.6'), mp.mpf('2.2'))]:
            d = delta_coeffs(a, NSER, kappa, tau)
            summed = sum(d[n]*lam**n for n in range(NSER+1))
            lhs = D_from_bessel(nu, 2*mp.sqrt(lam), kappa, tau)
            rhs = 4*summed/(g*Z**4)
            assert abs(lhs - rhs) <= mp.mpf(10)**-18*abs(rhs), (text, lam_text, kappa, tau)
print('PASS: D_nu^(kappa,tau)(2 sqrt lambda) = 4 Delta^(kappa,tau)/(g Z^4),')
print('      eq. (Dkappa-tau-Delta), against I_nu itself for general (kappa,tau)')

print('ALL PASS')
