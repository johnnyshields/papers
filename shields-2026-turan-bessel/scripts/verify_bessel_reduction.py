#!/usr/bin/env python3
r"""Paper section 6 (Exact reduction from 0F1 to the Bessel inequality) and section
7 (Bessel consequences and sharpness); definitions G_nu/P_nu/H_nu/D_nu of section 2,
eqs. (2.7)-(2.10), and Theorem 2.4 / Corollary 2.5.

All arithmetic is arbitrary precision (mpmath).  With nu = a-1 and z = 2 sqrt(lambda),
    G_nu(z) = -d_nu^2 log I_nu(z),
    P_nu(z) = d_nu (z d_z log I_nu(z)),
    H_nu(z) = 2 (z d_z log I_nu(z) - nu) - (z d_z)^2 log I_nu(z),
    D_nu(z) = G_nu (H_nu + 4/psi_1(nu+1)) - (1 + P_nu)^2,
this verifies:

  * I_{a-1}(2 sqrt lambda) = lambda^{(a-1)/2} Z(a,lambda), eq. (6.1);
  * the bridge identities G_nu = A/Z^2, 1+P_nu = 2B/Z^2, H_nu+4/g = 4C/(g Z^2), eqs. (6.2)-(6.4),
    the matrix congruence eq. (6.5), hence the reduction D_{a-1}(2 sqrt lambda) =
    4 Delta(a,lambda)/(g Z^4), eq. (6.6);
  * the boundary-correction optimality D_{nu,R} = D_nu + G_nu(R-4/g), Proposition 2.6 (proof in section 7);
  * boundary limits G->psi_1(nu+1), H->0, P->1 and the rank-one z=0 matrix [[g,2],[2,4/g]]
    (Corollary 2.5);
  * small-z law D_nu(z) = 2(a psi_1(a)-1)/(a^3 psi_1(a)) z^2 + O(z^4), eq. (7.4);
  * the kappa-family small-z coefficient (2/(a^3 g))[(kappa-1)/2 (a g)^2 + a g - 1], eq. (7.2);
  * negative-order failure Delta_2(a) < 0 on -2<a<-1, Proposition 7.2, eq. (7.5), with the certificate.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

mp.mp.dps = 50

def logI(nu, z):
    return mp.log(mp.besseli(nu, z))

def zdz(f, z):                       # z d/dz  of a one-variable function f(z)
    return z*mp.diff(f, z)

def G(nu, z):
    return -mp.diff(lambda n: logI(n, z), nu, 2)
def P(nu, z):
    return z*mp.diff(lambda zz: mp.diff(lambda n: logI(n, zz), nu), z)
def H(nu, z):
    U = zdz(lambda zz: logI(nu, zz), z)
    f1 = mp.diff(lambda zz: logI(nu, zz), z, 1)
    f2 = mp.diff(lambda zz: logI(nu, zz), z, 2)
    UU = z*f1 + z**2*f2                # (z d_z)^2 log I
    return 2*(U - nu) - UU
def Hk(nu, z, kappa):                 # kappa-family H^(kappa) eq. (2.11), D^(kappa) eq. (2.12)
    U = zdz(lambda zz: logI(nu, zz), z)
    f1 = mp.diff(lambda zz: logI(nu, zz), z, 1)
    f2 = mp.diff(lambda zz: logI(nu, zz), z, 2)
    UU = z*f1 + z**2*f2
    return 2*kappa*(U - nu) - UU
def Dnu(nu, z):
    return G(nu, z)*(H(nu, z) + 4/mp.polygamma(1, nu+1)) - (1 + P(nu, z))**2
def Dk(nu, z, kappa):
    return G(nu, z)*(Hk(nu, z, kappa) + 4/mp.polygamma(1, nu+1)) - (1 + P(nu, z))**2

def Z(a, lam):
    return mp.nsum(lambda k: lam**k/(mp.factorial(k)*mp.gamma(a+k)), [0, mp.inf])

def ABCDelta(a, lam, kappa=mp.mpf(1)):
    """A, B, C_kappa, Delta from series moments of Z (independent of the Bessel side)."""
    Zs = Za = Zaa = Zt = Ztt = Zat = mp.mpf(0)
    term = 1/mp.gamma(a)
    for k in range(20000):
        ps = mp.digamma(a+k); tr = mp.polygamma(1, a+k)
        Zs += term; Za += -ps*term; Zaa += (ps**2 - tr)*term
        Zt += k*term; Ztt += k*k*term; Zat += -k*ps*term
        term *= lam/((k+1)*(a+k))
        if k > 30 and abs(term) < mp.mpf('1e-55')*max(1, abs(Zs)):
            break
    g = mp.polygamma(1, a)
    A = Za**2 - Zs*Zaa
    B = Zs**2 + Zs*Zat - Za*Zt
    C = Zs**2 + g*(kappa*Zs*Zt - Zs*Ztt + Zt**2)
    return A, B, C, A*C - g*B**2, Zs, g

def loglog_slope(f, z0, ratio=mp.mpf(2)):
    z1 = z0/ratio
    return mp.log(abs(f(z0)/f(z1)))/mp.log(z0/z1)

# ---------------------------------------------------------------------------
# eq. (6.1): I_{a-1}(2 sqrt lambda) = lambda^{(a-1)/2} Z(a,lambda)
# ---------------------------------------------------------------------------
for a, lam in [(mp.mpf('1.3'), mp.mpf('0.7')), (mp.mpf('0.4'), mp.mpf('2')), (mp.mpf('3'), mp.mpf('5'))]:
    lhs = mp.besseli(a-1, 2*mp.sqrt(lam))
    rhs = lam**((a-1)/2)*Z(a, lam)
    assert abs(lhs - rhs)/abs(lhs) < mp.mpf('1e-40')
print('PASS: I_{a-1}(2 sqrt lambda) = lambda^{(a-1)/2} Z(a,lambda)')

# ---------------------------------------------------------------------------
# Bridge identities and reduction D = 4 Delta/(g Z^4)
# ---------------------------------------------------------------------------
for a, lam in [(mp.mpf('1.3'), mp.mpf('0.7')), (mp.mpf('0.4'), mp.mpf('0.2')), (mp.mpf('3'), mp.mpf('5'))]:
    nu = a - 1; z = 2*mp.sqrt(lam)
    A, B, C, Delta, Zs, g = ABCDelta(a, lam)
    assert abs(G(nu, z) - A/Zs**2) < mp.mpf('1e-38')
    assert abs((1 + P(nu, z)) - 2*B/Zs**2) < mp.mpf('1e-38')
    assert abs((H(nu, z) + 4/g) - 4*C/(g*Zs**2)) < mp.mpf('1e-38')
    assert abs(Dnu(nu, z) - 4*Delta/(g*Zs**4))/abs(Dnu(nu, z)) < mp.mpf('1e-38')
print('PASS: bridge identities G=A/Z^2, 1+P=2B/Z^2, H+4/g=4C/(gZ^2), and D=4 Delta/(g Z^4)')

# ---------------------------------------------------------------------------
# Matrix congruence eq. (6.5): the Bessel-Schur matrix equals
# (1/Z^2) diag(1, 2/sqrt g) T diag(1, 2/sqrt g).
# ---------------------------------------------------------------------------
for a, lam in [(mp.mpf('1.3'), mp.mpf('0.7')), (mp.mpf('0.4'), mp.mpf('0.2')), (mp.mpf('3'), mp.mpf('5'))]:
    nu = a - 1; z = 2*mp.sqrt(lam)
    A, B, C, Delta, Zs, g = ABCDelta(a, lam)
    T = mp.matrix([[A, mp.sqrt(g)*B], [mp.sqrt(g)*B, C]])
    Dg = mp.matrix([[1, 0], [0, 2/mp.sqrt(g)]])
    RHS = (Dg*T*Dg)*(1/Zs**2)
    MBS = mp.matrix([[G(nu, z), 1 + P(nu, z)], [1 + P(nu, z), H(nu, z) + 4/g]])
    assert max(abs(MBS[i, j] - RHS[i, j]) for i in range(2) for j in range(2)) < mp.mpf('1e-36')
print('PASS: Bessel-Schur congruence = (1/Z^2) diag(1,2/sqrt g) T diag(1,2/sqrt g)')

# ---------------------------------------------------------------------------
# Boundary-correction optimality, Proposition 2.6 (proof in section 7): with H+R in place of H+4/g,
# D_{nu,R} = D_nu + G_nu (R - 4/g), and D_{nu,R}(z) -> psi_1(nu+1) R - 4 as z->0.
# ---------------------------------------------------------------------------
def DnuR(nu, z, Rval):
    return G(nu, z)*(H(nu, z) + Rval) - (1 + P(nu, z))**2
for a in [mp.mpf('1.3'), mp.mpf('0.4')]:
    nu = a - 1; g = mp.polygamma(1, a); z = 2*mp.sqrt(mp.mpf('0.5'))
    for Rval in [mp.mpf('3'), 4/g, mp.mpf('7')]:
        assert abs((DnuR(nu, z, Rval) - Dnu(nu, z)) - G(nu, z)*(Rval - 4/g)) < mp.mpf('1e-34')
    z0 = mp.mpf('1e-4')
    for Rval in [mp.mpf('2'), mp.mpf('6')]:
        assert abs(DnuR(nu, z0, Rval) - (mp.polygamma(1, nu+1)*Rval - 4)) < mp.mpf('1e-5')
print('PASS: D_{nu,R} = D_nu + G(R-4/g); D_{nu,R}(z) -> psi_1(nu+1) R - 4 as z->0')

# ---------------------------------------------------------------------------
# Boundary limits and the rank-one z=0 matrix
# ---------------------------------------------------------------------------
for a in [mp.mpf('1.3'), mp.mpf('0.4'), mp.mpf('2.5')]:
    nu = a - 1; g = mp.polygamma(1, a); z = mp.mpf('1e-4')
    assert abs(G(nu, z) - mp.polygamma(1, nu+1)) < mp.mpf('1e-6')
    assert abs(H(nu, z)) < mp.mpf('1e-6')
    assert abs(P(nu, z) - 1) < mp.mpf('1e-6')
    Mat = mp.matrix([[G(nu, z), 1 + P(nu, z)], [1 + P(nu, z), H(nu, z) + 4/mp.polygamma(1, nu+1)]])
    lim = mp.matrix([[g, 2], [2, 4/g]])
    assert max(abs(Mat[i, j] - lim[i, j]) for i in range(2) for j in range(2)) < mp.mpf('1e-6')
    assert abs(mp.det(lim)) < mp.mpf('1e-40')
print('PASS: G->psi_1(nu+1), H->0, P->1; z=0 matrix [[g,2],[2,4/g]] is rank one')

# ---------------------------------------------------------------------------
# small-z expansion, eq. (7.4), with slope-2 rate fit
# ---------------------------------------------------------------------------
for a in [mp.mpf('1.3'), mp.mpf('0.4'), mp.mpf('2.5')]:
    nu = a - 1
    coeff = 2*(a*mp.polygamma(1, a) - 1)/(a**3*mp.polygamma(1, a))
    slope = loglog_slope(lambda zz: Dnu(nu, zz), mp.mpf('1e-3'))
    assert abs(slope - 2) < mp.mpf('1e-4'), (a, slope)
    z = mp.mpf('1e-4')
    assert abs(Dnu(nu, z)/z**2 - coeff)/abs(coeff) < mp.mpf('1e-6')
print('PASS: D_nu(z) = 2(a psi_1(a)-1)/(a^3 psi_1(a)) z^2 + O(z^4), slope 2')

# ---------------------------------------------------------------------------
# kappa-family small-z coefficient, eq. (7.2)
# ---------------------------------------------------------------------------
for a in [mp.mpf('1.3'), mp.mpf('0.6')]:
    nu = a - 1; g = mp.polygamma(1, a)
    for kappa in [mp.mpf('1'), mp.mpf('1.5'), mp.mpf('0.5')]:
        pred = 2/(a**3*g)*((kappa-1)/2*(a*g)**2 + a*g - 1)
        z = mp.mpf('1e-4')
        assert abs(Dk(nu, z, kappa)/z**2 - pred)/abs(pred) < mp.mpf('1e-5'), (a, kappa)
print('PASS: kappa-family small-z coefficient (2/(a^3 g))[(kappa-1)/2 (a g)^2 + a g - 1]')

# ---------------------------------------------------------------------------
# negative-order failure Delta_2(a) < 0 on -2 < a < -1, Proposition 7.2, eq. (7.5)
# ---------------------------------------------------------------------------
def Delta2_Q(a):
    t = mp.polygamma(1, a+1); Ra = t - 1/(a+1)
    Q = (2*a**4*(a+1)**2*Ra**2 + 2*a**2*(a+1)**2*(8*a**2+3*a+1)*Ra + 2*a*(a+1)*(5*a+3))
    return Q/(2*a**6*(a+1)**3*mp.gamma(a)**4)
for a in [mp.mpf(s) for s in ('-1.05', '-1.2', '-1.5', '-1.8', '-1.95')]:
    assert Delta2_Q(a) < 0, a
# polynomial certificate: 8b^3-3b^2-4b+3 > 0 for b>=1.  bracket(1)=4; its derivative
# d=24b^2-6b-4 is an upward parabola with vertex b*=1/8<1, so d is increasing on [1,inf)
# from d(1)=14>0, whence bracket is increasing on [1,inf) from bracket(1)=4>0.
b = sp.symbols('b', positive=True)
bracket = 8*b**3 - 3*b**2 - 4*b + 3
d = sp.diff(bracket, b)
assert bracket.subs(b, 1) == 4
assert d.subs(b, 1) == 14
assert d.coeff(b, 2) > 0 and -d.coeff(b, 1)/(2*d.coeff(b, 2)) < 1     # vertex < 1
print('PASS: Delta_2(a) < 0 on -2<a<-1, with polynomial certificate 8b^3-3b^2-4b+3>0 (b>=1)')

print('ALL PASS: verify_bessel_reduction')
