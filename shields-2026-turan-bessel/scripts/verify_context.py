#!/usr/bin/env python3
r"""Paper section 9 (Comparison with related positivity results), sec:context.

Section 9 (unnumbered displays):
  * the infinitesimal Turanian:
        Z(a+delta,lambda) Z(a-delta,lambda) - Z(a,lambda)^2 = -A(a,lambda) delta^2 + O(delta^4),
    both the identification [delta^2] = -A and the evenness in delta that kills every
    odd power, which is what makes the remainder O(delta^4) rather than O(delta^3);
  * the rescaling variance: with F(nu,y) = log I_nu(e^y), so that
        G_nu = -F_{nu nu},   P_nu = F_{nu y},   H_nu = 2(F_y - nu) - F_{yy}
    reproduce eqs. (2.7)-(2.9) under d/dy = Theta_z (checked here against the
    Theta_z forms, not assumed), replacing I_nu(e^y) by e^{cy} I_nu(e^y) leaves G_nu
    and P_nu unchanged but shifts H_nu by 2c, so the
    Schur determinant D_nu = G_nu(H_nu + 4/psi_1(nu+1)) - (1 + P_nu)^2, eq. (2.10),
    shifts to D_nu + 2 c G_nu;
  * the conclusion section 9 draws from that shift: since G_nu = A/Z^2 > 0, at any fixed
    z_0 > 0 every c < -D_nu(z_0)/(2 G_nu(z_0)) makes the rescaled determinant negative,
    so the sign of D_nu is not invariant under positive rescaling of the kernel and
    eq. (2.13) is not a rescaling-covariant confluent total-positivity minor.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

# ===========================================================================
# 1. Infinitesimal Turanian  Z(a+d)Z(a-d) - Z^2 = -A delta^2 + O(delta^4)
# ===========================================================================
a, lam, delta = sp.symbols('a lambda delta', positive=True)
K = 4

def Zsh(shift):
    return sum(lam**k/(sp.factorial(k)*sp.gamma(a+shift+k)) for k in range(K+1))

Zp, Zm, Z0 = Zsh(delta), Zsh(-delta), Zsh(0)
tur = sp.expand(Zp*Zm - Z0**2)

# A from the series definition (same route as the coefficient scripts).
psi  = lambda k: sp.digamma(a+k)
psi1 = lambda k: sp.polygamma(1, a+k)
Zser  = sum(lam**k/(sp.factorial(k)*sp.gamma(a+k)) for k in range(K+1))
Zaser = sum(-psi(k)*lam**k/(sp.factorial(k)*sp.gamma(a+k)) for k in range(K+1))
Zaaser = sum((psi(k)**2 - psi1(k))*lam**k/(sp.factorial(k)*sp.gamma(a+k)) for k in range(K+1))
A = Zaser**2 - Zser*Zaaser

for m in range(K):
    tur_m = tur.coeff(lam, m)
    d2 = sp.series(tur_m, delta, 0, 3).removeO().coeff(delta, 2)   # [delta^2]
    A_m = sp.series(A, lam, 0, m+1).removeO().coeff(lam, m)
    assert sp.simplify(sp.expand_func(d2 + A_m)) == 0, m            # [delta^2] = -A
print('PASS: [delta^2] of Z(a+d)Z(a-d) - Z^2 equals -A, degreewise in lambda')

# The remainder is O(delta^4), not O(delta^3): the product Z(a+d)Z(a-d) is invariant
# under d -> -d, so every odd power of delta vanishes identically.  Checking the
# symmetry is exact and settles all odd orders at once.
assert sp.simplify(sp.expand(tur.subs(delta, -delta) - tur)) == 0
print('PASS: the Turanian is even in delta, so no delta^1/delta^3 term: -A delta^2 + O(delta^4)')

# ===========================================================================
# 2. Rescaling variance (section 9): e^{cy} I_nu(e^y) shifts H_nu by 2c, hence the
#    Schur determinant by 2 c G_nu -- and a negative enough c flips its sign.
#    Section 9's contrast is that the total-positivity minors ARE preserved under such
#    a rescaling (a triangular action with positive diagonal on the confluent jet),
#    while this Schur determinant is not; only the second half is checkable here.
# ===========================================================================
mp.mp.dps = 30

def F(nu, yv):   return mp.log(mp.besseli(nu, mp.e**yv))
def G_(nu, yv):  return -mp.diff(lambda n_: F(n_, yv), nu, 2)          # -F_{nu nu}
def P_(nu, yv):  return mp.diff(lambda y: mp.diff(lambda n_: F(n_, y), nu), yv)  # F_{nu y}

def Hfun(Ffun, nu, yv):
    fy  = mp.diff(lambda y: Ffun(nu, y), yv)
    fyy = mp.diff(lambda y: Ffun(nu, y), yv, 2)
    return 2*(fy - nu) - fyy

# Section 9 rewrites eqs. (2.7)-(2.9) in the y variable via z = e^y, d/dy = Theta_z.
# That change of variable is the section's one silent step, so check the y-forms
# against the paper's Theta_z-forms directly rather than assuming they agree.
def G_theta(nu, z):     # eq. (2.7): -d_nu^2 log I_nu
    return -mp.diff(lambda n_: mp.log(mp.besseli(n_, z)), nu, 2)
def P_theta(nu, z):     # eq. (2.8): d_nu (z d_z log I_nu)
    return z*mp.diff(lambda zz: mp.diff(lambda n_: mp.log(mp.besseli(n_, zz)), nu), z)
def H_theta(nu, z):     # eq. (2.9): 2(z d_z log I_nu - nu) - (z d_z)^2 log I_nu
    L = lambda zz: mp.log(mp.besseli(nu, zz))
    f1, f2 = mp.diff(L, z, 1), mp.diff(L, z, 2)
    return 2*(z*f1 - nu) - (z*f1 + z**2*f2)

for nu, yv in [(mp.mpf('1.2'), mp.mpf('0.2')), (mp.mpf('-0.4'), mp.mpf('-0.7')),
               (mp.mpf('2.5'), mp.mpf('1.3'))]:
    z = mp.e**yv
    assert abs(G_(nu, yv) - G_theta(nu, z)) < mp.mpf('1e-25'), (nu, yv)
    assert abs(P_(nu, yv) - P_theta(nu, z)) < mp.mpf('1e-25'), (nu, yv)
    assert abs(Hfun(F, nu, yv) - H_theta(nu, z)) < mp.mpf('1e-25'), (nu, yv)
print('PASS: the F(nu,y) forms of section 9 agree with eqs. (2.7)-(2.9) under'
      ' z = e^y, d/dy = Theta_z')

c = mp.mpf('0.6')
for nu, yv in [(mp.mpf('1.2'), mp.mpf('0.2')), (mp.mpf('-0.4'), mp.mpf('-0.7')),
               (mp.mpf('0'), mp.mpf('1.1')), (mp.mpf('3.5'), mp.mpf('0.05'))]:
    Fresc = lambda n_, y: c*y + F(n_, y)
    H0, H1 = Hfun(F, nu, yv), Hfun(Fresc, nu, yv)
    G0 = G_(nu, yv)
    G1 = -mp.diff(lambda n_: Fresc(n_, yv), nu, 2)
    P0 = P_(nu, yv)
    P1 = mp.diff(lambda y: mp.diff(lambda n_: Fresc(n_, y), nu), yv)
    assert abs((H1 - H0) - 2*c) < mp.mpf('1e-28'), (nu, yv)    # H_nu -> H_nu + 2c
    assert abs(G1 - G0) < mp.mpf('1e-28') and abs(P1 - P0) < mp.mpf('1e-28'), (nu, yv)

    # the paper's own argument-independent correction, eq. (2.10)
    R = 4/mp.polygamma(1, nu + 1)
    D0 = G0*(H0 + R) - (1 + P0)**2
    D1 = G1*(H1 + R) - (1 + P1)**2
    assert abs((D1 - D0) - 2*c*G0) < mp.mpf('1e-27'), (nu, yv)  # D_nu += 2 c G_nu
    assert G0 > 0, (nu, yv)                                     # G_nu = A/Z^2 > 0
    assert D0 > 0, (nu, yv)                                     # thm:bessel at this sample

    # Non-invariance: every c < -D_nu/(2 G_nu) drives the rescaled determinant negative,
    # while just above that threshold it is still positive -- so the threshold is sharp
    # and the sign of D_nu is genuinely not rescaling-invariant.
    c_crit = -D0/(2*G0)
    for cneg in (c_crit - mp.mpf('0.5'), c_crit - mp.mpf('5')):
        Fneg = lambda n_, y: cneg*y + F(n_, y)
        assert G0*(Hfun(Fneg, nu, yv) + R) - (1 + P0)**2 < 0, (nu, yv, cneg)
    Fpos = lambda n_, y: (c_crit + mp.mpf('0.5'))*y + F(n_, y)
    assert G0*(Hfun(Fpos, nu, yv) + R) - (1 + P0)**2 > 0, (nu, yv)
print('PASS: rescaling e^{cy} I_nu(e^y) fixes G_nu, P_nu and shifts D_nu by 2 c G_nu;'
      ' c < -D_nu/(2 G_nu) makes it negative, so the sign is not rescaling-invariant')

print('ALL PASS: verify_context')
