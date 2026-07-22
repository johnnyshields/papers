#!/usr/bin/env python3
r"""Paper section 8 (Comparison with related positivity results).

Section 8 (unnumbered displays):
  * the infinitesimal Turanian:
        Z(a+delta,lambda) Z(a-delta,lambda) - Z(a,lambda)^2 = -A(a,lambda) delta^2 + O(delta^4);
  * the gauge variance: replacing I_s(e^y) by e^{cy} I_s(e^y) leaves G=-F_ss and p=F_sy
    (hence all total-positivity signs) unchanged but shifts H by 2c, so the Schur
    determinant D_s = G(H+4/psi_1(s+1))-(1+p)^2 shifts to D_s + 2cG.
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
print('PASS: Z(a+d)Z(a-d) - Z^2 = -A delta^2 + O(delta^4)')

# ===========================================================================
# 2. Gauge variance (section 8): e^{cy} I_s(e^y) shifts H by 2c, hence the Schur
#    determinant by 2cG
# ===========================================================================
mp.mp.dps = 30

def F(sv, yv):   return mp.log(mp.besseli(sv, mp.e**yv))
def G_(sv, yv):  return -mp.diff(lambda ss: F(ss, yv), sv, 2)
def p_(sv, yv):  return mp.diff(lambda y: mp.diff(lambda ss: F(ss, y), sv), yv)   # F_sy

def Hfun(Ffun, sv, yv):
    fy  = mp.diff(lambda y: Ffun(sv, y), yv)
    fyy = mp.diff(lambda y: Ffun(sv, y), yv, 2)
    return 2*(fy - sv) - fyy
c = mp.mpf('0.6')
for sv, yv in [(mp.mpf('1.2'), mp.mpf('0.2'))]:
    Fresc = lambda ss, y: c*y + F(ss, y)
    H0, H1 = Hfun(F, sv, yv), Hfun(Fresc, sv, yv)
    G0 = G_(sv, yv)
    G1 = -mp.diff(lambda ss: Fresc(ss, yv), sv, 2)
    p0 = p_(sv, yv)
    p1 = mp.diff(lambda y: mp.diff(lambda ss: Fresc(ss, y), sv), yv)
    assert abs((H1 - H0) - 2*c) < mp.mpf('1e-16')          # H -> H + 2c
    assert abs(G1 - G0) < mp.mpf('1e-16') and abs(p1 - p0) < mp.mpf('1e-16')
    kap0 = mp.mpf('1.3')                                    # any fixed correction
    D0 = G0*(H0 + kap0) - (1 + p0)**2
    D1 = G1*(H1 + kap0) - (1 + p1)**2
    assert abs((D1 - D0) - 2*c*G0) < mp.mpf('1e-15')       # Schur determinant += 2cG
print('PASS: rescaling e^{cy} I_s(e^y) leaves G,p fixed and shifts the Schur determinant by 2cG')

print('ALL PASS: verify_context')
