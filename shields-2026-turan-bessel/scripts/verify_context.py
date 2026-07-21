#!/usr/bin/env python3
r"""Paper section 9 (Comparison with related positivity results) and Appendix A
(Confluent minors of the modified Bessel kernel).

Section 9 (unnumbered displays unless noted):
  * the infinitesimal Turanian:
        Z(a+delta,lambda) Z(a-delta,lambda) - Z(a,lambda)^2 = -A(a,lambda) delta^2 + O(delta^4);
  * the gauge variance: replacing I_s(e^y) by e^{cy} I_s(e^y) leaves G=-F_ss and p=F_sy
    (hence all total-positivity signs) unchanged but shifts H by 2c, so the Schur
    determinant D_s = G(H+4/psi_1(s+1))-(1+p)^2 shifts to D_s + 2cG;
  * the large-argument expansion d_s(x d_x log I_s(x)) = s/x + O(x^{-2}), from the Hankel
    expansion eq. (9.1).

Appendix A, Proposition A.1 (the total-positivity confluence, F(s,y)=log I_s(e^y)):
  * the logarithmic Bessel equation F_yy+F_y^2=e^{2y}+s^2, its first and second
    s-derivatives p_y+2F_y p=2s and G_yy=2p^2-2F_y G_y-2, the order-3 confluent Wronskian
    reduction 2p^3-p G_yy+p_y G_y=2(p+s G_y), eq. (A.1), and the TP2/TP3 signs p>=0, p+sG_y>=0.
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
# 2. Confluence Wronskian reduction, Appendix A / Prop. A.1, eq. (A.1)
#    (symbolic, from the two differentiated relations)
# ===========================================================================
p, py, Fy, Gy, Gyy, s = sp.symbols('p py Fy Gy Gyy s')
py_rel  = 2*s - 2*Fy*p             # from p_y + 2 F_y p = 2s
Gyy_rel = 2*p**2 - 2*Fy*Gy - 2     # from second s-derivative
wronskian = 2*p**3 - p*Gyy + py*Gy
assert sp.expand(wronskian.subs({Gyy: Gyy_rel, py: py_rel}) - 2*(p + s*Gy)) == 0
print('PASS: 2p^3 - p G_yy + p_y G_y = 2(p + s G_y)  (symbolic reduction)')

# ===========================================================================
# 2b. The same relations hold numerically for F(s,y) = log I_s(e^y)
# ===========================================================================
mp.mp.dps = 30

def F(sv, yv):   return mp.log(mp.besseli(sv, mp.e**yv))
def Fy_(sv, yv): return mp.diff(lambda y: F(sv, y), yv)
def Fyy_(sv, yv):return mp.diff(lambda y: F(sv, y), yv, 2)
def G_(sv, yv):  return -mp.diff(lambda ss: F(ss, yv), sv, 2)
def Gy_(sv, yv): return mp.diff(lambda y: G_(sv, y), yv)
def Gyy_(sv, yv):return mp.diff(lambda y: G_(sv, y), yv, 2)
def p_(sv, yv):  return mp.diff(lambda y: mp.diff(lambda ss: F(ss, y), sv), yv)   # F_sy
def py_(sv, yv): return mp.diff(lambda y: p_(sv, y), yv)

for sv, yv in [(mp.mpf('1.5'), mp.mpf('0.3')), (mp.mpf('0.7'), mp.mpf('-0.4'))]:
    fy, fyy = Fy_(sv, yv), Fyy_(sv, yv)
    pp, pyy = p_(sv, yv), py_(sv, yv)
    gy, gyy = Gy_(sv, yv), Gyy_(sv, yv)
    assert abs(fyy + fy**2 - (mp.e**(2*yv) + sv**2)) < mp.mpf('1e-18')     # log-Bessel PDE
    assert abs(pyy + 2*fy*pp - 2*sv) < mp.mpf('1e-16')                     # p_y + 2 F_y p = 2s
    assert abs(gyy - (2*pp**2 - 2*fy*gy - 2)) < mp.mpf('1e-14')           # G_yy relation
    assert abs((2*pp**3 - pp*gyy + pyy*gy) - 2*(pp + sv*gy)) < mp.mpf('1e-14')
    assert pp > 0                                                          # TP2: p >= 0
    assert pp + sv*gy > 0                                                  # TP3: p + s G_y >= 0
print('PASS: log-Bessel PDE, p_y/G_yy relations, Wronskian, and TP2/TP3 signs for I_s(e^y)')

# ===========================================================================
# 3. Gauge variance (section 9): e^{cy} I_s(e^y) shifts H by 2c, hence the Schur
#    determinant by 2cG
# ===========================================================================
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

# ===========================================================================
# 4. Large-argument behaviour (section 9): the Hankel expansion eq. (9.1)
#    I_s(x) = e^x/sqrt(2 pi x) (1 - (4s^2-1)/(8x) + O(x^{-2})), and the consequence
#    d_s(x d_x log I_s(x)) = s/x + O(x^{-2}).
# ===========================================================================
def hankel_lead(sv, xv):     # (I_s(x) sqrt(2 pi x)/e^x - 1) * x  ->  -(4s^2-1)/8
    return (mp.besseli(sv, xv)*mp.sqrt(2*mp.pi*xv)/mp.e**xv - 1)*xv
for sv in [mp.mpf('0.7'), mp.mpf('2.0')]:
    assert abs(hankel_lead(sv, mp.mpf('400')) - (-(4*sv**2 - 1)/8)) < mp.mpf('1e-2')

def dsq(sv, xv):    # d_s ( x d_x log I_s(x) )
    return mp.diff(lambda ss: xv*mp.diff(lambda x: mp.log(mp.besseli(ss, x)), xv), sv)
for sv in [mp.mpf('0.7'), mp.mpf('2.0')]:
    for xv in [mp.mpf('50'), mp.mpf('100'), mp.mpf('200')]:
        resid = (dsq(sv, xv) - sv/xv)*xv**2      # O(1) if the remainder is O(x^{-2})
        assert abs(resid) < mp.mpf('5'), (sv, xv, resid)
        assert abs(xv*dsq(sv, xv) - sv) < mp.mpf('0.1')   # x * d_s(...) -> s
print('PASS: Hankel expansion (9.1) and d_s(x d_x log I_s(x)) = s/x + O(x^{-2})')

print('ALL PASS: verify_context')
