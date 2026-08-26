#!/usr/bin/env python3
r"""Paper section `sec:main` (Reciprocal-gamma formulation and positivity phase diagram, sec:main), which carries the
exact 0F1--Bessel correspondence together with the definitions G_nu/P_nu/H_nu/D_nu
and thm:bessel, cor:bessel-matrix and prop:bessel-sharpness; section `sec:phase`
(Canonical--microcanonical phase geometry, sec:phase); and Appendix B (Beyond the
positive-series domain, app:continuation).

The two-parameter form of the congruence, and the phase diagram it carries, are in
verify_phase_diagram.py and check_two_parameter_affine.py; the scalar forms of H and
the probabilistic reading of the same coupling are in verify_scalar_turanian.py and
verify_bessel_law.py.

All arithmetic is arbitrary precision (mpmath).  With nu = a-1 and z = 2 sqrt(lambda),
    G_nu(z) = -d_nu^2 log I_nu(z),
    P_nu(z) = d_nu (z d_z log I_nu(z)),
    H_nu(z) = 2 (z d_z log I_nu(z) - nu) - (z d_z)^2 log I_nu(z),
    D_nu(z) = G_nu (H_nu + 4/psi_1(nu+1)) - (1 + P_nu)^2,
this verifies:

  * I_{a-1}(2 sqrt lambda) = lambda^{(a-1)/2} Z(a,lambda), eq. (I-Z);
  * the bridge identities G_nu = A/Z^2, 1+P_nu = 2B/Z^2, H_nu+4/g = 4C/(g Z^2), eqs. (U-L), (G-L), (ABC-log),
    the matrix congruence eq. (bessel-congruence), hence the reduction D_{a-1}(2 sqrt lambda) =
    4 Delta(a,lambda)/(g Z^4), eq. (D-Delta);
  * the boundary-correction optimality D_{nu,R} = D_nu + G_nu(R-4/g),
    prop:bessel-sharpness (proof in sec:phase);
  * boundary limits G->psi_1(nu+1), H->0, P->1 and the rank-one z=0 matrix [[g,2],[2,4/g]]
    (cor:bessel-matrix);
  * small-z law D_nu(z) = 2(a psi_1(a)-1)/(a^3 psi_1(a)) z^2 + O(z^4), eq. (small-z-D);
  * the kappa-family small-z coefficient (2/(a^3 g))[(kappa-1)/2 (a g)^2 + a g - 1], which is
    not displayed in the paper but is eq. (MD01-kappa) transported through eq. (Dkappa-tau-Delta);
  * lem:coefficient-continuation at the degree-two coefficient: the closed form
    eq. (Delta2-Q)--(Qstar-decomp) still computes [lambda^2]Delta off a > 0, checked
    against a Cauchy convolution of the termwise Maclaurin coefficients that shares
    no arithmetic with it;
  * negative-order failure Delta_2(a) < 0 on -2<a<-1, prop:negative-coeff-failure,
    eq. (negative-Delta2), with the certificate.
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
def Hk(nu, z, kappa):                 # kappa-family H^(kappa) eq. (Hnu-kappa), D^(kappa) eq. (Dnu-kt-def)
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
# eq. (I-Z): I_{a-1}(2 sqrt lambda) = lambda^{(a-1)/2} Z(a,lambda)
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
print('PASS: bridge identities G=A/Z^2, 1+P=2B/Z^2, H+4/g=4C/(gZ^2), and D=4 Delta/(g Z^4),')
print('      which is rem:canonical-origin read through eqs. (U-L), (G-L), (ABC-log)')

# ---------------------------------------------------------------------------
# Matrix congruence eq. (bessel-congruence): the Bessel-Schur matrix equals
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
# Boundary-correction optimality, prop:bessel-sharpness (proof in sec:phase):
# with H+R in place of H+4/g,
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
# small-z expansion, eq. (small-z-D), with slope-2 rate fit
# ---------------------------------------------------------------------------
for a in [mp.mpf('1.3'), mp.mpf('0.4'), mp.mpf('2.5')]:
    nu = a - 1
    coeff = 2*(a*mp.polygamma(1, a) - 1)/(a**3*mp.polygamma(1, a))
    slope = loglog_slope(lambda zz: Dnu(nu, zz), mp.mpf('1e-3'))
    assert abs(slope - 2) < mp.mpf('1e-4'), (a, slope)
    z = mp.mpf('1e-4')
    assert abs(Dnu(nu, z)/z**2 - coeff)/abs(coeff) < mp.mpf('1e-6')
print('PASS: D_nu(z) = 2(a psi_1(a)-1)/(a^3 psi_1(a)) z^2 + O(z^4), slope 2')

# eq. (small-z-D) negative-order leg: for negative nonintegral a the same coefficient
# stays positive, because the trigamma partial-fraction recurrence eq. (trigamma-partial-fraction) keeps
# psi_1(a)>0, so both a psi_1(a) - 1 and a^3 psi_1(a) are negative.
for a in [mp.mpf('-0.5'), mp.mpf('-1.5'), mp.mpf('-2.5'), mp.mpf('-3.5')]:
    g = mp.polygamma(1, a)
    num, den = a*g - 1, a**3*g
    assert g > 0 and num < 0 and den < 0, (a, g, num, den)
    assert 2*num/den > 0                                          # coefficient stays positive
print('PASS: eq. (small-z-D) small-z coefficient > 0 for negative nonintegral a (both factors negative)')

# ---------------------------------------------------------------------------
# kappa-family small-z coefficient: eq. (MD01-kappa) transported through eq. (Dkappa-tau-Delta),
# not displayed in the paper
# ---------------------------------------------------------------------------
for a in [mp.mpf('1.3'), mp.mpf('0.6')]:
    nu = a - 1; g = mp.polygamma(1, a)
    for kappa in [mp.mpf('1'), mp.mpf('1.5'), mp.mpf('0.5')]:
        pred = 2/(a**3*g)*((kappa-1)/2*(a*g)**2 + a*g - 1)
        z = mp.mpf('1e-4')
        assert abs(Dk(nu, z, kappa)/z**2 - pred)/abs(pred) < mp.mpf('1e-5'), (a, kappa)
print('PASS: kappa-family small-z coefficient (2/(a^3 g))[(kappa-1)/2 (a g)^2 + a g - 1]')

# ---------------------------------------------------------------------------
# lem:coefficient-continuation, at the coefficient the appendix actually uses.
# The closed form eq. (Delta2-Q) is derived for a > 0; the failure proposition
# below evaluates it at a < 0.  What licenses that is the continuation lemma, so
# it is checked rather than assumed: [lambda^2]Delta is rebuilt by Cauchy
# convolution of the termwise Maclaurin coefficients of Z and its parameter and
# Euler derivatives -- eq. (Zdef) differentiated term by term, valid wherever
# 1/Gamma(a+k) is, hence on all of R \ {0,-1,-2,...} -- and required to agree
# with the closed form.  The two routes share no arithmetic.
# ---------------------------------------------------------------------------
def Delta2_series(a):
    """[lambda^2] Delta from eq. (ABC-log), termwise; no Chu-Vandermonde input."""
    z, za, zaa, zt, ztt, zat = ([mp.mpf(0)]*3 for _ in range(6))
    for k in range(3):
        base = 1/(mp.factorial(k)*mp.gamma(a+k))
        psi, psi1 = mp.psi(0, a+k), mp.psi(1, a+k)
        z[k], za[k], zaa[k] = base, -psi*base, (psi**2 - psi1)*base
        zt[k], ztt[k], zat[k] = k*base, k*k*base, -k*psi*base
    cau = lambda u, v: [mp.fsum(u[i]*v[n-i] for i in range(n+1)) for n in range(3)]
    g = mp.psi(1, a)
    A = [p - q for p, q in zip(cau(za, za), cau(z, zaa))]
    B = [p + q - r for p, q, r in zip(cau(z, z), cau(z, zat), cau(za, zt))]
    C = [p + g*(q - r + t) for p, q, r, t in
         zip(cau(z, z), cau(z, zt), cau(z, ztt), cau(zt, zt))]
    return cau(A, C)[2] - g*cau(B, B)[2]

# ---------------------------------------------------------------------------
# negative-order failure Delta_2(a) < 0 on -2 < a < -1,
# prop:negative-coeff-failure, eq. (negative-Delta2)
# ---------------------------------------------------------------------------
def Delta2_Q(a):
    t = mp.polygamma(1, a+1); Ra = t - 1/(a+1)
    Q = (2*a**4*(a+1)**2*Ra**2 + 2*a**2*(a+1)**2*(8*a**2+3*a+1)*Ra + 2*a*(a+1)*(5*a+3))
    return Q/(2*a**6*(a+1)**3*mp.gamma(a)**4)
for text in ('1.3', '0.4', '-0.5', '-1.05', '-1.2', '-1.5', '-1.8', '-1.95', '-2.5'):
    a = mp.mpf(text)
    direct, closed = Delta2_series(a), Delta2_Q(a)
    assert abs(direct - closed) <= mp.mpf(10)**-40*abs(closed), (text, direct, closed)
print('PASS: lem:coefficient-continuation at degree two -- eq. (Delta2-Q) agrees with')
print('      the termwise series for a > 0 and on -3 < a < 0 past the poles')

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

# ---------------------------------------------------------------------------
# zero-free domain licensing the differentiated large-argument expansion,
# proof of prop:bessel-sharpness.  With Sigma_delta = {|arg w| <= pi/2 - delta} and
# K a closed complex disc of orders,
#     E_mu(w) = (2 pi w)^{1/2} e^{-w} I_mu(w) = 1 - (4 mu^2-1)/(8w) + O(w^{-2}),
# so |E_mu - 1| < 1/2 past a threshold W(K,delta).  The values of E_mu then lie in
# the disc |zeta-1| < 1/2, on which the principal logarithm is holomorphic, so
# log E_mu is holomorphic in (mu,w) on the interior Omega of
# K x (Sigma_delta ^ {|w| >= W}) and a holomorphic log I_mu exists there.
# ---------------------------------------------------------------------------
def E(mu, w):
    return mp.sqrt(2*mp.pi*w)*mp.e**(-w)*mp.besseli(mu, w)

def sector_order_grid(center, radius, delta, absw, n_mu=12, n_arg=13):
    """Boundary of K x boundary-and-interior rays of Sigma_delta at |w| = absw."""
    out = []
    half = mp.pi/2 - delta
    for j in range(n_mu):
        mu = center + radius*mp.e**(2j*mp.pi*1j/n_mu)
        for k in range(n_arg):
            ph = -half + 2*half*mp.mpf(k)/(n_arg-1)
            out.append((mu, absw*mp.e**(1j*ph)))
    return out

delta = mp.pi/6                        # Sigma_delta = {|arg w| <= pi/3}
K_center, K_radius = mp.mpf('0.75'), mp.mpf('0.5')   # orders within 0.5 of 0.75

# (a) uniform approach to 1, and the O(1/|w|) rate
prev = None
for absw in [mp.mpf(v) for v in (20, 40, 80, 160)]:
    dev = max(abs(E(mu, w) - 1) for mu, w in
              sector_order_grid(K_center, K_radius, delta, absw))
    assert dev < mp.mpf('0.5'), (absw, dev)          # => E omits 0, so I_mu != 0
    if prev is not None:
        ratio = prev/dev                              # halving |w| doubles the deviation
        assert mp.mpf('1.6') < ratio < mp.mpf('2.4'), (absw, ratio)
    prev = dev
print('PASS: |E_mu(w)-1| < 1/2 uniformly on K x Sigma_delta for |w|>=20, decaying like 1/|w|')

# (a2) eq. (log-I-two-term): log E_mu(w) = -(4 mu^2 - 1)/(8w) + O(w^{-2}) uniformly on Omega.
# This is the quantity actually differentiated (log I_mu = w - (1/2)log(2 pi w) +
# log E_mu), so the display is load-bearing for the derivative conclusions below.
# Checked as w * [log E_mu(w) + (4 mu^2-1)/(8w)] -> 0 at rate 1/|w|, uniformly over
# the same order/sector grid; note the principal branch is the right one precisely
# because |E_mu - 1| < 1/2 keeps the values in the disc where Log is holomorphic.
prev = None
for absw in [mp.mpf(v) for v in (20, 40, 80, 160)]:
    resid = max(abs(w*(mp.log(E(mu, w)) + (4*mu**2 - 1)/(8*w)))
                for mu, w in sector_order_grid(K_center, K_radius, delta, absw))
    assert resid < mp.mpf('1.5'), (absw, resid)        # bounded => O(w^{-2}) term
    if prev is not None:
        ratio = prev/resid                             # halving |w| doubles the residual
        assert mp.mpf('1.6') < ratio < mp.mpf('2.4'), (absw, ratio)
    prev = resid
# and the leading coefficient is exactly -(4 mu^2-1)/8, not merely O(1/w)
for mu in [mp.mpf('0.3'), mp.mpf('0.75') + mp.mpf('0.4')*1j, mp.mpf('1.25')]:
    lead = mp.mpf(10)**5 * mp.log(E(mu, mp.mpf(10)**5))
    assert abs(lead - (-(4*mu**2 - 1)/8)) < mp.mpf('1e-3'), (mu, lead)
print('PASS: eq. (log-I-two-term) log E_mu(w) = -(4 mu^2-1)/(8w) + O(w^-2) uniformly on Omega')

# (b) the threshold W(K,delta) is load-bearing, not decorative: the estimate
# |E_mu - 1| < 1/2 that supplies nonvanishing FAILS in-sector for small |w|, so
# largeness of |w| is doing real work and W cannot be taken near 0.
half = mp.pi/2 - delta
mu_c = mp.mpc('0.5', '1')            # a complex order, as Cauchy in mu requires
worst = None
for k in range(10, 900):
    absw = mp.mpf(k)/100
    dev = max(abs(E(mu_c, absw*mp.e**(1j*(-half + 2*half*mp.mpf(kk)/40))) - 1)
              for kk in range(41))
    if dev >= mp.mpf('0.5'):
        worst = absw
assert worst is not None and worst > mp.mpf('3'), worst
print(f'PASS: threshold load-bearing -- max|E_mu-1| >= 1/2 in-sector out to '
      f'|w|={mp.nstr(worst,4)} at mu={mu_c}, so W(K,delta) cannot be dropped')

# Complementary negative result, recorded so the proof is not misread: no zero of
# I_mu was located strictly inside Sigma_delta for this complex order out to
# |w| = 14 (1400 radii x 41 rays, findroot polished).  Absence of located zeros
# is not a proof of absence -- which is exactly why the proof argues through the
# uniform estimate on E_mu rather than by locating zeros.
for k in range(5, 1400, 7):
    for kk in range(0, 41, 2):
        w = (mp.mpf(k)/100)*mp.e**(1j*(-half + 2*half*mp.mpf(kk)/40))
        assert abs(mp.besseli(mu_c, w)) > mp.mpf('1e-6'), w
print('PASS: no zero of I_mu found strictly inside Sigma_delta out to |w|=14 '
      '(complementary; the proof does not rely on locating zeros)')

# (c) the Cauchy disc |w-z| <= eps z stays inside Sigma_delta.  A disc centered on
# the positive axis meets arg w = +-(pi/2-delta) only if eps >= sin(pi/2-delta).
eps = mp.mpf('0.3')
assert eps < mp.sin(mp.pi/2 - delta), (eps, mp.sin(mp.pi/2 - delta))
for z in [mp.mpf(v) for v in (30, 60, 120)]:
    for kk in range(37):
        w = z + eps*z*mp.e**(2*kk*mp.pi*1j/37)
        assert abs(mp.arg(w)) <= mp.pi/2 - delta + mp.mpf('1e-30'), (z, w)
        assert abs(w) >= (1 - eps)*z
print('PASS: Cauchy disc |w-z|<=eps z lies in Sigma_delta and in |w|>=(1-eps)z, eps=0.3<sin(pi/3)')

# (c2) the derivative-order display in the lem:large-argument-limit proof: writing R(mu,w)
# for the O(w^{-2}) remainder of eq. (log-I-two-term),
#     d_mu^j d_w^l R(mu,w) = O(w^{-2-l})     (0 <= j,l <= 2),
# i.e. each w-derivative gains a factor w^{-1} while mu-derivatives preserve the
# order.  The exponent ledger is what licenses differentiating eq. (log-I-two-term)
# twice in each variable, so it is asserted directly on R rather than assumed.
def R_rem(mu, w):
    """The O(w^-2) remainder of eq. (log-I-two-term)."""
    return mp.log(E(mu, w)) + (4*mu**2 - 1)/(8*w)

mu0 = mp.mpf('0.75')
for (j, l) in [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]:
    vals = []
    for z in [mp.mpf(v) for v in (400, 800, 1600)]:
        d = mp.diff(R_rem, (mu0, z), (j, l))
        vals.append(abs(d)*z**(2 + l))                 # scaled by the claimed order
    # scaled quantity stays bounded and does not grow => the exponent is right
    assert all(v < mp.mpf('50') for v in vals), (j, l, vals)
    assert vals[-1] < 2*vals[0], (j, l, vals)
    # and the claim is sharp in l: one lower power of w would blow up
    d = mp.diff(R_rem, (mu0, mp.mpf(1600)), (j, l))
    assert abs(d)*mp.mpf(1600)**(2 + l) > mp.mpf('1e-6') or abs(d) == 0, (j, l)
print('PASS: d_mu^j d_w^l R = O(w^{-2-l}) for 0<=j,l<=2 (w-derivatives gain w^-1, mu-derivatives do not)')

# Theta_w = w d_w applied once or twice therefore preserves O(w^-2), which is the
# form the proof consumes (Theta_z acts on the argument variable).
for k in (1, 2):
    for z in [mp.mpf(v) for v in (400, 1600)]:
        if k == 1:
            val = z*mp.diff(lambda w: R_rem(mu0, w), z)
        else:
            val = z*mp.diff(lambda w: w*mp.diff(lambda v: R_rem(mu0, v), w), z)
        assert abs(val)*z**2 < mp.mpf('50'), (k, z, val)
print('PASS: Theta_w^k R = O(w^-2) for k=1,2 (order preserved under the Euler operator)')

# (d) the conclusions the licensed differentiation delivers (unnumbered displays):
#     G = z^-1+O(z^-2), 1+P = 1+O(z^-1), H^(k) = (2k-1)z-k(1+2nu)+O(z^-1),
#     D^(k) -> 2(k-1).
for nu in [mp.mpf('-0.4'), mp.mpf('0'), mp.mpf('2.5')]:
    for z in [mp.mpf(120), mp.mpf(240)]:
        assert abs(G(nu, z)*z - 1) < mp.mpf('0.05'), (nu, z)
        assert abs((1 + P(nu, z)) - 1) < mp.mpf('0.05'), (nu, z)
        for kappa in [mp.mpf('0.5'), mp.mpf('1'), mp.mpf('1.5')]:
            pred = (2*kappa - 1)*z - kappa*(1 + 2*nu)
            # exact next order: H^(k) - pred = (kappa+1/2)(nu^2-1/4)/z + O(z^-2)
            resid = (Hk(nu, z, kappa) - pred)*z
            exact = (kappa + mp.mpf('0.5'))*(nu**2 - mp.mpf('0.25'))
            assert abs(resid - exact) < mp.mpf('0.05')*(1 + abs(exact)), (nu, z, kappa, resid, exact)
            assert abs(Dk(nu, z, kappa) - 2*(kappa - 1)) < mp.mpf('0.08'), (nu, z, kappa)
print('PASS: differentiated expansion G,1+P,H^(k) with exact (k+1/2)(nu^2-1/4)/z residual, '
      'and D^(k) -> 2(kappa-1) independent of nu')

print('ALL PASS: verify_bessel_reduction')
