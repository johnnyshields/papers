#!/usr/bin/env python3
r"""Paper section `sec:phase` (Canonical--microcanonical phase geometry), sec:phase.

Exact symbolic certificates (sympy):
  * the refined large-argument expansion of lem:large-argument-limit, derived from the two-term
    Hankel expansion rather than quoted: log E_mu, then G_nu, P_nu, H_nu^(kappa),
    and finally eq. (D-large-z-refined)
        D_nu^(kappa,tau)(z) = 2(kappa-1) + [4 tau/g - 2(kappa+1)nu - 1/2]/z + O(z^-2),
    whose endpoint z^-1 coefficient is c(a) = 4/g - 4a + 7/2, eq. (c-critical);
  * tau_cw of eq. (tau-cw) as the exact solution of the degree-one equation, and
    the equivalent form tau_cw = tau_* - (kappa-1) q_1/p_1;
  * 1 - tau_cw = [a g - 1 + (kappa-1)a^2 g^2/2]/(2a^2 g - 1) > 0, so tau_cw < 1;
  * every step of the lem:boundary-positivity proof: dL_m/dm = (2a-1)/(2(2a+2m-3)^2),
    eq. (Lm-derivative); the m -> infinity limit of L_m and the value L_2, each
    with the trigamma substitution that bounds it (exactly -2a, -a, and
    -(a^2+1)/(3a) respectively); eq. (Fm-boundary); the small-a sufficient
    inequality with its m=2 value 2(2a^3-a^2+1); det N_1-hat of
    eq. (det-N1-boundary) with 2a^2 t - 2a + 1 > 1/(a+1)^2; s_*+c_2 > 0; the
    m=2 reduction of beta_m(2a^2 g-1) > a^2 alpha_m; and the boundary degree-two
    coefficient of eq. (boundary-delta2) with its polynomial P_2.

High-precision numerics (mpmath), from the series definition of Z:
  * the degree-one closed forms d_1, p_1, q_1 behind tau_cw;
  * eq. (qn-pn-ratio) q_n/p_n > g n/4, eq. (q1-p1) q_1/p_1 = a^2 g^2/(2(2a^2 g-1)) < g/2,
    and the gap eq. (q-ratio-gap);
  * lem:boundary-positivity itself: at (1, tau_*) the degree-one coefficient vanishes and every
    degree n >= 2 is strictly positive;
  * thm:two-parameter-coeff on both sides of its boundary, and for kappa > 1;
  * prop:bessel-sharpness: the limits 4(tau-1) at z -> 0 and 2(kappa-1) at z -> infinity,
    and the one-zero strip tau_cw <= tau < 1, where the constant coefficient is
    negative, every positive-degree coefficient is nonnegative, and the determinant
    has exactly one positive zero.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

mp.mp.dps = 50

# ===========================================================================
# Exact symbolic certificates
# ===========================================================================
a, g, t, m, w, mu, kap, tau = sp.symbols('a g t m w mu kappa tau', positive=True)
half = sp.Rational(1, 2)

# --- lem:large-argument-limit: the refined large-argument expansion ------------------------
u = 4*mu**2 - 1
E = 1 - u/(8*w) + u*(u - 8)/(128*w**2)              # DLMF 10.40.1, two terms
assert sp.simplify(sp.series(sp.log(E), w, sp.oo, 3).removeO()
                   - (-u/(8*w) - u/(16*w**2))) == 0
logI = w - sp.log(2*sp.pi*w)/2 - u/(8*w) - u/(16*w**2)
G_nu = sp.expand(-sp.diff(logI, mu, 2))
Theta = sp.expand(w*sp.diff(logI, w))
P_nu = sp.expand(sp.diff(Theta, mu))
Theta2 = sp.expand(w*sp.diff(Theta, w))
assert sp.simplify(G_nu - (1/w + 1/(2*w**2))) == 0
assert sp.simplify(P_nu - (mu/w + mu/w**2)) == 0
H_kappa = sp.expand(2*kap*(Theta - mu) - Theta2)
assert sp.simplify(sp.series(
    H_kappa - ((2*kap-1)*w - kap*(1+2*mu) + (2*kap+1)*(4*mu**2-1)/(8*w)),
    w, sp.oo, 2).removeO()) == 0
D_expansion = sp.series(sp.expand(G_nu*(H_kappa + 4*tau/g) - (1 + P_nu)**2),
                        w, sp.oo, 2).removeO()
assert sp.simplify(D_expansion
                   - (2*(kap-1) + (4*tau/g - 2*(kap+1)*mu - half)/w)) == 0
print('PASS: D_nu^(kappa,tau)(z) = 2(kappa-1) + [4tau/g - 2(kappa+1)nu - 1/2]/z + O(z^-2),')
print('      eq. (D-large-z-refined), derived from the two-term Hankel expansion')
c_a = 4/g - 4*a + sp.Rational(7, 2)
assert sp.simplify((4*tau/g - 2*(kap+1)*mu - half).subs({kap: 1, tau: 1, mu: a-1})
                   - c_a) == 0
print('PASS: the endpoint z^-1 coefficient is c(a) = 4/g - 4a + 7/2 = 4/g - 4nu - 1/2')
assert sp.simplify(c_a.subs(g, 1/(a - half)) - sp.Rational(3, 2)) == 0
print('PASS: substituting 1/g = a - 1/2 in c(a) gives exactly 3/2, so c(a) > 3/2')
# The upper half of eq. (c-range): eq. (trig-lower) gives g > 1/a, so 1/g < a.
assert sp.simplify(c_a.subs(g, 1/a) - sp.Rational(7, 2)) == 0
print('PASS: substituting 1/g = a in c(a) gives exactly 7/2, so c(a) < 7/2;')
print('      together with the previous line this is eq. (c-range), 3/2 < c(a) < 7/2')

# --- the coefficientwise boundary tau_cw ------------------------------------
Gam = sp.Symbol('Gamma_a', positive=True)
d1 = 2*(a*g - 1)/(a**3*Gam**4)
p1 = 2*(2*a**2*g - 1)/(a**3*Gam**4)
q1 = g**2/(a*Gam**4)
tau_cw = sp.solve(sp.Eq(d1 + (kap-1)*q1 + (tau-1)*p1, 0), tau)[0]
tau_cw_claim = (a*g*(2*a-1) - (kap-1)*a**2*g**2/2)/(2*a**2*g - 1)
assert sp.simplify(tau_cw - tau_cw_claim) == 0
print('PASS: tau_cw of eq. (tau-cw) is the exact solution of the degree-one equation')
tau_star = tau_cw_claim.subs(kap, 1)
assert sp.simplify(tau_cw_claim - (tau_star - (kap-1)*q1/p1)) == 0
assert sp.simplify(q1/p1 - a**2*g**2/(2*(2*a**2*g-1))) == 0
print('PASS: tau_cw = tau_* - (kappa-1) q_1/p_1, with q_1/p_1 = a^2 g^2/(2(2a^2 g-1))')
assert sp.simplify(1 - tau_cw_claim
                   - (a*g - 1 + (kap-1)*a**2*g**2/2)/(2*a**2*g - 1)) == 0
print('PASS: 1 - tau_cw = [a g - 1 + (kappa-1)a^2 g^2/2]/(2a^2 g - 1) > 0, so tau_cw < 1')

# --- lem:boundary-positivity, step by step ------------------------------------------------
# eq. (tau-star-s-star): tau_* = tau_cw(a,1) and s_* = tau_*/g.
s_star = a*(2*a-1)/(2*a**2*g - 1)
assert sp.simplify(s_star - tau_star/g) == 0
assert sp.simplify(tau_star - a*g*(2*a-1)/(2*a**2*g - 1)) == 0
print('PASS: eq. (tau-star-s-star) tau_* = a g(2a-1)/(2a^2 g-1) and s_* = tau_*/g')
c_m = m*(m-1)/(2*(2*a + 2*m - 3))
beta_m = (2*a + m - 2)/(2*(a + m - 1))
# L_m is det N_m-hat of eq. (Nhat-m) after the alpha_m factor is divided out, so
# L_m > 0 is eq. (Nhat-m-pd), N_m-hat > 0 for m >= 2.
L_m = s_star + c_m - (a + m/2 - 1)**2/(a + m - sp.Rational(3, 2))
assert sp.simplify(sp.diff(L_m, m) - (2*a-1)/(2*(2*a+2*m-3)**2)) == 0
print('PASS: dL_m/dm = (2a-1)/(2(2a+2m-3)^2), eq. (Lm-derivative): one sign for all m')

g_lower = 1/a + 1/(2*a**2)                      # eq. (trig-lower)
g_cubic = 1/a + 1/(2*a**2) + 1/(6*a**3)         # eq. (trig-upper-cubic)
lim_numer = 8*a**3*g - 6*a**2*g - 8*a**2 + 3
assert sp.simplify(sp.limit(L_m, m, sp.oo) + lim_numer/(4*(2*a**2*g - 1))) == 0
assert sp.simplify(lim_numer.subs(g, g_lower) + 2*a) == 0
print('PASS: lim L_m = -(8a^3 g-6a^2 g-8a^2+3)/(4(2a^2 g-1)); the numerator at the')
print('      trigamma lower bound is exactly -2a, so the limit is positive for a < 1/2')
print('      (with L_2 below, this is eq. (Nhat-m-pd): N_m-hat > 0 for m >= 2)')
L2_numer = 4*a**4*g - 4*a**3 - 2*a**2*g - 2*a**2 + a + 1
assert sp.simplify(L_m.subs(m, 2) + L2_numer/((2*a+1)*(2*a**2*g - 1))) == 0
assert sp.factor(sp.expand(4*a**4 - 2*a**2)) == 2*a**2*(2*a**2 - 1)
assert sp.simplify(L2_numer.subs(g, g_lower) + a) == 0
assert sp.simplify(L2_numer.subs(g, g_cubic) + (a**2+1)/(3*a)) == 0
print('PASS: L_2 = -(4a^4 g-4a^3-2a^2 g-2a^2+a+1)/((2a+1)(2a^2 g-1)); the coefficient of')
print('      g is 2a^2(2a^2-1), and the numerator is exactly -a at the trigamma lower')
print('      bound and exactly -(a^2+1)/(3a) at the cubic upper bound, so L_2 > 0')

Sigma, alpha1 = sp.symbols('Sigma alpha1', positive=True)
beta_1 = (2*a - 1)/(2*a)
F_m = g*(s_star + c_m) + s_star*(alpha1 - Sigma) - 2*beta_m
assert sp.simplify((g*s_star + s_star*alpha1 - 2*beta_1).subs(alpha1, g - 1/a**2)) == 0
print('PASS: MD(N_0-hat, N_1-hat) = 0 at s_*, the equation that defines the boundary')
assert sp.simplify((F_m - (g*c_m - s_star*Sigma + (a-1)*(m-1)/(a*(a+m-1))))
                   .subs(alpha1, g - 1/a**2)) == 0
print('PASS: F_m = g c_m - s_* sum_{r<m} (a+r)^-2 + (a-1)(m-1)/(a(a+m-1)), eq. (Fm-boundary),')
print('      whose positivity for m >= 2 is eq. (N0Nm-positive-boundary)')

small_a = m*(a + m - 1) - 2*a*(1 - a)*(2*a + 2*m - 3)
assert sp.simplify(small_a.subs(m, 2) - 2*(2*a**3 - a**2 + 1)) == 0
assert sp.simplify(sp.diff(small_a, m).subs(m, 2) - (4*a**2 - 3*a + 3)) == 0
print('PASS: the small-a sufficient inequality m(a+m-1) > 2a(1-a)(2a+2m-3) has value')
print('      2(2a^3-a^2+1) > 0 at m=2 and m-derivative 4a^2-3a+3 > 0')

N1_hat = sp.Matrix([[t, beta_1], [beta_1, s_star.subs(g, t + 1/a**2)]])
assert sp.simplify(N1_hat.det()
                   - (2*a-1)*(2*a**2*t - 2*a + 1)/(4*a**2*(2*a**2*t + 1))) == 0
t_lower = 1/(a+1) + 1/(2*(a+1)**2)              # eq. (trig-lower) at y = a+1
assert sp.simplify((2*a**2*t - 2*a + 1).subs(t, t_lower) - 1/(a+1)**2) == 0
print('PASS: det N_1-hat = (2a-1)(2a^2 t-2a+1)/(4a^2(2a^2 t+1)), eq. (det-N1-boundary),')
print('      and 2a^2 t - 2a + 1 is exactly 1/(a+1)^2 at the trigamma lower bound')

assert sp.simplify(s_star + c_m.subs(m, 2)
                   - (4*a**3 + 2*a**2*g - a - 1)/((2*a+1)*(2*a**2*g - 1))) == 0
alpha2 = t - 1/(a+1)**2
gap2 = (beta_m.subs(m, 2)*(2*a**2*g - 1) - a**2*alpha2).subs(g, t + 1/a**2)
assert sp.simplify(gap2 - (a*(2*a+1) - a**2*(1 - a**2)*t)/(a+1)**2) == 0
t_upper = 2/(2*a + 1)                           # eq. (trig-upper-half) at y = a+1
assert sp.simplify(gap2.subs(t, t_upper)
                   - a*(2*a**3 + 4*a**2 + 2*a + 1)/((2*a+1)*(a+1)**2)) == 0
print('PASS: s_*+c_2 > 0, and beta_2(2a^2 g-1) - a^2 alpha_2 is')
print('      a(2a^3+4a^2+2a+1)/((2a+1)(a+1)^2) > 0 at the trigamma upper bound, which is')
print('      the m >= 2 half of eq. (N1Nm-positive-boundary)')

gg = t + 1/a**2
def S_sym(k):
    return sp.rf(2*a + k - 1, k)/(sp.factorial(k)*sp.gamma(a + k)**2)
def M_sym(k, tv):
    alpha = {0: gg, 1: t, 2: t - 1/(a+1)**2}[k]
    beta = sp.Integer(1) if k == 0 else (2*a + k - 2)/(2*(a + k - 1))
    cc = {0: sp.Integer(0), 1: sp.Integer(0), 2: 1/(2*a + 1)}[k]
    return sp.Matrix([[alpha, sp.sqrt(gg)*beta], [sp.sqrt(gg)*beta, tv + gg*cc]])
def MD_sym(X, Y):
    return X[0, 0]*Y[1, 1] + X[1, 1]*Y[0, 0] - 2*X[0, 1]*Y[0, 1]
tau_star_t = (gg*s_star).subs(g, gg)
D2_hat = (S_sym(0)*S_sym(2)*MD_sym(M_sym(0, tau_star_t), M_sym(2, tau_star_t))
          + S_sym(1)**2*M_sym(1, tau_star_t).det())
P2 = ((2*a**5 + 4*a**4 + 2*a**3)*t**2
      + (8*a**5 + 12*a**4 + 5*a**3 + 2*a**2 + a)*t
      - 8*a**4 - 6*a**3 + a**2 + 4*a + 2)
claim = (a**2*t + 1)*P2/(sp.gamma(a)**4*a**5*(a+1)**3*(2*a**2*t + 1))
assert sp.simplify(sp.factor(sp.simplify(D2_hat - claim))) == 0
assert sp.factor(2*a**5 + 4*a**4 + 2*a**3) == 2*a**3*(a+1)**2
assert sp.simplify(P2.subs(t, t_lower)
                   - (8*a**5 + 20*a**4 + 28*a**3 + 30*a**2 + 19*a + 4)/(2*(a+1)**2)) == 0
print('PASS: the boundary degree-two coefficient is eq. (boundary-delta2); P_2 is')
print('      increasing in t and exceeds (8a^5+20a^4+28a^3+30a^2+19a+4)/(2(a+1)^2) > 0')

# ===========================================================================
# High-precision numerics from the series definition
# ===========================================================================
def cauchy(u_, v_, N):
    return [sum(u_[i]*v_[n-i] for i in range(n+1)) for n in range(N+1)]


def pieces(a0, N):
    z, za, zaa, zt, ztt, zat = ([mp.mpf(0)]*(N+1) for _ in range(6))
    for k in range(N+1):
        base = 1/(mp.factorial(k)*mp.gamma(a0 + k))
        psi, psi1 = mp.psi(0, a0 + k), mp.psi(1, a0 + k)
        z[k], za[k], zaa[k] = base, -psi*base, (psi**2 - psi1)*base
        zt[k], ztt[k], zat[k] = k*base, k*k*base, -k*psi*base
    A = [p - q for p, q in zip(cauchy(za, za, N), cauchy(z, zaa, N))]
    B = [p + q - s for p, q, s in
         zip(cauchy(z, z, N), cauchy(z, zat, N), cauchy(za, zt, N))]
    return A, B, cauchy(z, z, N), cauchy(z, zt, N), cauchy(z, ztt, N), cauchy(zt, zt, N)


def delta_num(a0, N, kappa=1, tauv=1):
    g0 = mp.psi(1, a0)
    A, B, Z2, ZZt, ZZtt, Zt2 = pieces(a0, N)
    C = [tauv*Z2[n] + g0*(kappa*ZZt[n] - ZZtt[n] + Zt2[n]) for n in range(N+1)]
    AC, B2 = cauchy(A, C, N), cauchy(B, B, N)
    return [AC[n] - g0*B2[n] for n in range(N+1)]


def PQ_num(a0, N):
    g0 = mp.psi(1, a0)
    A, _, Z2, ZZt, _, _ = pieces(a0, N)
    return cauchy(A, Z2, N), [g0*c for c in cauchy(A, ZZt, N)]


def tau_cw_num(a0, kappa):
    g0 = mp.psi(1, a0)
    return (a0*g0*(2*a0-1) - (kappa-1)*a0**2*g0**2/2)/(2*a0**2*g0 - 1)


def D_bessel(nu, z, kappa=1, tauv=1):
    g0 = mp.psi(1, nu + 1)
    logI = lambda n_, z_: mp.log(mp.besseli(n_, z_))
    theta = lambda n_, z_: z_*mp.diff(lambda s_: logI(n_, s_), z_)
    G = -mp.diff(lambda n_: logI(n_, z), nu, 2)
    P = mp.diff(lambda n_: theta(n_, z), nu)
    H = 2*kappa*(theta(nu, z) - nu) - z*mp.diff(lambda s_: theta(nu, s_), z)
    return G*(H + 4*tauv/g0) - (1 + P)**2


LADDER = ['0.02', '0.1', '0.3', '0.36907', '0.4999', '0.5', '0.5001',
          '0.8', '1', '1.4142', '2', '5', '20', '100']
N, TOL = 14, mp.mpf(10)**-35
for text in LADDER:
    a0 = mp.mpf(text)
    g0, Gam4 = mp.psi(1, a0), mp.gamma(a0)**4
    d, (p, q) = delta_num(a0, N), PQ_num(a0, N)
    assert abs(d[1] - 2*(a0*g0 - 1)/(a0**3*Gam4)) <= TOL*abs(d[1])
    assert abs(p[1] - 2*(2*a0**2*g0 - 1)/(a0**3*Gam4)) <= TOL*abs(p[1])
    assert abs(q[1] - g0**2/(a0*Gam4)) <= TOL*abs(q[1])
    assert all(q[n]/p[n] > g0*n/4 for n in range(1, N+1))
    assert q[1]/p[1] < g0/2
    assert abs(q[1]/p[1] - a0**2*g0**2/(2*(2*a0**2*g0-1))) <= TOL*(q[1]/p[1])
    assert all(q[n]/p[n] > q[1]/p[1] for n in range(2, N+1))
    for kappa in [mp.mpf(1), mp.mpf('1.5'), mp.mpf(4), mp.mpf(40)]:
        tv = tau_cw_num(a0, kappa)
        boundary = delta_num(a0, N, kappa, tv)
        assert abs(boundary[1]) <= TOL*max(abs(d[1]), abs(p[1]))
        assert all(boundary[n] > 0 for n in range(2, N+1))
        step = mp.mpf('1e-6')*max(abs(tv), mp.mpf(1))
        assert delta_num(a0, N, kappa, tv - step)[1] < 0
        assert all(c > 0 for c in delta_num(a0, N, kappa, tv + step)[1:])
    assert tau_cw_num(a0, 1) < 1 and tau_cw_num(a0, 7) < tau_cw_num(a0, 1)
print('PASS: degree-one closed forms d_1, p_1, q_1; eqs. (qn-pn-ratio), (q1-p1),')
print('      (q-ratio-gap); lem:boundary-positivity and thm:two-parameter-coeff on both')
print('      sides of tau_cw -- the three boundaries fig:phase-diagram draws --')
print('      on a 14-point a-ladder straddling 1/2, a_* and 1/sqrt(2)')

for text in ['0.3', '1', '4']:
    a0 = mp.mpf(text)
    nu, g0 = a0 - 1, mp.psi(1, a0)
    c_num = 4/g0 - 4*a0 + mp.mpf(7)/2
    # eq. (c-range), and the two trigamma bounds it is read off:
    # eq. (trig-lower) g > 1/a + 1/(2a^2) > 1/a, and eq. (inverse-trig) 1/g > a - 1/2.
    assert g0 > 1/a0 + 1/(2*a0**2) > 1/a0
    assert 1/g0 > a0 - mp.mpf(1)/2
    assert mp.mpf(3)/2 < c_num < mp.mpf(7)/2
    for tv in [mp.mpf('0.25'), mp.mpf(1), mp.mpf('2.5')]:
        assert abs(D_bessel(nu, mp.mpf('0.002'), mp.mpf('1.3'), tv) - 4*(tv-1)) < mp.mpf('1e-3')
    for z in [mp.mpf(200), mp.mpf(2000)]:
        assert abs(z*D_bessel(nu, z) - c_num) < 40/z          # eq. (D-endpoint-tail)
    for kappa in [mp.mpf('0.4'), mp.mpf(1), mp.mpf('2.2')]:
        assert abs(D_bessel(nu, mp.mpf(4000), kappa) - 2*(kappa-1)) < mp.mpf('0.02')
print('PASS: D^(kappa,tau) -> 4(tau-1) as z -> 0 and -> 2(kappa-1) as z -> infinity,')
print('      the two limits that force the sharp quadrant of prop:bessel-sharpness;')
print('      z D_nu(z) -> c(a), with 3/2 < c(a) < 7/2, eq. (c-range)')

NZ = 160
for text in ['0.3', '1', '3']:
    a0 = mp.mpf(text)
    for kappa in [mp.mpf(1), mp.mpf('2.5')]:
        tcw = tau_cw_num(a0, kappa)
        for frac in ['0', '0.5', '0.999']:
            tv = tcw + mp.mpf(frac)*(1 - tcw)
            d = delta_num(a0, NZ, kappa, tv)
            assert d[0] < 0
            assert all(c >= -TOL*abs(d[2]) for c in d[1:])
            assert all(c > 0 for c in d[2:])
            f = lambda L: sum(d[n]*L**n for n in range(NZ+1))
            hi = mp.mpf(1)
            while f(hi) < 0:
                hi *= 2
            root = mp.findroot(f, (mp.mpf('1e-9'), hi), solver='bisect')
            assert f(root/2) < 0 < f(root*2)
print('PASS: on the strip tau_cw <= tau < 1 the constant coefficient is negative, every')
print('      positive-degree coefficient is nonnegative, and there is exactly one')
print('      positive zero (prop:bessel-sharpness, one-zero regime)')

print('ALL PASS')
