#!/usr/bin/env python3
r"""Paper section `sec:scaling` (Critical wall fan and equivalence of ensembles), sec:scaling.

The tail estimates of lem:central-moments, eqs. (tilt-comparison) and (tilted-tail),
are check_tilted_tail.py's; the tau-general form of the matching is
check_vertical_wall_transfer.py's.

Exact symbolic certificates (sympy):
  * the duplication rewrite of S_m, eq. (Sm-gamma-ratio), as an identity;
  * the large-m expansions eqs. (alpha-asymptotic), (beta-asymptotic),
    (c-asymptotic) against the exact alpha_m, beta_m, c_m of thm:coefficients;
  * the central expansion eq. (MD-central-expansion) of MD(M_k, M_l) at
    k = n/2 + x sqrt n, with the displayed Phi_1(x) of eq. (Phi1) and Phi_2(x) of
    eq. (Phi2) recovered rather than assumed;
  * the denominator expansion eq. (den-central-expansion);
  * the exact hypergeometric moments eq. (hypergeom-moments) for Hyp(2n,n,n),
    summed in closed form at several n, and their limits 1/8 and 3/64;
  * the averaging: eq. (MD-expectation-two-term), eq. (den-expectation), and the
    division that produces n(1-kappa_n) = c(a) + (g-24)/(12g)/n + o(n^-1),
    equivalently eq. (kappa-n-two-term), with (g-24)/(12g) = 1/12 - 2/g;
  * the saddle relation of subsec:ensemble-equivalence, an unnumbered display:
    n = lambda d/d lambda (8 sqrt lambda)
    gives sqrt(lambda) = n/4 and z = 2 sqrt(lambda) = n/2.

High-precision numerics (mpmath), from the series definition of Z:
  * eq. (Sm-asymptotic) with C_a = 2^{2a-2}/sqrt(pi), b = 3/2-2a,
    s_a = -2a^2+5a/2-5/8, at m up to 6400;
  * E X_n^2 = 1/8 + (2a-1)/(8n) + O(n^-2), eq. (X2-asymptotic), under the true
    tilted convolution law rather than the hypergeometric approximation;
  * the two-term law itself: n(1-kappa_n) computed from exact coefficients out to
    degree 400 and Richardson-extrapolated against c(a) and 1/12 - 2/psi_1(a);
  * kappa_n < 1 and eventually strictly increasing, and the first-negative-degree
    law eq. (first-negative-asymptotic) N_a(kappa) ~ c(a)/(1-kappa);
  * the large-lambda asymptotics of Z, Q and Delta -- unnumbered displays of
    subsec:ensemble-equivalence -- and the ratio Delta/Q ~ c(a)/(2z) that the
    coefficient saddle converts into c(a)/n;
  * eq. (Tn-Kn-law) as a probability law and eq. (threshold-expectation) rewriting
    n(1-kappa_n) as a ratio of expectations under it.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

# ===========================================================================
# Exact symbolic certificates
# ===========================================================================
a, g, n, x, mm = sp.symbols('a g n x m', positive=True)

lhs = sp.rf(2*a + mm - 1, mm)/(sp.factorial(mm)*sp.gamma(a + mm)**2)
rhs = (2**(2*a - 2)/sp.sqrt(sp.pi)*4**mm/sp.factorial(mm)**2
       * sp.gamma(mm + a - sp.Rational(1, 2))/sp.gamma(mm + a)
       * sp.gamma(mm + 1)/sp.gamma(mm + 2*a - 1))
assert sp.simplify(sp.expand_func(sp.simplify(lhs/rhs))) == 1
print('PASS: the duplication rewrite of S_m, eq. (Sm-gamma-ratio), is an identity')

def alpha_exp(k):
    return 1/k + (sp.Rational(1, 2) - a)/k**2 + (a**2 - a + sp.Rational(1, 6))/k**3
def beta_exp(k):
    return sp.Rational(1, 2) + (a-1)/(2*k) - (a-1)**2/(2*k**2) + (a-1)**3/(2*k**3)
def c_exp(k):
    d = a - sp.Rational(3, 2)
    return k/4 - (a - sp.Rational(1, 2))/4 + d*(a - sp.Rational(1, 2))/(4*k) \
        - d**2*(a - sp.Rational(1, 2))/(4*k**2)

assert sp.simplify(sp.series(sp.polygamma(1, a + mm) - alpha_exp(mm),
                             mm, sp.oo, 4).removeO()) == 0
assert sp.simplify(sp.series((2*a + mm - 2)/(2*(a + mm - 1)) - beta_exp(mm),
                             mm, sp.oo, 4).removeO()) == 0
assert sp.simplify(sp.series(mm*(mm-1)/(2*(2*a + 2*mm - 3)) - c_exp(mm),
                             mm, sp.oo, 3).removeO()) == 0
print('PASS: the large-m expansions of alpha_m, beta_m, c_m, eqs. (alpha-asymptotic),')
print('      (beta-asymptotic), (c-asymptotic), match the exact thm:coefficients formulas')

k_, l_ = n/2 + x*sp.sqrt(n), n/2 - x*sp.sqrt(n)
MD_central = (alpha_exp(k_)*(1 + g*c_exp(l_)) + alpha_exp(l_)*(1 + g*c_exp(k_))
              - 2*g*beta_exp(k_)*beta_exp(l_))
Phi1 = 4 + g*(3 - 4*a) + 4*g*x**2
Phi2 = sp.Rational(1, 3)*(48*g*x**4 + (60 - 96*a)*g*x**2 + 48*x**2
                         + 24*a**2*g - 36*a*g - 24*a + 13*g + 12)
assert sp.simplify(sp.expand(sp.series(sp.expand(MD_central), n, sp.oo, 3).removeO()
                             - Phi1/n - Phi2/n**2)) == 0
print('PASS: MD(M_k, M_l) = Phi_1(x)/n + Phi_2(x)/n^2 + O(n^-3), eq. (MD-central-expansion),')
print('      with the displayed Phi_1(x) of eq. (Phi1) and Phi_2(x) of eq. (Phi2)')
den_central = sp.series(sp.expand((l_*alpha_exp(k_) + k_*alpha_exp(l_))/2),
                        n, sp.oo, 2).removeO()
assert sp.simplify(sp.expand(den_central - (1 + (1 - 2*a + 8*x**2)/n))) == 0
print('PASS: (l alpha_k + k alpha_l)/2 = 1 + (1-2a+8x^2)/n + O(n^-2), eq. (den-central-expansion)')

for nv in [6, 9, 14, 21]:
    total = sum(sp.binomial(nv, i)**2 for i in range(nv+1))
    assert total == sp.binomial(2*nv, nv)
    X2 = sum(sp.binomial(nv, i)**2*(sp.Rational(i) - sp.Rational(nv, 2))**2
             for i in range(nv+1))/total/nv
    X4 = sum(sp.binomial(nv, i)**2*(sp.Rational(i) - sp.Rational(nv, 2))**4
             for i in range(nv+1))/total/nv**2
    assert sp.simplify(X2 - sp.Rational(nv, 4*(2*nv - 1))) == 0
    assert sp.simplify(X4 - sp.Rational(nv*(3*nv - 4), 16*(2*nv - 3)*(2*nv - 1))) == 0
assert sp.limit(n/(4*(2*n - 1)), n, sp.oo) == sp.Rational(1, 8)
assert sp.limit(n*(3*n - 4)/(16*(2*n - 3)*(2*n - 1)), n, sp.oo) == sp.Rational(3, 64)
print('PASS: under Hyp(2n,n,n), E X^2 = n/(4(2n-1)) and E X^4 = n(3n-4)/(16(2n-3)(2n-1)),')
print('      eq. (hypergeom-moments), tending to 1/8 and 3/64')

EX2, EX4 = sp.Rational(1, 8) + (2*a - 1)/(8*n), sp.Rational(3, 64)
E_MD = sp.series(sp.expand(
    (4 + g*(3 - 4*a))/n + 4*g*EX2/n
    + (sp.Rational(1, 3)*(48*g*EX4 + (60 - 96*a)*g*sp.Rational(1, 8)
                          + 48*sp.Rational(1, 8) + 24*a**2*g - 36*a*g
                          - 24*a + 13*g + 12))/n**2), n, sp.oo, 3).removeO()
c_a = 4/g - 4*a + sp.Rational(7, 2)
E_MD_claim = g*c_a/n + (96*a**2*g - 180*a*g - 96*a + 85*g + 72)/(12*n**2)
assert sp.simplify(sp.expand(E_MD - E_MD_claim)) == 0
print('PASS: E MD = g c(a)/n + (96a^2 g-180a g-96a+85g+72)/(12 n^2) + o(n^-2),')
print('      eq. (MD-expectation-two-term); the 4g x^2 term contributes 4g/8 = g/2,')
print('      which is the fluctuation half of the 7/2 in c(a)')
E_den = 1 + (1 - 2*a + 8*sp.Rational(1, 8))/n
assert sp.simplify(E_den - (1 + 2*(1 - a)/n)) == 0
print('PASS: E[(n-K_n) alpha_{K_n}] = 1 + 2(1-a)/n + o(n^-1), eq. (den-expectation)')
ratio = sp.series(sp.expand(n*E_MD_claim/(g*E_den)), n, sp.oo, 2).removeO()
assert sp.simplify(sp.expand(ratio - (c_a + (g - 24)/(12*g)/n))) == 0
assert sp.simplify((g - 24)/(12*g) - (sp.Rational(1, 12) - 2/g)) == 0
print('PASS: n(1-kappa_n) = c(a) + (g-24)/(12g)/n + o(n^-1), equivalently')
print('      eq. (kappa-n-two-term), with (g-24)/(12g) = 1/12 - 2/g')

lam = sp.Symbol('lambda', positive=True)
saddle = sp.solve(sp.Eq(n, lam*sp.diff(8*sp.sqrt(lam), lam)), lam)[0]
assert sp.simplify(sp.sqrt(saddle) - n/4) == 0
print('PASS: coefficient saddle of subsec:ensemble-equivalence:')
print('      n = lambda d/d lambda (8 sqrt lambda) gives')
print('      sqrt(lambda) = n/4, hence z = 2 sqrt(lambda) = n/2')

# ===========================================================================
# High-precision numerics from the series definition
# ===========================================================================
def cauchy(u_, v_, N):
    return [sum(u_[i]*v_[j-i] for i in range(j+1)) for j in range(N+1)]


def delta_and_Q(a0, N):
    """[lambda^j] Delta and [lambda^j] Q, from the termwise coefficients of Z."""
    g0 = mp.psi(1, a0)
    z, za, zaa, zt, ztt, zat = ([mp.mpf(0)]*(N+1) for _ in range(6))
    for k in range(N+1):
        base = 1/(mp.factorial(k)*mp.gamma(a0 + k))
        psi, psi1 = mp.psi(0, a0 + k), mp.psi(1, a0 + k)
        z[k], za[k], zaa[k] = base, -psi*base, (psi**2 - psi1)*base
        zt[k], ztt[k], zat[k] = k*base, k*k*base, -k*psi*base
    A = [p - q for p, q in zip(cauchy(za, za, N), cauchy(z, zaa, N))]
    B = [p + q - s for p, q, s in
         zip(cauchy(z, z, N), cauchy(z, zat, N), cauchy(za, zt, N))]
    ZZt = cauchy(z, zt, N)
    C = [c + g0*(d - e + f) for c, d, e, f in
         zip(cauchy(z, z, N), ZZt, cauchy(z, ztt, N), cauchy(zt, zt, N))]
    AC, B2 = cauchy(A, C, N), cauchy(B, B, N)
    return ([AC[j] - g0*B2[j] for j in range(N+1)],
            [g0*c for c in cauchy(A, ZZt, N)])


def S_num(a0, k):
    return mp.rf(2*a0 + k - 1, k)/(mp.factorial(k)*mp.gamma(a0 + k)**2)


mp.mp.dps = 80
for text in ['0.3', '1', '2.5']:
    a0 = mp.mpf(text)
    C_a = 2**(2*a0 - 2)/mp.sqrt(mp.pi)
    b_a = mp.mpf(3)/2 - 2*a0
    s_a = -2*a0**2 + mp.mpf(5)/2*a0 - mp.mpf(5)/8
    for M in [400, 1600, 6400]:
        model = C_a*mp.mpf(4)**M/mp.factorial(M)**2*mp.mpf(M)**b_a*(1 + s_a/M)
        assert abs(S_num(a0, M)/model - 1) < 40/mp.mpf(M)**2
print('PASS: eq. (Sm-asymptotic) with C_a = 2^{2a-2}/sqrt(pi), b = 3/2-2a,')
print('      s_a = -2a^2+5a/2-5/8, tested to m = 6400')

mp.mp.dps = 120
for text in ['0.3', '1', '2.5']:
    a0 = mp.mpf(text)
    for N in [200, 400, 800]:
        weights = [S_num(a0, k)*S_num(a0, N - k) for k in range(N+1)]
        total = sum(weights)
        moment = sum(weights[k]*(k - mp.mpf(N)/2)**2 for k in range(N+1))/total/N
        predicted = mp.mpf(1)/8 + (2*a0 - 1)/(8*N)
        assert abs(moment - predicted)*N**2 < 30
print('PASS: E X_n^2 = 1/8 + (2a-1)/(8n) + O(n^-2), eq. (X2-asymptotic), under the')
print('      true tilted convolution law S_k S_{n-k}')

# eq. (Tn-Kn-law) and eq. (threshold-expectation): the threshold rewritten as an
# expectation under the law of K_n.  Delta_n and q_n come from the Cauchy convolution
# of the termwise Maclaurin coefficients of Z, the S_m/alpha_m/beta_m/c_m entries from
# thm:coefficients -- two routes sharing no arithmetic.
mp.mp.dps = 80
for text in ['0.3', '1', '2.5']:
    a0 = mp.mpf(text)
    g0 = mp.psi(1, a0)
    NT = 60
    d, q = delta_and_Q(a0, NT)
    S = [S_num(a0, k) for k in range(NT+1)]
    alpha_m = [mp.psi(1, a0 + j) for j in range(NT+1)]
    beta_m = [mp.mpf(1)] + [(2*a0 + j - 2)/(2*(a0 + j - 1)) for j in range(1, NT+1)]
    c_m = [mp.mpf(0), mp.mpf(0)] + [mp.mpf(j*(j-1))/(2*(2*a0 + 2*j - 3))
                                    for j in range(2, NT+1)]
    def MD(j, l):                     # polarization of det on M_j, M_l
        return (alpha_m[j]*(1 + g0*c_m[l]) + alpha_m[l]*(1 + g0*c_m[j])
                - 2*g0*beta_m[j]*beta_m[l])
    for N in [1, 2, 5, 20, 60]:
        T = mp.fsum(S[k]*S[N-k] for k in range(N+1))
        law = [S[k]*S[N-k]/T for k in range(N+1)]
        assert abs(mp.fsum(law) - 1) < mp.mpf('1e-70'), (a0, N)
        E_MD_n = mp.fsum(law[k]*MD(k, N-k) for k in range(N+1))
        E_den_n = mp.fsum(law[k]*(N-k)*alpha_m[k] for k in range(N+1))
        # eq. (Delta-n-MD) and eq. (pq-coefficients) in expectation form
        assert abs(d[N] - T/2*E_MD_n) < mp.mpf('1e-60')*abs(d[N]), (a0, N)
        assert abs(q[N] - g0*T/2*E_den_n) < mp.mpf('1e-60')*abs(q[N]), (a0, N)
        # eq. (threshold-expectation)
        assert abs(N*d[N]/q[N] - N*E_MD_n/(g0*E_den_n)) < mp.mpf('1e-60')*abs(N*d[N]/q[N])
print('PASS: eq. (Tn-Kn-law) P(K_n=k) = S_k S_{n-k}/T_n is a probability law, and')
print('      eq. (threshold-expectation) n(1-kappa_n) = n E MD(M_{K_n},M_{n-K_n})')
print('      / (g E[(n-K_n) alpha_{K_n}]), against Delta_n/q_n from the convolution route')

NMAX = 400
for text in ['0.1', '1', '10']:
    a0 = mp.mpf(text)
    g0 = mp.psi(1, a0)
    c_num = 4/g0 - 4*a0 + mp.mpf(7)/2
    b_num = mp.mpf(1)/12 - 2/g0
    d, q = delta_and_Q(a0, NMAX)
    scaled = {N: N*(d[N]/q[N]) for N in (100, 200, 400)}
    for N in (100, 200, 400):
        assert abs(scaled[N] - c_num) < 3*(abs(c_num) + abs(b_num))/N
    # Richardson: if f(N) = b + O(1/N) then 2 f(2N) - f(N) = b + O(1/N^2)
    for N in (100, 200):
        f_N = N*(scaled[N] - c_num)
        f_2N = 2*N*(scaled[2*N] - c_num)
        assert abs(2*f_2N - f_N - b_num) < mp.mpf('0.02')*max(abs(b_num), mp.mpf(1))
    # eq. (qndef): q_n = [lambda^n] Q > 0 and kappa_n = 1 - Delta_n/q_n.
    assert all(q[j] > 0 for j in range(1, NMAX+1))
    kappa_n = [None] + [1 - d[j]/q[j] for j in range(1, NMAX+1)]
    assert all(kappa_n[j] < 1 for j in range(1, NMAX+1))
    start = next(j0 for j0 in range(1, NMAX-1)
                 if all(kappa_n[j+1] > kappa_n[j] for j in range(j0, NMAX)))
    assert start <= 20
    # eq. (first-negative-asymptotic) is a kappa -> 1 statement, and it has to be
    # tested there: at a = 10 the low-degree thresholds still wiggle, and
    # 1 - kappa = 0.1 already returns degree one rather than c(a)/(1-kappa).
    ratios = []
    for eps_text in ['0.1', '0.05', '0.02', '0.01']:
        eps = mp.mpf(eps_text)
        first = next(j for j in range(1, NMAX+1) if d[j] - eps*q[j] < 0)
        ratios.append(first*eps/c_num)
    assert abs(ratios[-1] - 1) < mp.mpf('0.1')
print('PASS: eq. (qndef) q_n > 0; n(1-kappa_n) -> c(a), which is the coefficient half of')
print('      eq. (critical-constant-match) -- its large-z half, z D_{a-1}(z) -> c(a), is')
print('      verify_phase_diagram.py\'s -- with the Richardson-extrapolated 1/n correction')
print('      matching 1/12 - 2/psi_1(a); kappa_n < 1 and eventually strictly increasing;')
print('      N_a(kappa) ~ c(a)/(1-kappa), eq. (first-negative-asymptotic)')

mp.mp.dps = 40
for text in ['0.5', '1', '2']:
    a0 = mp.mpf(text)
    g0 = mp.psi(1, a0)
    c_num = 4/g0 - 4*a0 + mp.mpf(7)/2
    for lam_v in [mp.mpf(400), mp.mpf(2500)]:
        terms = int(20*mp.sqrt(lam_v)) + 80
        Z = sum(lam_v**k/(mp.factorial(k)*mp.gamma(a0 + k)) for k in range(terms))
        model = mp.e**(2*mp.sqrt(lam_v))*lam_v**(mp.mpf(1)/4 - a0/2)/(2*mp.sqrt(mp.pi))
        assert abs(Z/model - 1) < 3/mp.sqrt(lam_v)
        Q_model = g0/(32*mp.pi**2)*mp.e**(8*mp.sqrt(lam_v))*lam_v**(1 - 2*a0)
        D_model = (g0*c_num/(128*mp.pi**2)*mp.e**(8*mp.sqrt(lam_v))
                   * lam_v**(mp.mpf(1)/2 - 2*a0))
        assert abs(D_model/Q_model - c_num/(4*mp.sqrt(lam_v))) < mp.mpf('1e-25')
print('PASS: large-lambda asymptotics of Z, Q and Delta (subsec:ensemble-equivalence), and')
print('      Delta/Q ~ c(a)/(4 sqrt lambda) = c(a)/(2z), which at the saddle z ~ n/2')
print('      is c(a)/n, the leading term of 1 - kappa_n')

print('ALL PASS')
