#!/usr/bin/env python3
r"""The coefficient--argument transfer along the whole vertical wall kappa = 1:
thm:wall-fan and eq. (vertical-wall-two-term), in the critical-scaling section
sec:scaling.

The endpoint case tau = 1 is verify_critical_scaling.py's.  What is settled here is
the single question thm:wall-fan raises -- whether the matching of the two limits
survives varying tau -- by checking the remark's own chain rather than its conclusion
alone.  With p_n = [lambda^n] P, q_n = [lambda^n] Q, alpha_k = psi_1(a+k),
T_n = sum_k S_k S_{n-k}, and P(K_n = k) = S_k S_{n-k}/T_n:

  * eq. (pq-coefficients): p_n = sum_k S_k S_{n-k} alpha_k and
    q_n = (g/2) sum_k (n-k) S_k S_{n-k} alpha_k, checked against p_n and q_n built by
    Cauchy convolution of the termwise Maclaurin coefficients of Z, Z_a, Z_aa, Z_Theta
    -- two routes that share no arithmetic;
  * the remark's two intermediate steps, p_n = T_n E alpha_{K_n} with
    E alpha_{K_n} = 2/n + O(n^-2), and q_n = (g T_n/2) E[(n-K_n) alpha_{K_n}] with
    E[(n-K_n) alpha_{K_n}] = 1 + O(n^-1);
  * the ratio p_n/q_n = 4/(g n) + O(n^-2), with the n^2-weighted remainder bounded
    along a ladder rather than fitted at one n;
  * eq. (vertical-wall-two-term): 1 - kappa_{n,tau}(a) = c_tau(a)/n + O(n^-2) with
    c_tau(a) = 4 tau/g - 4a + 7/2, and the exact affine relation
    1 - kappa_{n,tau} = (1 - kappa_n) + (tau-1) p_n/q_n behind it;
  * c_tau(a) = lim_{z -> infinity} z D_{a-1}^{(1,tau)}(z), computed from I_nu itself,
    which is the argument-side half of the matching;
  * c_tau(a) = c(a) at tau = 1, and the multicritical value tau_infinity(a) = g(a-7/8)
    at which c_tau(a) = 0, so both the 1/n and the 1/z leading terms vanish together.

All numerics are mpmath at arbitrary precision.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

# ===========================================================================
# Exact symbolic content of eq. (vertical-wall-two-term)
# ===========================================================================
a_s, g_s, tau_s = sp.symbols('a g tau', positive=True)
c_tau = 4*tau_s/g_s - 4*a_s + sp.Rational(7, 2)
c_end = 4/g_s - 4*a_s + sp.Rational(7, 2)                    # eq. (c-critical)
assert sp.simplify(c_tau.subs(tau_s, 1) - c_end) == 0
tau_infinity = g_s*(a_s - sp.Rational(7, 8))
assert sp.simplify(c_tau.subs(tau_s, tau_infinity)) == 0
# eq. (D-large-z-refined) at kappa = 1 has z^-1 coefficient 4 tau/g - 2(kappa+1) nu - 1/2;
# with nu = a-1 that is exactly c_tau(a).
nu_s = a_s - 1
assert sp.simplify((4*tau_s/g_s - 2*(1 + 1)*nu_s - sp.Rational(1, 2)) - c_tau) == 0
print('PASS: c_tau(a) = 4 tau/g - 4a + 7/2 is c(a) at tau=1, vanishes at tau_infinity = g(a-7/8),')
print('      and is the z^-1 coefficient of eq. (D-large-z-refined) at kappa = 1')

# ===========================================================================
# Coefficients, by two independent routes
# ===========================================================================
mp.mp.dps = 120

def cauchy(u_, v_, N):
    return [sum(u_[i]*v_[j-i] for i in range(j+1)) for j in range(N+1)]

def delta_p_q(a0, N):
    """[lambda^j] of Delta, P = A Z^2 and Q = g A Z Z_Theta, from termwise Z data."""
    g0 = mp.psi(1, a0)
    z, za, zaa, zt, ztt, zat = ([mp.mpf(0)]*(N+1) for _ in range(6))
    for k in range(N+1):
        base = 1/(mp.factorial(k)*mp.gamma(a0 + k))
        ps, ps1 = mp.psi(0, a0 + k), mp.psi(1, a0 + k)
        z[k], za[k], zaa[k] = base, -ps*base, (ps**2 - ps1)*base
        zt[k], ztt[k], zat[k] = k*base, k*k*base, -k*ps*base
    A = [u - v for u, v in zip(cauchy(za, za, N), cauchy(z, zaa, N))]
    B = [u + v - w for u, v, w in
         zip(cauchy(z, z, N), cauchy(z, zat, N), cauchy(za, zt, N))]
    ZZ, ZZt = cauchy(z, z, N), cauchy(z, zt, N)
    C = [u + g0*(v - w + y) for u, v, w, y in
         zip(ZZ, ZZt, cauchy(z, ztt, N), cauchy(zt, zt, N))]
    AC, B2 = cauchy(A, C, N), cauchy(B, B, N)
    return ([AC[j] - g0*B2[j] for j in range(N+1)],
            cauchy(A, ZZ, N),
            [g0*c for c in cauchy(A, ZZt, N)])

def S_num(a0, k):                       # eq. (asymmetric-convolution) weight
    return mp.rf(2*a0 + k - 1, k)/(mp.factorial(k)*mp.gamma(a0 + k)**2)

NMAX = 240
LADDER = ['0.3', '1', '2.5']
TAUS = [mp.mpf('-2'), mp.mpf(0), mp.mpf('0.5'), mp.mpf(1), mp.mpf(3)]

for text in LADDER:
    a0 = mp.mpf(text)
    g0 = mp.psi(1, a0)
    d, p, q = delta_p_q(a0, NMAX)
    Ssum = [S_num(a0, k) for k in range(NMAX+1)]
    alpha = [mp.psi(1, a0 + k) for k in range(NMAX+1)]

    # ---- eq. (pq-coefficients), against the convolution route. ----
    for n in [1, 2, 5, 17, 60, NMAX]:
        p_ser = sum(Ssum[k]*Ssum[n-k]*alpha[k] for k in range(n+1))
        q_ser = g0/2*sum((n-k)*Ssum[k]*Ssum[n-k]*alpha[k] for k in range(n+1))
        assert abs(p[n]/p_ser - 1) < mp.mpf('1e-100'), (a0, n)
        assert abs(q[n]/q_ser - 1) < mp.mpf('1e-100'), (a0, n)

    # ---- the remark's two intermediate steps. ----
    for n in [40, 80, 160, 240]:
        T = sum(Ssum[k]*Ssum[n-k] for k in range(n+1))
        E_alpha = sum(Ssum[k]*Ssum[n-k]*alpha[k] for k in range(n+1))/T
        E_den = sum(Ssum[k]*Ssum[n-k]*(n-k)*alpha[k] for k in range(n+1))/T
        assert abs(p[n] - T*E_alpha) < mp.mpf('1e-100')*abs(p[n]), (a0, n)
        assert abs(q[n] - g0*T/2*E_den) < mp.mpf('1e-100')*abs(q[n]), (a0, n)
        assert abs(E_alpha - 2/mp.mpf(n))*n**2 < 20, (a0, n, E_alpha)
        assert abs(E_den - 1)*n < 20, (a0, n, E_den)
        # ---- p_n/q_n = 4/(g n) + O(n^-2). ----
        assert abs(p[n]/q[n] - 4/(g0*n))*n**2 < 40, (a0, n, p[n]/q[n])

    # ---- eq. (vertical-wall-two-term). ----
    for tau in TAUS:
        c_num = 4*tau/g0 - 4*a0 + mp.mpf(7)/2
        prev = None
        for n in [60, 120, 240]:
            kappa_n_tau = 1 - (d[n] + (tau - 1)*p[n])/q[n]
            # the affine relation the remark is built on, exactly
            assert abs((1 - kappa_n_tau)
                       - ((d[n]/q[n]) + (tau - 1)*p[n]/q[n])) < mp.mpf('1e-100')
            resid = abs(n*(1 - kappa_n_tau) - c_num)
            assert resid*n < 60, (a0, tau, n, resid)
            if prev is not None:
                assert resid < prev, (a0, tau, n)          # the remainder shrinks
            prev = resid
print(f'PASS: eq. (pq-coefficients) p_n = sum S_k S_{{n-k}} alpha_k and')
print(f'      q_n = (g/2) sum (n-k) S_k S_{{n-k}} alpha_k, against the convolution route')
print(f'PASS: p_n = T_n E alpha_{{K_n}} with E alpha_{{K_n}} = 2/n + O(n^-2), and')
print(f'      q_n = (g T_n/2) E[(n-K_n) alpha_{{K_n}}] with E[...] = 1 + O(n^-1)')
print(f'PASS: p_n/q_n = 4/(g n) + O(n^-2) on an n-ladder to {NMAX}')
print(f'PASS: eq. (vertical-wall-two-term) 1 - kappa_{{n,tau}} = c_tau(a)/n + O(n^-2),')
print(f'      c_tau(a) = 4 tau/g - 4a + 7/2, at {len(TAUS)} values of tau on each of '
      f'{len(LADDER)} a-values')

# ===========================================================================
# The argument side: c_tau(a) = lim_{z -> infinity} z D^{(1,tau)}_{a-1}(z)
# ===========================================================================
mp.mp.dps = 40

def logI(nu, z):
    return mp.log(mp.besseli(nu, z))

def D_1tau(nu, z, tau):
    g0 = mp.polygamma(1, nu + 1)
    G = -mp.diff(lambda n_: logI(n_, z), nu, 2)
    P = z*mp.diff(lambda zz: mp.diff(lambda n_: logI(n_, zz), nu), z)
    f1 = mp.diff(lambda zz: logI(nu, zz), z, 1)
    f2 = mp.diff(lambda zz: logI(nu, zz), z, 2)
    H = 2*(z*f1 - nu) - (z*f1 + z**2*f2)           # kappa = 1
    return G*(H + 4*tau/g0) - (1 + P)**2

for text in LADDER:
    a0 = mp.mpf(text)
    nu, g0 = a0 - 1, mp.polygamma(1, a0)
    for tau in TAUS:
        c_num = 4*tau/g0 - 4*a0 + mp.mpf(7)/2
        prev = None
        for z in [mp.mpf(200), mp.mpf(800), mp.mpf(3200)]:
            resid = abs(z*D_1tau(nu, z, tau) - c_num)
            assert resid*z < 200, (a0, tau, z, resid)
            if prev is not None:
                assert resid < prev, (a0, tau, z)
            prev = resid
print('PASS: c_tau(a) = lim_{z->inf} z D^{(1,tau)}_{a-1}(z), from I_nu itself, so the')
print('      coefficient and argument constants agree along the whole wall kappa = 1')

# The multicritical value, on both sides at once.
for text in LADDER:
    a0 = mp.mpf(text)
    nu, g0 = a0 - 1, mp.polygamma(1, a0)
    tau_inf = g0*(a0 - mp.mpf(7)/8)
    assert abs(4*tau_inf/g0 - 4*a0 + mp.mpf(7)/2) < mp.mpf('1e-30'), a0
    for z in [mp.mpf(800), mp.mpf(3200)]:
        assert abs(z*D_1tau(nu, z, tau_inf)) < 200/z, (a0, z)
print('PASS: at tau_infinity(a) = g(a-7/8) both the 1/n and the 1/z leading terms vanish')

print('ALL PASS: check_vertical_wall_transfer')
