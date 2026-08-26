#!/usr/bin/env python3
r"""thm:wall-fan and prop:c-monotone, from exact coefficients rather than from
the expansions the proof assembles.

thm:wall-fan states the full two-term deformation wall for every fixed tau,
of which the endpoint theorem's expansion is the tau = 1 slice.  Both sides of
the coefficient-argument dictionary are checked independently:

  * eq. (vertical-wall-two-term): 1 - kappa_{n,tau} = c_tau/n + d_tau/n^2 + O(n^-3)
    with c_tau = 4 tau/g - 4a + 7/2 and d_tau = 1/12 - 2 tau/g, from Delta_n, p_n
    and q_n built by Cauchy convolution of the exact fibers;
  * eq. (pq-ratio-two-term): p_n/q_n = 4/(g n) - 2/(g n^2) + O(n^-3), the ratio
    that makes the second term available;
  * eq. (D-wall-two-term): D_{a-1}^{(1,tau)}(z) = c_tau/z + e_tau/z^2 + O(z^-3)
    with e_tau = 2 tau/g - 3(a-1) - 1/3, from log I_nu directly;
  * eq. (tau-n-limit): the individual coefficient walls tau_n(a,1) = 1 - Delta_n/p_n
    converge to tau_infty(a) = g(a - 7/8), the accumulation point of the fan;
  * eq. (c-d-tau) as a signed distance: c_tau = (4/g)(tau - tau_infty), so
    c_{tau_infty} = 0 and the leading jet vanishes there;
  * eq. (second-order-match): at tau = tau_infty both sides drop one order to
    2(11/12 - a)/n^2 and (11/12 - a)/z^2, matching under n ~ 2z;
  * eq. (wall-ordering): tau_infty(a) < tau_cw(a,1) < 1;
  * eq. (wall-slope-covariance): q_n/p_n = gn/4 - (g/2)Cov(K_n, alpha_{K_n})/E alpha_{K_n}
    as an exact identity, with the covariance strictly negative because alpha is
    decreasing -- so the strict wall-slope ordering q_n/p_n > gn/4 that keeps degree
    one exposed is a negative-covariance effect rather than a pairing accident;
  * cor:wall-orientation, all four displays: eq. (wall-orientation) the 1/n law whose
    sign flips at a = 11/12, eq. (wall-transverse) the O(n) transverse slope and the
    resulting trichotomy, and eq. (wall-tangent-cone) the blow-up limit whose
    solution for x is c_tau.

prop:c-monotone upgrades the endpoint bound 3/2 < c(a) < 7/2 to an exact range:
c'(a) = -4(g^2+g')/g^2 < 0 with limits 7/2 and 3/2.  The engine of that proof is
checked too -- t/(1-e^-t) > 1 + t/2 and (k*k)(s) > s^2/(1-e^-s), which is what
makes psi_1^2 + psi_2 > 0.
"""
from mpmath import mp, mpf, psi, quad, exp
from _wallfan_common import (build_S, wall_data, richardson, D_bessel,
                             c_tau, d_tau, e_tau, tau_infty)

mp.dps = 50
NS = [150, 300, 600, 1200]
N = max(NS)

for a in (mpf(1)/2, mpf(1), mpf(5)/2):
    S = build_S(a, N)
    dat = wall_data(a, S, NS)
    g = psi(1, a)
    for tau in (mpf(0), mpf(1), mpf(3)/2):
        f = [(dat[n][0] + (tau-1)*dat[n][1])/dat[n][2] for n in NS]
        c_hat = richardson(NS, [n*v for n, v in zip(NS, f)])
        d_hat = richardson(NS, [n*(n*v - c_tau(a, tau)) for n, v in zip(NS, f)])
        assert abs(c_hat - c_tau(a, tau)) < mpf('1e-4'), (a, tau, c_hat)
        assert abs(d_hat - d_tau(a, tau)) < mpf('1e-3'), (a, tau, d_hat)
        assert abs(c_tau(a, tau) - 4*(tau - tau_infty(a))/g) < mpf('1e-40')
    r = [dat[n][1]/dat[n][2] for n in NS]
    assert abs(richardson(NS, [n*v for n, v in zip(NS, r)]) - 4/g) < mpf('1e-5')
    assert abs(richardson(NS, [n*(n*v-4/g) for n, v in zip(NS, r)]) + 2/g) < mpf('1e-3')
print('PASS: eq. (vertical-wall-two-term) at nine (a, tau) pairs, with c_tau recovered')
print('      as the signed distance (4/g)(tau - tau_infty), and eq. (pq-ratio-two-term).')

for a in (mpf(1)/2, mpf(1), mpf(2)):
    S = build_S(a, N)
    dat = wall_data(a, S, NS)
    assert abs(richardson(NS, [1 - dat[n][0]/dat[n][1] for n in NS]) - tau_infty(a)) < mpf('1e-4')
    ti = tau_infty(a)
    f = [(dat[n][0] + (ti-1)*dat[n][1])/dat[n][2] for n in NS]
    assert abs(richardson(NS, [n*v for n, v in zip(NS, f)])) < mpf('1e-4')
    sec = richardson(NS, [n*n*v for n, v in zip(NS, f)])
    assert abs(sec - 2*(mpf(11)/12 - a)) < mpf('1e-3'), (a, sec)
print('PASS: eq. (tau-n-limit) tau_n(a,1) -> tau_infty(a), and the coefficient half of')
print('      eq. (second-order-match): the leading jet vanishes and 2(11/12-a)/n^2 remains.')

ZS = [mpf(40), mpf(80), mpf(160), mpf(320)]
for a in (mpf(1), mpf(2)):
    for tau in (mpf(1), mpf(3)/2):
        vals = [D_bessel(a-1, z, 1, tau) for z in ZS]
        assert abs(richardson(ZS, [z*v for z, v in zip(ZS, vals)]) - c_tau(a, tau)) < mpf('1e-3')
        e_hat = richardson(ZS, [z*(z*v - c_tau(a, tau)) for z, v in zip(ZS, vals)])
        assert abs(e_hat - e_tau(a, tau)) < mpf('1e-2'), (a, tau, e_hat)
    ti = tau_infty(a)
    vals = [D_bessel(a-1, z, 1, ti) for z in ZS]
    assert abs(richardson(ZS, [z*v for z, v in zip(ZS, vals)])) < mpf('1e-3')
    sec = richardson(ZS, [z*z*v for z, v in zip(ZS, vals)])
    assert abs(sec - (mpf(11)/12 - a)) < mpf('1e-2'), (a, sec)
print('PASS: eq. (D-wall-two-term) c_tau/z + e_tau/z^2, and the argument half of')
print('      eq. (second-order-match): (11/12-a)/z^2, one half the coefficient jet at n ~ 2z.')

for x in ('0.05', '0.2', '0.5', '0.875', '1', '2', '7', '50'):
    a = mpf(x)
    g = psi(1, a)
    assert tau_infty(a) < a*g*(2*a-1)/(2*a**2*g-1) < 1, x
print('PASS: eq. (wall-ordering) tau_infty(a) < tau_cw(a,1) < 1 across a in [0.05, 50].')


def c_of(a):
    return 4/psi(1, a) - 4*a + mpf(7)/2


prev = None
for x in ('0.001', '0.01', '0.1', '0.5', '1', '2', '5', '20', '100', '1000'):
    a = mpf(x)
    assert psi(1, a)**2 + psi(2, a) > 0, x
    cur = c_of(a)
    if prev is not None:
        assert cur < prev, x
    prev = cur
assert abs(c_of(mpf('1e-9')) - mpf(7)/2) < mpf('1e-8')
assert abs(c_of(mpf('1e8')) - mpf(3)/2) < mpf('1e-7')
for t in ('0.001', '0.05', '1', '5', '30'):
    tv = mpf(t)
    assert tv/(1-exp(-tv)) > 1 + tv/2, t
for s in ('0.25', '1', '3', '9'):
    sv = mpf(s)
    kk = quad(lambda t: (t/(1-exp(-t)))*((sv-t)/(1-exp(-(sv-t)))), [0, sv])
    assert kk > sv**2/(1-exp(-sv)), s
print('PASS: prop:c-monotone -- g^2 + g\' > 0, c strictly decreasing, limits 7/2 and 3/2,')
print('      and the two kernel inequalities the proof rests on.')

for x in ('0.5', '1.0', '3.0'):
    a = mpf(x)
    g = psi(1, a)
    S = build_S(a, 400)
    for n in (50, 200, 400):
        T = sum(S[k]*S[n-k] for k in range(n+1))
        w = [S[k]*S[n-k]/T for k in range(n+1)]
        al = [psi(1, a+k) for k in range(n+1)]
        Ea = sum(w[k]*al[k] for k in range(n+1))
        EK = sum(w[k]*k for k in range(n+1))
        assert abs(EK - mpf(n)/2) < mpf('1e-30'), (x, n)     # K_n symmetric about n/2
        Cov = sum(w[k]*(k-EK)*(al[k]-Ea) for k in range(n+1))
        pn = sum(S[k]*S[n-k]*al[k] for k in range(n+1))
        qn = g/2*sum((n-k)*S[k]*S[n-k]*al[k] for k in range(n+1))
        assert abs(qn/pn - (g*n/4 - g/2*Cov/Ea)) < mpf('1e-28'), (x, n)
        assert Cov < 0 and qn/pn > g*n/4, (x, n)
print('PASS: eq. (wall-slope-covariance) as an exact identity, with Cov(K_n, alpha) < 0')
print('      and hence q_n/p_n > gn/4 -- the inequality that keeps degree one exposed.')

NSO = [200, 400, 800, 1600]
SO = max(NSO)
for x in ('0.5', '0.75', '1.5', '3'):
    a = mpf(x)
    g = psi(1, a)
    S = build_S(a, SO)
    dat = wall_data(a, S, NSO)
    tn = [1 - dat[n][0]/dat[n][1] for n in NSO]
    lead = richardson(NSO, [n*(t - tau_infty(a)) for n, t in zip(NSO, tn)])
    want = g/2*(a - mpf(11)/12)
    assert abs(lead - want) < mpf('1e-4')*abs(want), (x, lead, want)
    below = tn[-1] < tau_infty(a)
    assert below == (a < mpf(11)/12), x        # the orientation flip at 11/12
    for kap in (mpf('1.3'), mpf('0.7')):
        tk = [1 - (dat[n][0] + (kap-1)*dat[n][2])/dat[n][1] for n in NSO]
        slope = richardson(NSO, [t/n for n, t in zip(NSO, tk)])
        assert abs(slope + g/4*(kap-1)) < mpf('1e-4')*abs(g/4*(kap-1)), (x, kap)
        assert (slope < 0) == (kap > 1), (x, kap)
    for xx in (mpf(1), mpf(3), mpf(-2)):
        vals = [1 - (dat[n][0] + (-xx/n)*dat[n][2])/dat[n][1] for n in NSO]
        lim = richardson(NSO, vals)
        assert abs(lim - (tau_infty(a) + g*xx/4)) < mpf('1e-4'), (x, xx)
        assert abs(4*((tau_infty(a) + g*xx/4) - tau_infty(a))/g - xx) < mpf('1e-40')
print('PASS: cor:wall-orientation -- the 1/n law with its sign flip at a = 11/12,')
print('      the transverse O(n) slope and its trichotomy, and the tangent-cone limit,')
print('      whose inversion for x returns c_tau.')
print('ALL PASS')
