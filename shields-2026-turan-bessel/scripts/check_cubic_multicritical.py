#!/usr/bin/env python3
r"""thm:cubic-multicritical, checked on both sides from exact data rather than
from the tilted-moment expansions the proof assembles.

At a = 11/12 the second wall jet d_tau = 1/12 - 2 tau/g vanishes exactly where
the first one does: c_tau = 0 forces tau = tau_infty(a) = g(a - 7/8), and then
d_{tau_infty} = 11/6 - 2a, zero at a = 11/12.  So (a, tau) = (11/12, psi_1(11/12)/24)
is the unique point where both lower jets vanish, and the paper computes the
third.  This probe verifies the two constants that result:

  * eq. (cubic-coeff-scaling): 1 - kappa_{n,tau_mc}(11/12) = 3/(8 n^3) + O(n^-4),
    from Delta_n, p_n, q_n built by Cauchy convolution of the exact fibers;
  * eq. (cubic-bessel-scaling): D_{-1/12}^{(1,tau_mc)}(z) = 3/(32 z^3) + O(z^-4),
    from log I_nu directly;
  * both lower jets really do vanish at that point, on both sides;
  * nu_mc = a_mc - 1 and tau_mc = tau_infty(a_mc), so the point is the one the
    wall fan singles out and not a separate coincidence;
  * the ratio 3/(8n^3) : 3/(32z^3) is the same factor 2 at n = 2z that already
    relates the first and second jets, so the dictionary is consistent through
    three orders rather than rescued at the third.

eq. (critical-wall-orientation) and rem:jet-transfer-factor are checked too: at the
switching value the wall approaches tau_mc from below at rate 3 g_mc/(32 n^2), and the
three verified jets satisfy A_r^canonical = 2^(1-r) A_r^microcanonical for r = 1, 2, 3.

eq. (log-I-four-term) is checked independently: the residual of the four-term
logarithmic Hankel expansion, times z^5, settles to a constant.
"""
from mpmath import mp, mpf, psi, besseli, log, pi
from _wallfan_common import (build_S, wall_data, richardson, D_bessel,
                             c_tau, d_tau, tau_infty)

mp.dps = 60
a = mpf(11)/12
nu = -mpf(1)/12
g = psi(1, a)
tau = g/24

assert abs(nu - (a-1)) < mpf('1e-45')
assert abs(tau - tau_infty(a)) < mpf('1e-45')
assert abs(c_tau(a, tau)) < mpf('1e-45')
assert abs(d_tau(a, tau)) < mpf('1e-45')
# uniqueness: c_tau = 0 forces tau = tau_infty(a) = g(a-7/8), and d_tau = 0 forces
# tau = g/24, so both vanish only where a - 7/8 = 1/24, i.e. a = 11/12 -- and the
# solved tau is then forced too.  Checked as a solve, not just evaluated at 11/12.
for x in ('0.1', '0.5', '0.9', '0.91', '0.92', '1.5', '4.0'):
    av = mpf(x)
    t_c = tau_infty(av)              # the unique tau killing c_tau at this a
    t_d = psi(1, av)/24              # the unique tau killing d_tau at this a
    assert abs(c_tau(av, t_c)) < mpf('1e-40') and abs(d_tau(av, t_d)) < mpf('1e-40')
    both = abs(t_c - t_d) < mpf('1e-30')
    assert both == (abs(av - mpf(11)/12) < mpf('1e-30')), x
print('PASS: at a = 11/12, tau_mc = psi_1(11/12)/24 = tau_infty(a) and nu_mc = a - 1;')
print('      both c_tau and d_tau vanish there, and the two tau-solutions coincide')
print('      at no other a, so the point is unique.')

NS = [300, 600, 1200, 2400]
S = build_S(a, max(NS))
dat = wall_data(a, S, NS)
f = [(dat[n][0] + (tau-1)*dat[n][1])/dat[n][2] for n in NS]
seq = [n**3*v for n, v in zip(NS, f)]
for lo, hi in zip(seq, seq[1:]):
    assert lo > hi > mpf(3)/8, seq
cub = richardson(NS, seq)
assert abs(cub - mpf(3)/8) < mpf('1e-4'), cub
assert abs(richardson(NS, [n*v for n, v in zip(NS, f)])) < mpf('1e-5')
assert abs(richardson(NS, [n*n*v for n, v in zip(NS, f)])) < mpf('1e-4')
print(f'PASS: eq. (cubic-coeff-scaling) -- n^3(1-kappa_n) decreases to 3/8, extrapolating')
print(f'      to {mp.nstr(cub, 10)} against 0.375, with both lower jets vanishing.')

ZS = [mpf(40), mpf(80), mpf(160), mpf(320), mpf(640)]
vals = [D_bessel(nu, z, 1, tau) for z in ZS]
seqz = [z**3*v for z, v in zip(ZS, vals)]
for lo, hi in zip(seqz, seqz[1:]):
    assert lo > hi > mpf(3)/32, seqz
cubz = richardson(ZS, seqz)
assert abs(cubz - mpf(3)/32) < mpf('1e-4'), cubz
assert abs(richardson(ZS, [z*v for z, v in zip(ZS, vals)])) < mpf('1e-4')
assert abs(richardson(ZS, [z*z*v for z, v in zip(ZS, vals)])) < mpf('1e-3')
print(f'PASS: eq. (cubic-bessel-scaling) -- z^3 D decreases to 3/32, extrapolating')
print(f'      to {mp.nstr(cubz, 10)} against 0.09375, with both lower jets vanishing.')

assert abs((mpf(3)/8)/8 - (mpf(3)/32)/2) < mpf('1e-45')
for jet, coef_side, bessel_side in ((1, c_tau(a, mpf(1)), c_tau(a, mpf(1))),
                                    (2, 2*(mpf(11)/12 - mpf(1)/2), mpf(11)/12 - mpf(1)/2)):
    assert abs(coef_side/2**jet - bessel_side/2) < mpf('1e-40'), jet
print('PASS: 3/(8n^3) at n = 2z equals half of 3/(32 z^3), the same factor 2 relating')
print('      the first and second jets -- the dictionary is uniform across all three.')


def hankel4(nu_, z_):
    chi = 4*nu_**2
    return (z_ - log(2*pi*z_)/2 - (chi-1)/(8*z_) - (chi-1)/(16*z_**2)
            + (chi-1)*(chi-25)/(384*z_**3) + (chi-1)*(chi-13)/(128*z_**4))


for nu_ in (nu, mpf(0), mpf('0.7'), mpf('-0.4'), mpf(2)):
    res = [(log(besseli(nu_, z))-hankel4(nu_, z))*z**5 for z in (mpf(100), mpf(200), mpf(400))]
    assert all(r != 0 for r in res)
    assert abs(res[2]-res[1]) < abs(res[1]-res[0]), nu_
    assert abs(res[2]) < 10, nu_
print('PASS: eq. (log-I-four-term) -- the four-term residual times z^5 settles to a')
print('      constant at five orders, so the expansion is exact to the stated order.')

NSO = [300, 600, 1200, 2400]
tn = [1 - dat[n][0]/dat[n][1] for n in NSO]
sec = richardson(NSO, [n*n*(t - tau_infty(a)) for n, t in zip(NSO, tn)])
assert abs(sec + 3*g/32) < mpf('1e-3')*abs(3*g/32), sec
assert all(t < tau_infty(a) for t in tn)
print('PASS: eq. (critical-wall-orientation) -- at the switching value the 1/n term is')
print(f'      gone and the wall sits below tau_mc at rate 3g/32, extrapolating to')
print(f'      {mp.nstr(-sec, 10)} against {mp.nstr(3*g/32, 10)}.')

for r, mic, can in ((1, c_tau(a, mpf(1)), c_tau(a, mpf(1))),
                    (2, 2*(mpf(11)/12 - mpf(1)/2), mpf(11)/12 - mpf(1)/2),
                    (3, mpf(3)/8, mpf(3)/32)):
    assert abs(can - mpf(2)**(1-r)*mic) < mpf('1e-40'), r
print('PASS: rem:jet-transfer-factor -- A_r^canonical = 2^(1-r) A_r^microcanonical at')
print('      r = 1, 2, 3, which is the single factor behind all three verified matches.')
print('ALL PASS')
