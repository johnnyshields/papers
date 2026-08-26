#!/usr/bin/env python3
r"""The polynomial certificate behind step 2 of lem:boundary-positivity,
in the range a > 1/2, where MD(N_0-hat, N_m-hat) = F_m is shown positive directly.

The paper reduces F_m > 0 to positivity of B_{a,m}(g) of eq. (Bm-boundary) via a
telescoping trigamma estimate, then bounds B below by substituting the two
strict bounds g > g_0 and s_* < \tilde a = a - 1/2, landing on a single printed
polynomial P(\tilde a, \tilde m), in the shifted variables the paper uses.  There is no convexity step and no derivative certificate:
the whole argument is that B is increasing in g.  This probe checks that, and
the polynomial.

  * the telescoping bound 1/x^2 < 1/(x-1/2) - 1/(x+1/2) sums to
    sum_{r=1}^{m-1} (a+r)^{-2} < (m-1)/[(a+1/2)(a+m-1/2)];
  * F_m > (m-1) B_{a,m}(g), so B_{a,m} > 0 suffices for m >= 2;
  * B is increasing in g -- BOTH g-dependent pieces move up, the first term
    trivially and -s_*(g)/(...) because s_* decreases in g.  The derivative of
    the second has numerator a^3(16a-8), positive exactly on a > 1/2, which is
    why a = 1/2 is excluded here and handled separately;
  * s_* < \tilde a is not an extra input: 2a^2 g_0 - 1 = 2a exactly, so s_*(g_0) = \tilde a,
    and the bound is the same substitution as g -> g_0 rather than a second one;
  * substituting both gives, with t_a = \tilde a and t_m = \tilde m,
    B > P(t_a,t_m)/[(t_a+1)(2t_a+1)^2(t_a+t_m+1)(t_a+t_m+2)(2t_a+2t_m+3)]
    identically, with the printed P;
  * every coefficient of P is positive and every denominator factor is positive
    for \tilde a > 0, \tilde m >= 0.

The a = 1/2 value F_m = pi^2 m/8 - 2(m-1)/(2m-1) and the 0 < a < 1/2 branch
are checked directly.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mpm

a, m, g, ta, tm = sp.symbols('a m g atil mtil', positive=True)   # atil = \tilde a, mtil = \tilde m
half = sp.Rational(1, 2)

s_star = a*(2*a-1)/(2*a**2*g-1)
B = (g*m/(2*(2*a+2*m-3))
     - s_star/((a+half)*(a+m-half))
     + (a-1)/(a*(a+m-1)))
g0 = 1/a + 1/(2*a**2)
sub = {a: ta + half, m: tm + 2}

d_first = sp.simplify(sp.diff(g*m/(2*(2*a+2*m-3)), g))
d_second = sp.simplify(sp.diff(-s_star/((a+half)*(a+m-half)), g))
assert sp.simplify(d_first - m/(2*(2*a+2*m-3))) == 0
num2 = sp.simplify(sp.numer(sp.together(d_second)))
assert sp.simplify(num2 - a**3*(16*a-8)) == 0
print('PASS: B is increasing in g -- the first term has derivative m/[2(2a+2m-3)] > 0 and')
print('      the s_* term has derivative numerator a^3(16a-8), positive exactly on a > 1/2.')

assert sp.simplify(2*a**2*g0 - 1 - 2*a) == 0
assert sp.simplify(s_star.subs(g, g0) - (a - half)) == 0
print('PASS: 2a^2 g_0 - 1 = 2a exactly, so s_*(g_0) = a - 1/2 = ta; the bound s_* < ta is')
print('      the g -> g_0 substitution itself, not an independent estimate.')

B_low = (g0*m/(2*(2*a+2*m-3)) - (a-half)/((a+half)*(a+m-half)) + (a-1)/(a*(a+m-1)))
P_printed = (2*ta**4*tm + 8*ta**4 + 4*ta**3*tm**2 + 23*ta**3*tm + 26*ta**3
             + 2*ta**2*tm**3 + 19*ta**2*tm**2 + 48*ta**2*tm + 35*ta**2
             + 4*ta*tm**3 + 22*ta*tm**2 + 40*ta*tm + 25*ta
             + 2*tm**3 + 9*tm**2 + 14*tm + 8)
den_printed = (ta+1)*(2*ta+1)**2*(ta+tm+1)*(ta+tm+2)*(2*ta+2*tm+3)
assert sp.simplify(sp.together(B_low.subs(sub) - P_printed/den_printed)) == 0
print('PASS: the two substitutions give, with t_a = tilde a and t_m = tilde m,')
print('      B > P(t_a,t_m)/[(t_a+1)(2t_a+1)^2(t_a+t_m+1)(t_a+t_m+2)(2t_a+2t_m+3)]')
print('      identically, with the printed polynomial and the printed denominator.')

lo = min(sp.Poly(P_printed, ta, tm).coeffs())
assert lo > 0, lo
print(f'PASS: every coefficient of P is positive (minimum {lo}), and every denominator')
print('      factor is positive for tilde a > 0, tilde m >= 0, so B > 0 for a > 1/2, m >= 2.')

mpm.mp.dps = 40
Bf = sp.lambdify((a, m, g), B, 'mpmath')
Blf = sp.lambdify((ta, tm), P_printed/den_printed, 'mpmath')
mhalf = mpm.mpf(1)/2


def F_exact(av, mv):
    gv = mpm.psi(1, av)
    ss = av*(2*av-1)/(2*av**2*gv-1)
    cm = mpm.mpf(mv*(mv-1))/(2*(2*av+2*mv-3))
    return (gv*cm - ss*sum(1/(av+r)**2 for r in range(1, mv))
            + (av-1)*(mv-1)/(av*(av+mv-1)))


for av in ('0.5001', '0.51', '0.7', '1.0', '2.0', '5.0', '50.0', '500.0'):
    for mv in (2, 3, 5, 10, 100, 1000, 10000):
        av_ = mpm.mpf(av)
        gv = mpm.psi(1, av_)
        b = Bf(av_, mv, gv)
        bl = Blf(av_ - mhalf, mv - 2)
        assert b > bl > 0, (av, mv)
        assert F_exact(av_, mv) > (mv-1)*b, (av, mv)
        assert F_exact(av_, mv) > 0, (av, mv)
print('PASS: F_m > (m-1) B_{a,m}(g) > (m-1) P/den > 0 across a > 1/2 and m up to 10000.')

for mv in (2, 3, 10, 500):
    lhs = F_exact(mhalf, mv)
    rhs = mpm.pi**2*mv/8 - mpm.mpf(2*(mv-1))/(2*mv-1)
    assert abs(lhs-rhs) < mpm.mpf('1e-30') and lhs > 0, mv
print('PASS: at a = 1/2, F_m = pi^2 m/8 - 2(m-1)/(2m-1) > 0 for m >= 2.')

for av in ('0.05', '0.2', '0.35', '0.49'):
    av_ = mpm.mpf(av)
    assert av_*(2*av_-1)/(2*av_**2*mpm.psi(1, av_)-1) < 0
    for mv in (2, 3, 10, 100, 1000):
        assert mv*(av_+mv-1) > 2*av_*(1-av_)*(2*av_+2*mv-3), (av, mv)
        assert F_exact(av_, mv) > 0, (av, mv)
    assert 2*(2*av_**3-av_**2+1) > 0
print('PASS: for 0 < a < 1/2, s_* < 0, the m = 2 margin 2(2a^3-a^2+1) > 0, and F_m > 0.')
print('ALL PASS')
