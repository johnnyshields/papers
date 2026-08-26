#!/usr/bin/env python3
r"""Targeted probe, sec:scaling (prop:c-monotone): the inequality
psi_1(a)^2 + psi_2(a) > 0 that the strict monotonicity of c(a) rests on, and the
recurrence descent that proves it from the trigamma bounds of lem:trigamma-bounds
alone.

check_wall_fan.py already checks the conclusion -- the inequality itself, c
strictly decreasing, the two endpoint limits, and the two kernel inequalities the
paper's Laplace-convolution proof rests on.  This probe is about a different route
to the same inequality, the one a formalization can take: no integrals, only the
series recurrences.  It closes, but only just, and the margin is why this exists.
With P(y) = psi_1(y)^2 + psi_2(y):

  * P is O(y^-4) at infinity, not O(y^-2).  The leading terms of psi_1^2 and
    -psi_2 agree through order y^-3, so any route that bounds the two sides
    separately by their first three terms proves nothing.  That is measured here
    rather than asserted, because it is what rules out the obvious proof;
  * psi_1(y) = 1/y^2 + psi_1(y+1) and psi_2(y) = -2/y^3 + psi_2(y+1) give the
    exact descent P(y) - P(y+1) = 1/y^4 - 2/y^3 + 2 psi_1(y+1)/y^2;
  * the sharp lower bound eq:trig-lower, psi_1(y) > 1/y + 1/(2y^2), applied at
    y+1 makes that positive -- and by an exact margin of 1/(y^2 (y+1)^2 y^2),
    since (2y+3) y^2 - (2y-1)(y+1)^2 = 1 identically.  A cruder lower bound on
    psi_1(y+1) does not close it, which is checked;
  * so P(y) > P(y+n) for every n, and P(y+n) -> 0, giving P > 0 on (0, infinity);
  * c'(a) = -4 psi_2(a)/psi_1(a)^2 - 4, so P > 0 is exactly c' < 0.

mpmath at 50 digits throughout: the fourth-order cancellation in P is below
double precision for y of order 30.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

mp.mp.dps = 50

YVALS = ['1e-5', '0.001', '0.05', '0.3', '0.5', '1', '1.7', '3', '8', '25',
         '100', '1000', '1e5']


def P(y):
    return mp.psi(1, y)**2 + mp.psi(2, y)


# ------------------------------------------------- P > 0, and its true order at infinity
for ys in YVALS:
    y = mp.mpf(ys)
    assert P(y) > 0, (ys, P(y))
print(f'PASS: psi_1^2 + psi_2 > 0 at all {len(YVALS)} tested points, spanning ten decades')

for ys in ['30', '100', '1000', '1e4']:
    y = mp.mpf(ys)
    scaled = P(y)*y**4
    assert abs(scaled - mp.mpf(1)/12) < mp.mpf('0.4'), (ys, scaled)
print('PASS: y^4 (psi_1^2 + psi_2) -> 1/12, so P is O(y^-4) and the two sides of the')
print('      inequality agree through order y^-3')

# the obvious route really is blocked: three-term expansions of the two sides
# cancel identically, so no bound stopping at y^-3 can separate them
ysym = sp.Symbol('y', positive=True)
psi1_3 = 1/ysym + 1/(2*ysym**2) + 1/(6*ysym**3)
minus_psi2_3 = 1/ysym**2 + 1/ysym**3 + 1/(2*ysym**4)
gap = sp.expand(psi1_3**2 - minus_psi2_3)
assert sp.simplify(gap - (1/(12*ysym**4) + 1/(6*ysym**5) + 1/(36*ysym**6))) == 0
print('PASS: the three-term expansions of psi_1^2 and -psi_2 cancel through y^-3')
print('      exactly, leaving a y^-4 head -- so a termwise comparison of the two')
print('      sandwiches decides nothing without the fourth order')

# ------------------------------------------------------------------ the descent
for ys in YVALS:
    y = mp.mpf(ys)
    lhs = P(y) - P(y + 1)
    rhs = 1/y**4 - 2/y**3 + 2*mp.psi(1, y + 1)/y**2
    assert abs(lhs - rhs) <= mp.mpf('1e-38')*max(1, abs(rhs)), (ys, lhs, rhs)
    assert rhs > 0, (ys, rhs)
print('PASS: P(y) - P(y+1) = 1/y^4 - 2/y^3 + 2 psi_1(y+1)/y^2 exactly, and it is')
print('      positive at every tested y, so P is strictly decreasing by unit steps')

# the sharp lower bound closes it, with an exact margin
lower = (2*ysym + 3)/(2*(ysym + 1)**2)          # 1/(y+1) + 1/(2(y+1)^2)
needed = (2*ysym - 1)/(2*ysym**2)               # what 2 psi_1(y+1)/y^2 >= 2/y^3 - 1/y^4 asks
margin = sp.expand((2*ysym + 3)*ysym**2 - (2*ysym - 1)*(ysym + 1)**2)
assert margin == 1, margin
assert sp.simplify(sp.together(lower - needed) - 1/(2*ysym**2*(ysym + 1)**2)) == 0
print('PASS: (2y+3) y^2 - (2y-1)(y+1)^2 = 1 identically, so eq:trig-lower at y+1 beats')
print('      the requirement by exactly 1/(2 y^2 (y+1)^2) -- the descent closes, but')
print('      with no room to spare')

# the crude bound psi_1(y+1) > 1/(y+1) does NOT close it
crude = 1/(ysym + 1)
crude_gap = sp.simplify(sp.together(crude - needed))
assert sp.simplify(crude_gap - (1 - ysym)/(2*ysym**2*(ysym + 1))) == 0
assert crude_gap.subs(ysym, 2) < 0
print('PASS: the crude psi_1(y+1) > 1/(y+1) falls short for every y > 1, so the sharp')
print('      eq:trig-lower is load-bearing in the descent and not a convenience')

# ------------------------------------------------------------------ the limit
for ys in ['0.05', '1', '7']:
    y = mp.mpf(ys)
    tail = [abs(P(y + n)) for n in (10, 100, 1000, 10000)]
    for u, v in zip(tail, tail[1:]):
        assert v < u
    assert tail[-1] < mp.mpf('1e-15')
print('PASS: P(y+n) -> 0 as n -> infinity, so the descent pins P(y) > 0 rather than')
print('      merely P decreasing')

# -------------------------------------------------------- c(a) strictly decreasing
a = sp.Symbol('a', positive=True)
g, gp = sp.symbols('g gp')                       # psi_1(a), psi_2(a)
c_a = 4/g - 4*a + sp.Rational(7, 2)              # eq:c-critical
cprime = sp.simplify(sp.diff(c_a, g)*gp - 4)
assert sp.simplify(cprime - (-4*gp/g**2 - 4)) == 0
assert sp.simplify(sp.together(-4*gp/g**2 - 4) - (-4*(gp + g**2)/g**2)) == 0
print("PASS: c'(a) = -4 psi_2/psi_1^2 - 4 = -4(psi_1^2 + psi_2)/psi_1^2, so c' < 0 is")
print('      the inequality above and nothing else')

for ys in YVALS:
    y = mp.mpf(ys)
    assert -4*mp.psi(2, y)/mp.psi(1, y)**2 - 4 < 0, ys


def cCrit(av):
    return 4/mp.psi(1, av) - 4*av + mp.mpf(7)/2


grid = [mp.mpf(s) for s in
        ['1e-6', '1e-4', '0.01', '0.1', '0.4', '1', '2', '5', '20', '200', '5000']]
for u, v in zip(grid, grid[1:]):
    assert cCrit(u) > cCrit(v), (u, v)
assert cCrit(grid[0]) < mp.mpf(7)/2 and cCrit(grid[-1]) > mp.mpf(3)/2
print("PASS: c' < 0 at every tested a and c is strictly decreasing across the grid,")
print('      inside the range eq:c-range')

print('ALL PASS')
