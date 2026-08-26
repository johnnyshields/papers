#!/usr/bin/env python3
r"""The cubic trigamma upper bound psi_1(y) < 1/y + 1/(2y^2) + 1/(6y^3),
eq. (trig-upper-cubic) of lem:trigamma-bounds.

The paper already carries psi_1(y) < 1/(y-1/2), eq. (trig-upper-half).  The cubic
bound is a separate statement, needed once and only once -- for the branch
a >= 1/sqrt(2) of the L_2 estimate in lem:boundary-positivity -- and it is not implied by the
half-shift bound in the range where it is used.  This probe checks that, the
integrand inequality the proof rests on, and the bound itself.

  * x coth x < 1 + x^2/3 for x > 0, with the sharpness x coth x - (1+x^2/3)
    = -x^4/45 + O(x^6) at the origin;
  * hence theta/(1-e^{-theta}) = (theta/2) coth(theta/2) + theta/2 < 1 + theta/2 + theta^2/12,
    whose Laplace transform against e^{-y theta} is exactly the cubic bound, so the
    integral representation eq. (trigamma-integral) transfers it;
  * psi_1(y) < 1/y + 1/(2y^2) + 1/(6y^3) numerically across eight decades;
  * the cubic bound is not redundant: on a >= 1/sqrt(2) it is strictly sharper
    than 1/(y-1/2), and substituting 1/(y-1/2) in place of it in the L_2 numerator
    of lem:boundary-positivity does not close that estimate.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

x, theta, y, a = sp.symbols('x theta y a', positive=True)

expansion = sp.series(x/sp.tanh(x) - (1 + x**2/3), x, 0, 6).removeO()
assert sp.simplify(expansion + x**4/45) == 0
print('PASS: x coth x - (1+x^2/3) = -x^4/45 + O(x^6), so the bound is sharp at 0')

integrand = theta/2*sp.coth(theta/2) + theta/2
majorant = 1 + theta/2 + theta**2/12
assert sp.simplify((integrand - theta/(1 - sp.exp(-theta))).rewrite(sp.exp)) == 0
print('PASS: theta/(1-e^{-theta}) = (theta/2) coth(theta/2) + theta/2, the split the proof uses')
transform = sp.integrate(sp.exp(-y*theta)*majorant, (theta, 0, sp.oo))
assert sp.simplify(transform - (1/y + 1/(2*y**2) + 1/(6*y**3))) == 0
print('PASS: the Laplace transform of 1 + theta/2 + theta^2/12 is exactly')
print('      1/y + 1/(2y^2) + 1/(6y^3), which is eq. (trig-upper-cubic)')

mp.mp.dps = 40
for y0 in ['1e-6', '0.01', '0.25', '0.5', '0.7071067811865476', '1', '2',
           '5', '20', '200', '1e4']:
    v = mp.mpf(y0)
    assert v*mp.coth(v) < 1 + v**2/3
    assert mp.psi(1, v) < 1/v + 1/(2*v**2) + 1/(6*v**3)
    assert mp.psi(1, v) > 1/v + 1/(2*v**2)
print('PASS: x coth x < 1+x^2/3 and the two-sided trigamma bracket')
print('      1/y+1/(2y^2) < psi_1(y) < 1/y+1/(2y^2)+1/(6y^3) across eight decades')

# not redundant: sharper than 1/(y-1/2) where lem:boundary-positivity uses it, and the
# half-shift bound does not close the L_2 estimate there
for y0 in ['0.7071067811865476', '0.8', '1', '2', '10']:
    v = mp.mpf(y0)
    assert 1/v + 1/(2*v**2) + 1/(6*v**3) < 1/(v - mp.mpf(1)/2)
gsym = sp.Symbol('g', positive=True)
L2_numer = 4*a**4*gsym - 4*a**3 - 2*a**2*gsym - 2*a**2 + a + 1
assert sp.simplify(L2_numer.subs(gsym, 1/(a - sp.Rational(1, 2)))
                   - (a - 1)/(2*a - 1)) == 0
assert sp.simplify(L2_numer.subs(gsym, 1/a + 1/(2*a**2) + 1/(6*a**3))
                   + (a**2 + 1)/(3*a)) == 0
print('PASS: the half-shift bound puts the L_2 numerator at exactly (a-1)/(2a-1), which')
print('      is nonnegative for every a >= 1 and so proves nothing there, whereas the')
print('      cubic bound puts it at exactly -(a^2+1)/(3a) < 0 for every a > 0.  So')
print('      eq. (trig-upper-cubic) is load-bearing in lem:boundary-positivity, not decorative')

print('ALL PASS')
