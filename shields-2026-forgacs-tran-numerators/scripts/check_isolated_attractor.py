#!/usr/bin/env python3
r"""Paper section `sec:consequences` (Global and local zero laws), section `subsec:isolated-attractors`
`subsec:isolated-attractors`, `prop:isolated-dominant-cancellation` and
`cor:panel-B-attractor`.

Every claim of the two attractor propositions, one assertion per printed line.
Exact rational/symbolic arithmetic wherever the paper's argument is exact --
the Rouche split on |t| = 1/2, the positivity of b on [-1/2, 1/2], the Vieta
separation, the resultant -- and mpmath at raised precision only where a root
has to be located or a rate measured.

  (A1) The denominator expansion Q(t) + z t = 1 + (z - 7/4)t + (7/8)t^2 - (1/8)t^3.
  (A2) P_0 = z^2+z+1, P_1 = -z^3 + (3/4)z^2 - (1/4)z + 15/4, and the coefficient
       recurrence they run from, both against a direct series division.
  (A3) cor:panel-B-attractor's first assertion: [z^{m+2}]P_m = (-1)^m and deg P_m = m+2,
       for every m in a long range -- the induction's conclusion, checked, and
       the base cases it runs from.
  (A4) The reduced numerator B, and the exact Laurent-Gauss
       division, and that the Laurent-polynomial quotient carries no t^m with
       m >= 2, which is what makes P_m = F_{m+2} hold from m = 2.  The paper
       claims only the eventual identity that lem:laurent-reduction supplies,
       so the sharp threshold is strictly more than the paper needs.
  (A5) P_m = F_{m+2} for m >= 2, and NOT at m = 0, 1,
       so "from m = 2 onward" is shown sharp rather than merely sufficient.
  (A6) The Rouche split 64B = calQ + calH on |t| = 1/2 -- the paper writes the
       two pieces `\mathcal Q` and `\mathcal H`, carried below as the local q and
       h: the bound |calH| <= 2625/64, the exact minimum |calQ|^2 >= 298424/137
       attained at cos(theta) = 1809/2192, and the strict gap
       298424/137 - (2625/64)^2 = 278329079/561152 > 0.
  (A7) The zeros of q are (36 +- 8i sqrt(14))/137, of modulus 4/sqrt(137) < 1/2.
  (A8) b > 0 on [-1/2, 1/2]: every term positive on [-1/2, 0]; and on [0, 1/2]
       the completed square q >= 3584/137, h decreasing via
       h' = 2t^2(3t^3 - 55t^2 + 282t - 378) with that cubic increasing
       (derivative >= 917/4) and negative at 1/2 (-2003/8), so h >= -1495/64
       and b >= 24561/8768 > 0.
  (A9) Hence exactly one conjugate pair of zeros of B in |t| < 1/2, both simple
       and nonreal; t_* is the upper one.
  (A10) The Vieta separation at z_*: -8(Q + z_* t) is t^3 - 7t^2 + (14 - 8z_*)t - 8,
        u + v = 7 - t_*, uv = 8/t_*, and |u|, |v| > 3/2 -- the paper's own
        contradiction, run as an exact inequality and then confirmed on the
        located roots.  Hence chi_* < 1/3, the spectral gap cor:panel-B-attractor's
        proof establishes, and t_* is
        the unique minimum-modulus denominator zero.
  (A11) z_* is nonreal, and the decimals cor:panel-B-attractor prints for z_*,
        together with those for t_*, which the proof selects but does not display.
  (A12) The algebraicity of z_*: D((z^2+z+1)/(z-2), z) = -R(z)/(8(z-2)^3) as an
        exact rational identity, R(z_*) = 0, and N(t, 2) = 7 so z_* != 2.
  (A13) z_m = z_* + O(3^-m): |z_m - z_*| measured against 3^{-m}
        over an m-ladder, asserted to decay AT LEAST that fast, with the
        realized log-ratio reported.  Precision is raised with m, since at
        m = 60 the difference is below 10^-28.
  (A14) prop:isolated-dominant-cancellation itself, on configurations the panel-B
        example does not cover: nu = 2 (a double reduced-numerator zero, where
        the packet is a PAIR converging at the halved rate sigma^{M/2}), and
        r = 2.  The count in U is asserted to be exactly nu.
  (A15) The hypothesis eq:isolated-dominant-root is shown load-bearing: at a
        cancellation on a NON-dominant branch the conclusion fails -- no zero of
        F_M stays near z_0.
  (A17b) eq:cancellation-intersection-multiplicity: the packet size is the LOCAL
        INTERSECTION MULTIPLICITY of the numerator and denominator curves,
        nu = ord_{t_0} B = ord_{t_0} N(t, g(t)) = I_{(t_0,z_0)}(N, D) with
        g = -Q/t^r -- so it is intrinsic to N and D and not an artifact of the
        Laurent reduction.  At nu = 1 and nu = 2, and once on a numerator that
        genuinely carries z so the substitution is not vacuous.  Smoothness of
        the denominator curve is checked outright (dD/dz = t_0^r != 0, t_0 a
        simple zero of D(.,z_0)), since it is what makes the substitution the
        intersection.
  (A19) The proposition's hypotheses are r >= 1, Q(0) != 0 and B != 0, and NOT
        eq:Q-hypotheses: it is local, and its proof reads the zeros of Q only
        through the minimum-modulus condition it states outright.  Three
        witnesses that FAIL positive-rootedness and satisfy BOTH halves of the
        conclusion -- a Q with a negative zero (chi_0 = 1/32), a Q with a
        nonreal conjugate pair (chi_0 = 1/25), and the latter at nu = 2.  Both
        halves: a FIXED neighborhood U holding exactly nu zeros at every tested
        M, found by scanning radii rather than assumed, and |z - z_0| <=
        K chi_0^{M/nu} with a single K across the ladder.  Without these the
        widened statement would be words.
"""

import sympy as sp
from mpmath import mp

t, z, x = sp.symbols('t z x')

nfail = 0
def ok(msg):
    print('PASS:', msg)
def die(msg):
    raise AssertionError(msg)


# ---------------------------------------------------------------- setup
Q = sp.expand((1 - t) * (1 - t / 2) * (1 - t / 4))
r = 1
N = 1 + z + z**2 + t * (2 - z)
Dtz = sp.expand(Q + z * t**r)

# (A1)
want = sp.expand(1 + (z - sp.Rational(7, 4)) * t + sp.Rational(7, 8) * t**2
                 - sp.Rational(1, 8) * t**3)
assert sp.simplify(Dtz - want) == 0, '(A1) denominator expansion'
ok('(A1) Q(t) + zt = 1 + (z - 7/4)t + (7/8)t^2 - (1/8)t^3')


# ------------------------------------------------- coefficient polynomials
def coeff_polys(num, den, M):
    """P_m from the exact convolution sum_j d_j P_{m-j} = N_m, d_0 = den(0)."""
    dp = sp.Poly(den, t)
    d = [sp.expand(dp.coeff_monomial(t**j)) for j in range(dp.degree() + 1)]
    np_ = sp.Poly(num, t)
    Ncoef = [sp.expand(np_.coeff_monomial(t**j)) for j in range(np_.degree() + 1)]
    d0 = d[0]
    P = []
    for m in range(M + 1):
        rhs = Ncoef[m] if m < len(Ncoef) else sp.Integer(0)
        acc = sum(d[j] * P[m - j] for j in range(1, min(m, len(d) - 1) + 1))
        P.append(sp.expand(sp.cancel((rhs - acc) / d0)))
    return P

MMAX = 46
P = coeff_polys(N, Dtz, MMAX)

# cross-check against a direct series division, so the recurrence is not
# checked against itself
ser = sp.series(N / Dtz, t, 0, 9).removeO()
for m in range(9):
    got = sp.expand(sp.Poly(sp.expand(ser), t).coeff_monomial(t**m) if m else
                    sp.expand(ser.subs(t, 0)))
    assert sp.simplify(got - P[m]) == 0, f'(A2) series vs recurrence at m={m}'
ok('(A2) P_m from the recurrence agrees with a direct series division, m <= 8')

assert sp.simplify(P[0] - (z**2 + z + 1)) == 0, '(A2) P_0'
assert sp.simplify(P[1] - (-z**3 + sp.Rational(3, 4) * z**2
                           - sp.Rational(1, 4) * z + sp.Rational(15, 4))) == 0, '(A2) P_1'
ok('(A2) P_0 = z^2+z+1 and P_1 = -z^3 + (3/4)z^2 - (1/4)z + 15/4')

for m in range(3, MMAX + 1):
    lhs = P[m]
    rhs = sp.expand(-(z - sp.Rational(7, 4)) * P[m - 1]
                    - sp.Rational(7, 8) * P[m - 2]
                    + sp.Rational(1, 8) * P[m - 3])
    assert sp.simplify(lhs - rhs) == 0, f'(A2) recurrence at m={m}'
# m = 2 uses P_{-1} = 0
rhs2 = sp.expand(-(z - sp.Rational(7, 4)) * P[1] - sp.Rational(7, 8) * P[0])
assert sp.simplify(P[2] - rhs2) == 0, '(A2) recurrence at m=2 with P_{-1}=0'
ok(f'(A2) the coefficient recurrence holds for 2 <= m <= {MMAX}, with P_(-1) = 0')

# (A3)
for m in range(MMAX + 1):
    pm = sp.Poly(P[m], z)
    assert pm.degree() == m + 2, f'(A3) deg P_{m} = {pm.degree()} != {m+2}'
    lead = pm.coeff_monomial(z**(m + 2))
    assert lead == (-1)**m, f'(A3) [z^{m+2}]P_{m} = {lead} != {(-1)**m}'
ok(f'(A3) cor:panel-B-attractor: [z^(m+2)]P_m = (-1)^m and '
   f'deg P_m = m+2 for every m <= {MMAX}')


# ------------------------------------------------------ Laurent reduction
B_paper = sp.Rational(1, 64) * (t**6 - 22 * t**5 + 141 * t**4 - 252 * t**3
                                + 548 * t**2 - 288 * t + 64)
E, mu = 2, 0
A_expr = sp.expand(sp.simplify(t**(r * E) * N.subs(z, -Q / t**r)))
assert sp.simplify(A_expr - t**mu * B_paper) == 0, '(A4) A = t^mu B'
ok('(A4) the reduced numerator: t^{rE} N(t, -Q/t^r) = B(t) with '
   '64B = t^6-22t^5+141t^4-252t^3+548t^2-288t+64  (E = 2, mu = 0)')

S_paper = t / 8 - sp.Rational(15, 8) + (z + sp.Rational(11, 4)) / t - 1 / t**2
ident = sp.simplify(N - (Dtz * S_paper + t**(-2) * B_paper))
assert ident == 0, f'(A4) Laurent identity residue {ident}'
ok('(A4) the exact Laurent identity: N = D*(t/8 - 15/8 + (z+11/4)/t - 1/t^2) '
   '+ t^(-2) B, exactly')

Spoly = sp.Poly(sp.expand(S_paper * t**2), t)   # t^2 S has degree 3
powers = [k - 2 for k in range(Spoly.degree() + 1)
          if sp.simplify(Spoly.coeff_monomial(t**k)) != 0]
assert max(powers) < 2, f'(A4) quotient carries t^{max(powers)}, not < 2'
ok(f'(A4) the Laurent quotient carries only t^k with k in {sorted(powers)}, '
   'all < 2, which is what makes the reduction exact from m = 2')

# (A5)
F = coeff_polys(B_paper, Dtz, MMAX + 4)
for m in range(2, MMAX + 1):
    assert sp.simplify(P[m] - F[m + 2]) == 0, f'(A5) P_{m} != F_{m+2}'
ok(f'(A5) P_m = F_(m+2) for 2 <= m <= {MMAX}')
assert sp.simplify(P[0] - F[2]) != 0 and sp.simplify(P[1] - F[3]) != 0, \
    '(A5) the reduction unexpectedly already holds at m = 0 or 1'
ok('(A5) and it FAILS at m = 0 and m = 1, so "from m = 2 onward" is sharp')


# --------------------------------------------------------- Rouche on |t|=1/2
b = sp.expand(64 * B_paper)
q = 548 * t**2 - 288 * t + 64
h = t**6 - 22 * t**5 + 141 * t**4 - 252 * t**3
assert sp.expand(b - (q + h)) == 0, '(A6) b != q + h'

hbound = sp.Rational(1, 64) + sp.Rational(22, 32) + sp.Rational(141, 16) + sp.Rational(252, 8)
assert hbound == sp.Rational(2625, 64), f'(A6) triangle bound {hbound}'
# and it really does bound |h| on the circle
mp.dps = 40
hmax = max(abs(sp.lambdify(t, h, 'mpmath')(mp.mpf(1) / 2 * mp.exp(mp.mpc(0, 1) * th)))
           for th in [mp.mpf(k) * 2 * mp.pi / 4000 for k in range(4000)])
assert hmax <= mp.mpf(2625) / 64, f'(A6) realized |h| max {hmax} exceeds 2625/64'
ok(f'(A6) |h| <= 2625/64 = {float(hbound):.6f} on |t| = 1/2  '
   f'(realized max {float(hmax):.6f})')

# |q|^2 on |t| = 1/2 as a polynomial in x = cos(theta), exactly.  Write
# t = (x + i s)/2 with x, s real on the unit circle, expand, then reduce by
# s^2 = 1 - x^2; |q|^2 is even in s, so the reduction is exact.
xr, sr = sp.symbols('x s', real=True)
qq = sp.expand(q.subs(t, (xr + sp.I * sr) / 2))
q2raw = sp.expand(sp.re(qq)**2 + sp.im(qq)**2)
q2s = sp.Poly(q2raw, sr)
acc = sp.Integer(0)
for (k,), c in q2s.terms():
    assert k % 2 == 0, f'(A6) |q|^2 has an odd power s^{k}, so it is not a function of cos alone'
    acc += c * (1 - xr**2)**(k // 2)
q2poly = sp.Poly(sp.expand(acc), xr)
x = xr
want_q2 = sp.Poly(35072 * xr**2 - 57888 * xr + 26065, xr)
assert sp.simplify(q2poly.as_expr() - want_q2.as_expr()) == 0, \
    f'(A6) |q|^2 = {q2poly.as_expr()}'
ok('(A6) |q|^2 = 35072x^2 - 57888x + 26065 on |t| = 1/2, x = cos(theta), exactly')

xmin = sp.Rational(57888, 2 * 35072)
assert xmin == sp.Rational(1809, 2192), f'(A6) vertex at {xmin}'
assert -1 <= xmin <= 1, '(A6) vertex outside the range of cos'
q2min = sp.nsimplify(want_q2.as_expr().subs(x, xmin))
assert sp.simplify(q2min - sp.Rational(298424, 137)) == 0, f'(A6) min {q2min}'
ok('(A6) its minimum over x in [-1,1] is 298424/137, at x = 1809/2192 '
   '(interior, so the vertex is the minimum)')

gap = sp.Rational(298424, 137) - sp.Rational(2625, 64)**2
assert sp.simplify(gap - sp.Rational(278329079, 561152)) == 0, f'(A6) gap {gap}'
assert gap > 0
ok(f'(A6) 298424/137 - (2625/64)^2 = 278329079/561152 = {float(gap):.6f} > 0, '
   'so |q| > |h| on |t| = 1/2')

# (A7)
qroots = sp.solve(sp.Eq(q, 0), t)
want_roots = {sp.Rational(36, 137) + 8 * sp.I * sp.sqrt(14) / 137,
              sp.Rational(36, 137) - 8 * sp.I * sp.sqrt(14) / 137}
assert {sp.simplify(sp.radsimp(rr)) for rr in qroots} == \
       {sp.simplify(sp.radsimp(rr)) for rr in want_roots}, f'(A7) {qroots}'
modsq = sp.simplify(sp.Abs(qroots[0])**2)
assert sp.simplify(modsq - sp.Rational(16, 137)) == 0, f'(A7) |root|^2 = {modsq}'
assert sp.Rational(16, 137) < sp.Rational(1, 4)
ok('(A7) the zeros of q are (36 +- 8i sqrt(14))/137, of modulus '
   '4/sqrt(137) = %.6f < 1/2' % float(sp.sqrt(sp.Rational(16, 137))))


# ------------------------------------------------- positivity of b on [-1/2,1/2]
bp = sp.Poly(b, t)
negcoeffs = [(k, bp.coeff_monomial(t**k)) for k in range(bp.degree() + 1)]
# on [-1/2, 0]: every term of b(t) is positive
for k, c in negcoeffs:
    if c == 0:
        continue
    sign_on_neg = c * (-1)**k
    assert sign_on_neg > 0, f'(A8) term t^{k} coeff {c} is not positive on [-1/2, 0]'
ok('(A8) on [-1/2, 0] every term of b has positive sign (even powers with '
   'positive coefficients, odd with negative), so b > 0 there')

qsq = 548 * (t - sp.Rational(36, 137))**2 + sp.Rational(3584, 137)
assert sp.expand(qsq - q) == 0, '(A8) completed square'
ok('(A8) q(t) = 548(t - 36/137)^2 + 3584/137, hence q >= 3584/137 everywhere')

hprime = sp.expand(sp.diff(h, t))
assert sp.expand(hprime - 2 * t**2 * (3 * t**3 - 55 * t**2 + 282 * t - 378)) == 0, \
    "(A8) h' factorization"
cubic = 3 * t**3 - 55 * t**2 + 282 * t - 378
cubicp = sp.expand(sp.diff(cubic, t))          # 9t^2 - 110t + 282
# minimum of cubicp on [0,1/2] is at t = 1/2 (vertex at 110/18 > 1/2)
assert sp.Rational(110, 18) > sp.Rational(1, 2)
cpmin = cubicp.subs(t, sp.Rational(1, 2))
assert cpmin == sp.Rational(917, 4), f'(A8) min derivative {cpmin}'
ok("(A8) h' = 2t^2(3t^3 - 55t^2 + 282t - 378), and that cubic has derivative "
   ">= 917/4 > 0 on [0, 1/2], so it is increasing there")
c_half = cubic.subs(t, sp.Rational(1, 2))
assert c_half == sp.Rational(-2003, 8), f'(A8) cubic(1/2) = {c_half}'
assert c_half < 0
ok('(A8) its value at 1/2 is -2003/8 < 0, so the cubic is negative on [0, 1/2] '
   "and h' <= 0: h is decreasing there")
h_half = h.subs(t, sp.Rational(1, 2))
assert h_half == sp.Rational(-1495, 64), f'(A8) h(1/2) = {h_half}'
lower = sp.Rational(3584, 137) + sp.Rational(-1495, 64)
assert sp.simplify(lower - sp.Rational(24561, 8768)) == 0, f'(A8) {lower}'
assert lower > 0
ok(f'(A8) h >= h(1/2) = -1495/64, so b >= 3584/137 - 1495/64 = 24561/8768 = '
   f'{float(lower):.6f} > 0 on [0, 1/2]')

# independent confirmation that b has no real zero in [-1/2, 1/2]
realroots = [rr for rr in sp.Poly(b, t).real_roots()
             if sp.Rational(-1, 2) <= rr <= sp.Rational(1, 2)]
assert realroots == [], f'(A8) real roots of b in [-1/2,1/2]: {realroots}'
ok('(A8) independent route: exact real-root isolation finds no real zero of b '
   'in [-1/2, 1/2]')

# (A9)
mp.dps = 60
broots = mp.polyroots([mp.mpf(int(c)) for c in sp.Poly(b, t).all_coeffs()],
                      maxsteps=200, extraprec=200)
inside = [rr for rr in broots if abs(rr) < mp.mpf(1) / 2]
assert len(inside) == 2, f'(A9) {len(inside)} zeros of B inside |t| < 1/2'
assert all(abs(mp.im(rr)) > mp.mpf('1e-20') for rr in inside), '(A9) a zero is real'
assert abs(inside[0] - mp.conj(inside[1])) < mp.mpf('1e-40'), '(A9) not a conjugate pair'
tstar = inside[0] if mp.im(inside[0]) > 0 else inside[1]
# simplicity: gcd(b, b') has no root there
gcdbb = sp.gcd(sp.Poly(b, t), sp.Poly(sp.diff(b, t), t))
assert sp.Poly(gcdbb, t).degree() == 0, f'(A9) B is not squarefree: gcd {gcdbb}'
ok(f'(A9) exactly two zeros of B in |t| < 1/2, a nonreal conjugate pair, and B '
   f'is squarefree so both are simple; t_* = {mp.nstr(tstar, 12)}')

# (A11) decimals
zstar = -sp.lambdify(t, Q, 'mpmath')(tstar) / tstar
def trunc(val, ndec):
    """The decimal expansion of `val` cut, not rounded, after `ndec` places.

    A displayed constant followed by `\\ldots` asserts that the expansion BEGINS
    with the digits shown, so it must be a truncation.  Rounding the last digit
    up makes the assertion false at that place: Im z_* is 1.36749157536..., so
    `1.3674915754\\ldots` names a digit string the number does not have.
    """
    body = mp.nstr(val, 30)
    neg = body.startswith('-')
    ip, fp = body.lstrip('-').split('.')
    return ('-' if neg else '') + ip + '.' + fp[:ndec]

# The corollary prints z_* alone; t_* is selected by the argument but not
# displayed, and the caption points at the corollary rather than repeating it.
# Both printed strings are checked, and t_* is kept as an unprinted cross-check.
for shown, val, lbl in [('-0.5655268358', mp.re(zstar), 'Re z_*  (printed)'),
                        ('1.3674915753', mp.im(zstar), 'Im z_*  (printed)'),
                        ('0.3096778032', mp.re(tstar), 'Re t_*  (not printed)'),
                        ('0.2349211750', mp.im(tstar), 'Im t_*  (not printed)')]:
    got = trunc(val, len(shown.split('.')[1]))
    assert got == shown, f'(A11) {lbl}: paper shows {shown}, truncation is {got}'
ok('(A11) the printed z_* = -0.5655268358... + 1.3674915753... i is a TRUNCATION '
   'of the true value at every place, as \\ldots requires, and so is the '
   'unprinted t_* = 0.3096778032... + 0.2349211750... i that the argument selects')
ok(f'(A11) full precision: t_* = {mp.nstr(tstar, 20)}, z_* = {mp.nstr(zstar, 20)}')
assert abs(mp.im(zstar)) > mp.mpf('1e-20'), '(A11) z_* is real'
ok('(A11) z_* is nonreal')


# ------------------------------------------------------- Vieta separation
cubic_den = sp.expand(-8 * Dtz)
assert sp.expand(cubic_den - (t**3 - 7 * t**2 + (14 - 8 * z) * t - 8)) == 0, \
    '(A10) -8(Q + zt) shape'
ok('(A10) -8(Q(t) + zt) = t^3 - 7t^2 + (14 - 8z)t - 8')

droots = mp.polyroots([mp.mpf(1), mp.mpf(-7), 14 - 8 * zstar, mp.mpf(-8)],
                      maxsteps=200, extraprec=200)
droots.sort(key=lambda w: abs(w))
assert abs(droots[0] - tstar) < mp.mpf('1e-40'), '(A10) t_* is not a denominator zero'
u, v = droots[1], droots[2]
assert abs(u + v - (7 - tstar)) < mp.mpf('1e-40'), '(A10) Vieta u+v'
assert abs(u * v - 8 / tstar) < mp.mpf('1e-40'), '(A10) Vieta uv'
ok('(A10) Vieta at z_*: u + v = 7 - t_* and uv = 8/t_*, both to 40 digits')
assert abs(u) > mp.mpf(3) / 2 and abs(v) > mp.mpf(3) / 2, \
    f'(A10) |u| = {abs(u)}, |v| = {abs(v)} not both > 3/2'
ok(f'(A10) |u| = {mp.nstr(abs(u),10)}, |v| = {mp.nstr(abs(v),10)}, both > 3/2 '
   "as the paper's contradiction argument requires")
# the contradiction itself, as stated: |u| <= 3/2 would force |u+v| > 55/6 > 15/2
assert mp.mpf(32) / 3 - mp.mpf(3) / 2 == mp.mpf(55) / 6
assert abs(7 - tstar) < mp.mpf(15) / 2, f'(A10) |7 - t_*| = {abs(7-tstar)}'
assert mp.mpf(55) / 6 > mp.mpf(15) / 2
ok('(A10) the contradiction closes: 32/3 - 3/2 = 55/6 > 15/2 > |7 - t_*| = '
   f'{mp.nstr(abs(7-tstar),10)}')
chi = max(abs(tstar / u), abs(tstar / v))
assert chi < mp.mpf(1) / 3, f'(A10) chi_* = {chi} >= 1/3'
ok(f'(A10) the spectral gap: chi_* = {mp.nstr(chi,10)} < 1/3, and t_* is '
   'the unique minimum-modulus denominator zero (moduli '
   f'{mp.nstr(abs(tstar),8)}, {mp.nstr(abs(u),8)}, {mp.nstr(abs(v),8)})')


# ------------------------------------------------------------- resultant
Rz = z**6 - 12 * z**5 + 44 * z**4 - 44 * z**3 + 96 * z**2 - 104 * z + 135
assert sp.simplify(N.subs(z, 2)) == 7, '(A12) N(t,2)'
ok('(A12) N(t, 2) = 7, so z_* != 2 and the substitution t = (z^2+z+1)/(z-2) is legal')
tsub = (z**2 + z + 1) / (z - 2)
lhs = sp.simplify(sp.together(Dtz.subs(t, tsub)))
rhs = sp.simplify(-Rz / (8 * (z - 2)**3))
assert sp.simplify(sp.expand(sp.together(lhs - rhs))) == 0, \
    f'(A12) substitution identity residue {sp.simplify(lhs - rhs)}'
ok('(A12) z_* is algebraic: D((z^2+z+1)/(z-2), z) = -R(z)/(8(z-2)^3) '
   'exactly, R = z^6-12z^5+44z^4-44z^3+96z^2-104z+135')
Rval = sp.lambdify(z, Rz, 'mpmath')(zstar)
assert abs(Rval) < mp.mpf('1e-45'), f'(A12) R(z_*) = {Rval}'
ok(f'(A12) R(z_*) = {mp.nstr(abs(Rval), 5)}, so z_* is an algebraic number and '
   'a root of R')
assert sp.Poly(Rz, z).is_irreducible, '(A12) R is reducible'
ok('(A12) R is irreducible over Q, so z_* has degree exactly 6')


# --------------------------------------------------- the attractor rate
def Fm_roots_near(Bexpr, den, M, target, dps):
    mp.dps = dps
    FM = coeff_polys(Bexpr, den, M)[M]
    co = [mp.mpf(str(sp.Rational(c))) if sp.im(c) == 0 else mp.mpc(str(c))
          for c in sp.Poly(FM, z).all_coeffs()]
    rts = mp.polyroots(co, maxsteps=400, extraprec=400)
    return min(rts, key=lambda w: abs(w - target))

print()
prev = None
for M, dps in [(20, 60), (30, 70), (40, 90), (50, 110), (60, 130)]:
    mp.dps = dps
    zs = -sp.lambdify(t, Q, 'mpmath')(tstar) / tstar   # recompute at this dps
    zM = Fm_roots_near(B_paper, Dtz, M, zs, dps)
    err = abs(zM - zs)
    bound = mp.mpf(3)**(-M)
    assert err < bound, f'(A13) |z_M - z_*| = {err} exceeds 3^-{M} = {bound}'
    rate = -mp.log(err) / (M * mp.log(3))
    ok(f'(A13) M = {M:3d}: |z_M - z_*| = {mp.nstr(err, 6):>14s} < 3^-M = '
       f'{mp.nstr(bound, 6):>14s}   (realized rate sigma^M with sigma = '
       f'3^-{mp.nstr(rate, 5)})')
    prev = err
ok('(A13) z_m = z_* + O(3^-m): the decay is at least 3^-M over the '
   'whole ladder, and the realized rate is strictly faster, consistent with '
   f'chi_* = {mp.nstr(chi, 6)} < 1/3')


# ------------------------------- prop:isolated-dominant-cancellation, general
print()

def denom_roots_at(Qe, rr, z0):
    den = sp.expand(Qe + z * t**rr)
    co = [mp.mpc(str(sp.N(c.subs(z, sp.Float(str(mp.re(z0)), 40)
                                 + sp.I * sp.Float(str(mp.im(z0)), 40)), 50)))
          for c in sp.Poly(den, t).all_coeffs()]
    rts = mp.polyroots(co, maxsteps=400, extraprec=400)
    rts.sort(key=lambda w: abs(w))
    return rts


def attractor_test(Qe, rr, Bexpr, t0, nu, label, Ms):
    """Check prop:isolated-dominant-cancellation on one configuration.

    Asserts the two things the proposition claims and nothing weaker: that
    EXACTLY nu zeros of F_M collapse onto z_0 (so the packet size is the
    multiplicity, not merely at least one zero), and that they do so at the
    rate sigma^(M/nu) for sigma just above chi_0 -- which is the claim the
    1/nu exponent lives in, and it is checked as a log-ratio across an M
    ladder rather than against a fixed tolerance.
    """
    mp.dps = 100
    den = sp.expand(Qe + z * t**rr)
    z0 = -sp.lambdify(t, Qe, 'mpmath')(t0) / t0**rr
    assert abs(sp.lambdify(t, Bexpr, 'mpmath')(t0)) < mp.mpf('1e-40'), \
        f'[{label}] t_0 is not a zero of B'
    assert abs(sp.lambdify(t, Bexpr, 'mpmath')(mp.mpf(0))) > mp.mpf('1e-20'), \
        f'[{label}] B(0) = 0'
    dr = denom_roots_at(Qe, rr, z0)
    assert abs(dr[0] - t0) < mp.mpf('1e-25'), \
        f'[{label}] t_0 is not the minimum-modulus denominator zero'
    assert abs(dr[1]) > abs(dr[0]) * (1 + mp.mpf('1e-6')), \
        f'[{label}] the minimum-modulus zero is not unique'
    chi0 = abs(dr[0] / dr[1])
    sigma = chi0 ** (mp.mpf(1) / nu)

    errs = []
    for M in Ms:
        FM = coeff_polys(Bexpr, den, M)[M]
        co = [mp.mpc(str(sp.N(c, 60))) for c in sp.Poly(FM, z).all_coeffs()]
        rts = sorted(mp.polyroots(co, maxsteps=500, extraprec=500),
                     key=lambda w: abs(w - z0))
        d = [abs(w - z0) for w in rts[:nu + 1]]
        # exactly nu form the packet: a wide gap separates the nu-th from the next
        assert d[nu] > 1000 * d[nu - 1], \
            f'[{label}] M={M}: no clean packet of {nu}; distances ' \
            f'{[mp.nstr(x, 4) for x in d]}'
        errs.append(d[nu - 1])

    # the decay rate, measured: |z - z_0| should fall at least like sigma^(M/nu)
    for (M1, e1), (M2, e2) in zip(zip(Ms, errs), list(zip(Ms, errs))[1:]):
        realized = (mp.log(e1) - mp.log(e2)) / ((M2 - M1) / mp.mpf(nu))
        claimed = -mp.log(sigma) * nu / mp.mpf(nu)
        assert realized >= -mp.log(sigma) * mp.mpf('0.9'), \
            f'[{label}] decay {mp.nstr(realized,6)} slower than ' \
            f'-log sigma = {mp.nstr(-mp.log(sigma),6)} between M={M1},{M2}'
    ok(f'({label}) nu = {nu}, r = {rr}, chi_0 = {mp.nstr(chi0, 6)}: exactly {nu} '
       f'zero(s) of F_M collapse onto z_0 at every M in {Ms} (the next is '
       f'>1000x farther), and the outermost falls from {mp.nstr(errs[0], 4)} to '
       f'{mp.nstr(errs[-1], 4)}, at least the claimed sigma^(M/nu) with '
       f'sigma^(1/nu) = {mp.nstr(sigma, 6)}')
    return chi0


QB = sp.expand((1 - t) * (1 - t / 2) * (1 - t / 4))
# nu = 1, r = 1, but a different B from panel B's
attractor_test(QB, 1, sp.expand((1 - 5 * t) * (1 + t**2)), mp.mpf(1) / 5, 1,
               'A14 r=1 nu=1', [20, 30, 40])
# nu = 2: the packet is a genuine PAIR and the exponent is sigma^(M/2)
attractor_test(QB, 1, sp.expand((1 - 5 * t)**2 * (1 + t)), mp.mpf(1) / 5, 2,
               'A14 r=1 nu=2', [20, 30, 40])
# r = 2, which panel B does not exercise
attractor_test(QB, 2, sp.expand((1 - 5 * t) * (1 + t**2)), mp.mpf(1) / 5, 1,
               'A14 r=2 nu=1', [40, 60, 80])
ok('(A14) prop:isolated-dominant-cancellation holds beyond the panel-B setting: '
   'at r = 2, and at nu = 2 where the packet is a genuine PAIR, so the '
   'sigma^(M/nu) exponent of eq:isolated-cancellation-rate is load-bearing '
   'rather than cosmetic')

# (A15) a cancellation on a NON-dominant branch: the conclusion fails, so the
# hypothesis eq:isolated-dominant-root is load-bearing rather than defensive.
mp.dps = 80
t0far = mp.mpf(3)                       # not a zero of Q, and not minimum-modulus
Bfar = sp.expand((1 - t / 3) * (1 + t**2))
denfar = sp.expand(QB + z * t)
z0far = -sp.lambdify(t, QB, 'mpmath')(t0far) / t0far
assert abs(sp.lambdify(t, Bfar, 'mpmath')(t0far)) < mp.mpf('1e-40'), '(A15) B(t_0) != 0'
assert abs(sp.lambdify(t, Bfar, 'mpmath')(mp.mpf(0))) > mp.mpf('1e-20'), '(A15) B(0) = 0'
drf = denom_roots_at(QB, 1, z0far)
assert min(abs(w - t0far) for w in drf) < mp.mpf('1e-25'), \
    '(A15) t_0 is not a denominator zero at z_0'
assert abs(drf[0] - t0far) > mp.mpf('0.5'), '(A15) t_0 is unexpectedly dominant'
ok(f'(A15) counter-configuration: B(3) = 0 and z_0 = {mp.nstr(z0far, 8)}, but the '
   f'denominator moduli at z_0 are {[mp.nstr(abs(w), 8) for w in drf]}, so the '
   'minimum-modulus zero is not t_0 = 3 and eq:isolated-dominant-root FAILS')

closest = []
for M in [30, 45, 60]:
    FM = coeff_polys(Bfar, denfar, M)[M]
    co = [mp.mpc(str(sp.N(c, 50))) for c in sp.Poly(FM, z).all_coeffs()]
    rts = mp.polyroots(co, maxsteps=500, extraprec=500)
    closest.append(min(abs(w - z0far) for w in rts))
assert min(closest) > mp.mpf('1e-3'), \
    f'(A15) a zero approached z_0 anyway: {[mp.nstr(c, 4) for c in closest]}'
assert closest[-1] > closest[0] / 10, \
    f'(A15) the nearest zero is still shrinking: {[mp.nstr(c, 4) for c in closest]}'
ok('(A15) and no zero of F_M approaches z_0: the nearest sits at '
   f'{[mp.nstr(c, 5) for c in closest]} for M = 30, 45, 60 -- not shrinking, so '
   'the dominance hypothesis is load-bearing, not decorative')

# ------------------------------- the intermediate steps of the general proof
# A14 checks the CONCLUSION of prop:isolated-dominant-cancellation.  These check
# the three steps the proof passes through, which is where an error would hide
# without changing the conclusion on the configurations tested.
print()

def proof_steps(Qe, rr, Bexpr, t0, nu, label):
    mp.dps = 60
    den = sp.expand(Qe + z * t**rr)
    Qf = sp.lambdify(t, Qe, 'mpmath')
    z0 = -Qf(t0) / t0**rr
    dD_dt = sp.lambdify((t, z), sp.diff(den, t), 'mpmath')
    dD_dz = sp.lambdify((t, z), sp.diff(den, z), 'mpmath')

    # (i) eq:dominant-root-derivative.  Track the branch t(z) numerically and
    #     differentiate it, against the closed form -t_0^r / dD/dt.
    def branch(zz):
        w = mp.mpc(t0)
        for _ in range(80):
            w = w - sp.lambdify((t, z), den, 'mpmath')(w, zz) / dD_dt(w, zz)
        return w
    hstep = mp.mpf(10) ** (-15)
    tprime_num = (branch(z0 + hstep) - branch(z0 - hstep)) / (2 * hstep)
    tprime_cf = -t0**rr / dD_dt(mp.mpc(t0), z0)
    assert abs(tprime_num - tprime_cf) < mp.mpf('1e-12') * max(1, abs(tprime_cf)), \
        f'[{label}] eq:dominant-root-derivative: {tprime_num} vs {tprime_cf}'
    assert abs(tprime_cf) > mp.mpf('1e-20'), f'[{label}] t\'(z_0) = 0'
    # and the identity -dD/dz / dD/dt, the form the paper writes first
    assert abs(-dD_dz(mp.mpc(t0), z0) / dD_dt(mp.mpc(t0), z0) - tprime_cf) < mp.mpf('1e-30'), \
        f'[{label}] the two forms of t\'(z_0) disagree'
    ok(f'({label}) eq:dominant-root-derivative: t\'(z_0) = -dD/dz / dD/dt = '
       f'-t_0^r / dD/dt = {mp.nstr(tprime_cf, 8)}, nonzero, and matching a '
       'numerically differentiated branch to 12 digits')

    # (ii) eq:isolated-amplitude-order.  A(z) = -B(t(z))/dD/dt(t(z),z) must have a
    #      zero of EXACTLY order nu at z_0 -- the step that needs t'(z_0) != 0.
    Bf = sp.lambdify(t, Bexpr, 'mpmath')
    def A(zz):
        w = branch(zz)
        return -Bf(w) / dD_dt(w, zz)
    for k, rad in enumerate([mp.mpf('1e-3'), mp.mpf('1e-4'), mp.mpf('1e-5')]):
        vals = [abs(A(z0 + rad * mp.exp(2j * mp.pi * j / 8))) for j in range(8)]
        if k == 0:
            prev, prad = sum(vals) / 8, rad
        else:
            cur = sum(vals) / 8
            order = mp.log(prev / cur) / mp.log(prad / rad)
            assert abs(order - nu) < mp.mpf('0.05'), \
                f'[{label}] |A| ~ |z-z_0|^{mp.nstr(order,4)}, not ^{nu}'
            prev, prad = cur, rad
    ok(f'({label}) eq:isolated-amplitude-order: |A(z)| ~ |z-z_0|^{nu} on shrinking '
       f'circles (measured exponent {mp.nstr(order, 6)}), so A has a zero of '
       f'exactly order nu = {nu}; this is what t\'(z_0) != 0 buys')

    # (iii) eq:isolated-dominant-expansion.  t(z)^{M+1} F_M(z) - A(z) must fall
    #       like eta^M for eta just above chi_0.  Measured off the diagonal, at a
    #       z where A is not small, so the remainder is not masked.
    dr = denom_roots_at(Qe, rr, z0)
    chi0 = abs(dr[0] / dr[1])
    zt = z0 + mp.mpf('0.02')
    errs = []
    for M in (14, 22, 30):
        FM = coeff_polys(Bexpr, den, M)[M]
        FMv = sp.lambdify(z, FM, 'mpmath')(zt)
        errs.append(abs(branch(zt)**(M + 1) * FMv - A(zt)))
    r1 = (mp.log(errs[0]) - mp.log(errs[1])) / 8
    r2 = (mp.log(errs[1]) - mp.log(errs[2])) / 8
    for rr_ in (r1, r2):
        assert rr_ >= -mp.log(chi0) * mp.mpf('0.85'), \
            f'[{label}] remainder decays at e^-{mp.nstr(rr_,5)}/step, slower than ' \
            f'chi_0 = {mp.nstr(chi0,5)} allows'
    ok(f'({label}) eq:isolated-dominant-expansion: t(z)^(M+1) F_M(z) - A(z) falls '
       f'from {mp.nstr(errs[0],4)} to {mp.nstr(errs[-1],4)} over M = 14,22,30, at '
       f'rate e^-{mp.nstr(r2,5)} per step against the -log(chi_0) = '
       f'{mp.nstr(-mp.log(chi0),5)} the proof claims')

proof_steps(QB, 1, sp.expand((1 - 5 * t) * (1 + t**2)), mp.mpf(1) / 5, 1, 'A17 nu=1')
proof_steps(QB, 1, sp.expand((1 - 5 * t)**2 * (1 + t)), mp.mpf(1) / 5, 2, 'A17 nu=2')
ok('(A17) the three intermediate steps of prop:isolated-dominant-cancellation -- '
   'the branch derivative, the exact order of the amplitude zero, and the '
   'remainder rate -- hold independently of the conclusion A14 measures')

# ------------------------------------------------ rem:cancellation-meaning
# The bridge that licenses the word "cancellation" and carries the necessary
# obstruction stated in the closing question of sec:conclusion: for t_0 != 0 and
# z_0 = -Q(t_0)/t_0^r,   B(t_0) = 0  <=>  N(t_0, z_0) = 0 = D(t_0, z_0).
print()
for (Qe, rr, Nexpr, lbl) in [
        (QB, 1, 1 + z + z**2 + t * (2 - z), 'panel B'),
        (sp.expand((1 - t) * (1 - t / 3)), 2, sp.expand(1 + z * t), 'r=2, bivariate N'),
        (sp.expand((1 - t) * (1 - t / 2)), 1, sp.expand((z**2 + 1) + t * (1 - z)), 'r=1, deg Q = 2')]:
    den = sp.expand(Qe + z * t**rr)
    assert sp.Poly(Nexpr, t).degree() < sp.Poly(den, t).degree(), f'[{lbl}] N is not proper'
    # Reduce.  N(t, -Q/t^r) is a rational function whose denominator is a
    # power of t; clearing it gives A(t) directly, with no search over E.
    expr = sp.cancel(sp.together(Nexpr.subs(z, -Qe / t**rr)))
    numer, denom = sp.fraction(expr)
    dp = sp.Poly(sp.expand(denom), t)
    assert dp.is_monomial, f'[{lbl}] the cleared denominator {denom} is not a t-monomial'
    Ae = sp.Poly(sp.expand(numer), t)
    mue = min(k for (k,), c in Ae.terms() if c != 0)
    Be = sp.expand(sp.cancel(Ae.as_expr() / t**mue))
    assert sp.simplify(Be.subs(t, 0)) != 0, f'[{lbl}] B(0) = 0'
    # The equivalence is a consequence of the identity, not of root chasing:
    # N(t, -Q/t^r) = B(t) / (c t^k) as rational functions, so for t_0 != 0 the
    # three conditions B(t_0) = 0, N(t_0,z_0) = 0 and D(t_0,z_0) = 0 stand or
    # fall together.  Assert the identity exactly, then evaluate at the roots so
    # the conclusion is exhibited and not merely inferred.  (A CRootOf cannot be
    # substituted and simplified to exact zero, which is a SymPy limit, not a
    # failure of the claim -- hence the numeric evaluation.)
    kden = sp.Poly(sp.expand(denom), t).monoms()[0][0]
    cden = sp.Poly(sp.expand(denom), t).coeffs()[0]
    ident = sp.simplify(sp.expand(t**kden * Nexpr.subs(z, -Qe / t**rr) * cden
                                  - t**mue * Be))
    assert ident == 0, f'[{lbl}] reduction identity residue {ident}'

    mp.dps = 50
    Nf = sp.lambdify((t, z), Nexpr, 'mpmath')
    Qf = sp.lambdify(t, Qe, 'mpmath')
    Df = sp.lambdify((t, z), den, 'mpmath')
    Bf = sp.lambdify(t, Be, 'mpmath')
    Bco = [mp.mpc(str(sp.N(c, 40))) for c in sp.Poly(Be, t).all_coeffs()]
    tested = 0
    for t0 in (mp.polyroots(Bco, maxsteps=400, extraprec=400)
               if sp.Poly(Be, t).degree() > 0 else []):
        if abs(t0) < mp.mpf('1e-30'):
            continue
        z0 = -Qf(t0) / t0**rr
        scale = max(mp.mpf(1), abs(t0)) ** sp.Poly(Nexpr, t).degree()
        assert abs(Df(t0, z0)) < mp.mpf('1e-30') * scale, f'[{lbl}] D(t_0,z_0) != 0'
        assert abs(Nf(t0, z0)) < mp.mpf('1e-30') * scale, \
            f'[{lbl}] B(t_0) = 0 but N(t_0,z_0) = {Nf(t0, z0)}'
        tested += 1

    # converse: where B does not vanish, D still does but N must not
    ctrl = mp.mpf(1) / 7
    assert abs(Bf(ctrl)) > mp.mpf('1e-20'), f'[{lbl}] control point is a zero of B'
    z0c = -Qf(ctrl) / ctrl**rr
    assert abs(Df(ctrl, z0c)) < mp.mpf('1e-30'), f'[{lbl}] control D != 0'
    assert abs(Nf(ctrl, z0c)) > mp.mpf('1e-15'), \
        f'[{lbl}] N vanishes at a control point where B does not'
    ok(f'(A16) [{lbl}] rem:cancellation-meaning: the identity '
       f't^{kden} * c * N(t, -Q/t^r) = t^{mue} B(t) holds exactly, and over the '
       f'{tested} nonzero zeros of B it exhibits B(t_0) = 0 => N(t_0,z_0) = 0 = '
       'D(t_0,z_0); at a control t_0 = 1/7 with B(t_0) != 0, D still vanishes but '
       'N does not, so the equivalence is not one-directional bookkeeping')
ok('(A16) the reduction identity t^{rE} N(t, -Q/t^r) = t^mu B(t) therefore makes '
   '"numerator-denominator cancellation" literal for the original N, which is what '
   "the closing question of sec:conclusion needs to state its obstruction")

# (A17b) `eq:cancellation-intersection-multiplicity`: the packet size is the LOCAL
# INTERSECTION MULTIPLICITY of N and D, not merely the order of B.  With
# g(t) = -Q(t)/t^r, the claim is
#     nu = ord_{t_0} B = ord_{t_0} N(t, g(t)) = I_{(t_0,z_0)}(N, D),
# the last equality because D = 0 is smooth at (t_0,z_0) (dD/dz = t_0^r != 0) and is
# parameterized there by t |-> (t, g(t)), so intersecting N with that branch is
# exactly substituting g.  Checked at nu = 1 and nu = 2, on a numerator carrying a
# genuine z-dependence so the substitution is not vacuous.
for Qe, r_, Ne, tag in [
        ((1 - t) * (1 - t / 2), 1, 1 - t / sp.Rational(3, 2), 'nu = 1'),
        ((1 - t) * (1 - t / 2), 1, (1 - t / sp.Rational(3, 2))**2, 'nu = 2'),
        ((1 - t) * (1 - t / 2), 1, (2 * t - 3) * (1 + z * t) / 2, 'nu = 1, N carries z'),
]:
    Qe, Ne = sp.expand(Qe), sp.expand(Ne)
    g = -Qe / t**r_
    E_ = sp.Poly(Ne, z).degree() if Ne.has(z) else 0
    A_ = sp.simplify(sp.expand(t**(r_ * E_) * Ne.subs(z, g)))
    Apol = sp.Poly(sp.simplify(A_), t)
    mu_ = min(m[0] for m in Apol.monoms())
    Bp = sp.Poly(sp.cancel(A_ / t**mu_), t)
    # t_0: the nonzero zero of B that is also a simple zero of D at z_0
    t0 = None
    for rt in Bp.all_roots():
        if sp.simplify(rt) != 0:
            t0 = rt
            break
    assert t0 is not None, tag
    z0 = sp.simplify(g.subs(t, t0))
    ordB = sp.Poly(Bp.as_expr(), t).as_expr()
    nu_B = 0
    e = sp.simplify(ordB)
    while sp.simplify(e.subs(t, t0)) == 0:
        nu_B += 1
        e = sp.simplify(sp.cancel(e / (t - t0)))
    # ord of N(t, g(t)) at t_0, computed WITHOUT the t^{rE} / t^mu factors
    Ng = sp.simplify(Ne.subs(z, g))
    nu_N, e = 0, sp.simplify(sp.together(Ng))
    num = sp.fraction(sp.cancel(e))[0]
    while sp.simplify(sp.expand(num).subs(t, t0)) == 0:
        nu_N += 1
        num = sp.cancel(sp.expand(num) / (t - t0))
    # smoothness of D at (t_0, z_0): dD/dz = t_0^r != 0, and t_0 simple in D(.,z0)
    D_ = Qe + z * t**r_
    assert sp.simplify(sp.diff(D_, z).subs({t: t0})) != 0, tag
    Dz0 = sp.Poly(sp.expand(D_.subs(z, z0)), t)
    assert sp.simplify(Dz0.as_expr().subs(t, t0)) == 0
    assert sp.simplify(sp.diff(Dz0.as_expr(), t).subs(t, t0)) != 0, (tag, 'not simple')
    assert nu_B == nu_N, (tag, nu_B, nu_N)
    ok(f'(A17b) {tag}: ord_t0 B = {nu_B} = ord_t0 N(t, g(t)); D is smooth at '
       f'(t_0, z_0) with dD/dz = t_0^r != 0 and t_0 a simple zero of D(.,z_0), so '
       f'that common order IS the local intersection multiplicity I(N, D) of '
       f'`eq:cancellation-intersection-multiplicity`')
ok('(A17b) hence the packet size is intrinsic to the original numerator and '
   'denominator curves and not an artifact of the Laurent reduction')

# ------------------------- the exclusion in rem:cancellation-meaning must be
# CLOSED.  z_0 = 0 satisfies z_0 notin (0,inf), yet every neighborhood of 0
# meets (0,inf), so a packet attracted to 0 need not be exceptional.  This
# pins the counterexample that forced [0,inf).
print()
Qce = sp.expand((1 - t) * (1 - t / 2))
Nce = 1 - t
Dce = sp.expand(Qce + z * t)
t0ce = sp.Integer(1)
z0ce = sp.simplify(-Qce.subs(t, t0ce))
assert z0ce == 0, f'(A18) z_0 = {z0ce}, expected 0'
assert sp.simplify(Nce.subs(t, t0ce)) == 0 and sp.simplify(Dce.subs([(t, t0ce), (z, z0ce)])) == 0
qroots = sorted(sp.solve(Qce, t), key=lambda w: abs(sp.N(w)))
assert qroots[0] == 1 and abs(sp.N(qroots[1])) > 1, f'(A18) {qroots}'
ok('(A18) Q=(1-t)(1-t/2), r=1, N=1-t is admissible, and t_0 = 1 is a simple, '
   'uniquely minimum-modulus zero of D(.,0) with B(t_0) = 0 -- so every '
   'hypothesis of prop:isolated-dominant-cancellation holds at z_0 = 0, which '
   'lies OUTSIDE (0,inf)')

mp.dps = 60
Pce = coeff_polys(Nce, Dce, 40)
for m in (10, 20, 30, 40):
    co = [mp.mpf(str(sp.Rational(c))) for c in sp.Poly(Pce[m], z).all_coeffs()]
    rts = mp.polyroots(co, maxsteps=400, extraprec=400)
    npos = sum(1 for w in rts if abs(mp.im(w)) < mp.mpf('1e-40') and mp.re(w) > 0)
    assert npos == len(rts), \
        f'(A18) m={m}: only {npos} of {len(rts)} zeros are positive'
    small = min(rts, key=lambda w: abs(w))
    assert mp.re(small) > 0, f'(A18) the attracted zero is not positive: {small}'
ok('(A18) yet EVERY zero of P_m is positive for m = 10, 20, 30, 40 -- the '
   'attracted zero included, which approaches z_0 = 0 from the right at '
   f'{mp.nstr(min(mp.polyroots([mp.mpf(str(sp.Rational(c))) for c in sp.Poly(Pce[20], z).all_coeffs()], maxsteps=400, extraprec=400), key=abs), 6)} '
   'at m = 20, about 2^-m/4')
ok('(A18) so "z_0 notin (0,inf) => the packet is exceptional" is FALSE at '
   'z_0 = 0, and rem:cancellation-meaning and the closing question of '
   'sec:conclusion state the exclusion against the CLOSED ray [0,inf)')

# ===========================================================================
# (A19) the widened hypotheses: r >= 1, Q(0) != 0, B != 0, and NO
# positive-rootedness.  Each witness FAILS eq:Q-hypotheses.
# ===========================================================================
print()

def _packet(Qe, r_, Be, t0, nu_expect, tag):
    """Check the hypotheses at t0 and both halves of the conclusion."""
    mp.dps = 60
    Qe, Be = sp.expand(Qe), sp.expand(Be)
    assert sp.simplify(Be.subs(t, t0)) == 0, (tag, 'B(t0) != 0')
    z0e = sp.simplify(-Qe.subs(t, t0) / t0**r_)
    z0 = mp.mpf(str(sp.N(z0e, 50)))
    # positive-rootedness must FAIL -- that is the whole point of the witness
    qr = sp.Poly(Qe, t).all_roots()
    assert not all(sp.im(sp.N(w, 30)) == 0 and sp.N(w, 30) > 0 for w in qr), \
        (tag, 'this witness does not actually fail eq:Q-hypotheses')
    # t0 is a SIMPLE zero of D(.,z0) and its unique minimum-modulus finite zero
    Dz0 = sp.Poly(sp.expand(Qe + z0e * t**r_), t)
    assert sp.simplify(Dz0.as_expr().subs(t, t0)) == 0, tag
    assert sp.simplify(sp.diff(Dz0.as_expr(), t).subs(t, t0)) != 0, (tag, 'not simple')
    others = [mp.mpc(str(sp.re(sp.N(w, 50))), str(sp.im(sp.N(w, 50))))
              for w in Dz0.all_roots() if sp.simplify(w - t0) != 0]
    t0n = mp.mpf(str(sp.N(t0, 50)))
    # `eq:local-spectral-ratio`: the max over the OTHER finite zeros, union {0},
    # so a denominator with no other finite zero gives chi_0 = 0 rather than -inf.
    chi0 = max([abs(t0n) / abs(w) for w in others], default=mp.mpf(0))
    assert chi0 < 1, (tag, 'not uniquely minimum modulus', chi0)
    # the two halves of the conclusion
    Ms = (5, 7, 9, 11, 13)
    Fs = coeff_polys(Be, sp.expand(Qe + z * t**r_), max(Ms))
    roots_by_M = {}
    for M in Ms:
        co = sp.Poly(sp.expand(Fs[M]), z).all_coeffs()
        roots_by_M[M] = mp.polyroots([mp.mpf(str(sp.N(c, 50))) for c in co],
                                     maxsteps=800, extraprec=800)
    # (i) a FIXED neighborhood U containing exactly nu zeros at every M
    RU = None
    for e in range(1, 26):
        cand = abs(z0) * mp.mpf(2)**(-e) if z0 != 0 else mp.mpf(2)**(-e)
        if all(sum(1 for w in roots_by_M[M] if abs(w - z0) < cand) == nu_expect
               for M in Ms):
            RU = cand
            break
    assert RU is not None, (tag, 'no fixed U holds exactly nu zeros',
                            {M: sorted(abs(w - z0) for w in roots_by_M[M])[:3] for M in Ms})
    # (ii) those nu zeros converge at the claimed rate chi0^(M/nu)
    gaps = [max(abs(w - z0) for w in roots_by_M[M] if abs(w - z0) < RU) for M in Ms]
    K = max(g / chi0**(mp.mpf(M) / nu_expect) for g, M in zip(gaps, Ms))
    Kmin = min(g / chi0**(mp.mpf(M) / nu_expect) for g, M in zip(gaps, Ms))
    assert K / Kmin < mp.mpf(50), (tag, 'K not uniform', K, Kmin)
    return z0, chi0, RU, gaps, K

for Qe, r_, Be, t0, nu_, tag in [
        ((1 - t) * (1 + t / 2), 1, 1 - 4 * t, sp.Rational(1, 4), 1,
         'Q = (1-t)(1+t/2) has a NEGATIVE zero'),
        (1 - t + t**2, 1, 1 - 5 * t, sp.Rational(1, 5), 1,
         'Q = 1-t+t^2 has a NONREAL conjugate pair'),
        (1 - t + t**2, 1, (1 - 5 * t)**2, sp.Rational(1, 5), 2,
         'the same nonreal Q at nu = 2'),
]:
    z0, chi0, RU, gaps, K = _packet(Qe, r_, Be, t0, nu_, tag)
    ok(f'(A19) {tag}: z_0 = {mp.nstr(z0, 8)}, chi_0 = {mp.nstr(chi0, 5)}; a FIXED '
       f'U of radius {mp.nstr(RU, 4)} holds exactly nu = {nu_} zero(s) of F_M at '
       f'M = 5,7,9,11,13, and they satisfy |z - z_0| <= K chi_0^(M/nu) with one '
       f'K = {mp.nstr(K, 4)} across all five (gap at M=13: {mp.nstr(gaps[-1], 4)})')
ok('(A19) all three FAIL eq:Q-hypotheses and satisfy both halves of the '
   'conclusion, so r >= 1, Q(0) != 0, B != 0 are the hypotheses '
   'prop:isolated-dominant-cancellation\'s proof consumes; the standing '
   'positive-rootedness is not among them')

print()
print('ALL PASS: check_isolated_attractor')
