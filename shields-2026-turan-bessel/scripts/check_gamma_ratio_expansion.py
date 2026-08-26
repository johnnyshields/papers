#!/usr/bin/env python3
r"""Targeted probe, sec:scaling: the constants of eq:Sm-asymptotic, and the two
explicit-remainder steps the Lean route reaches them through.

eq:Sm-gamma-ratio is an identity and is already proved; what eq:Sm-asymptotic
adds is the expansion of the two gamma ratios it leaves behind, together with the
values of C_a, b and s_a.  Those three constants are stated in the paper without
a derivation, and a formalization that guesses one of them is worse than none, so
they are re-derived here from the four shifts alone and then measured against the
exact weight.

  * the shift bookkeeping.  Writing the gamma-ratio product as a signed sum over
    the four shifts c = a-1/2, a, 1, 2a-1 with signs +,-,+,-, the exponent is
    sum(eps*c) and the 1/m coefficient is sum(eps*(c^2-c)/2).  Both are computed
    symbolically and compared with the paper's b and s_a;
  * the identity eq:Sm-gamma-ratio itself, against the Pochhammer definition of
    S_m, so the normalization C_a = 2^(2a-2)/sqrt(pi) is measured and not copied;
  * the expansion eq:Sm-asymptotic, with the remainder confirmed to be of order
    exactly m^-2 -- the scaled error m^2 (S_m/(C_a 4^m/(m!)^2 m^b) - 1 - s_a/m)
    converges to a finite nonzero limit, so the stated order is neither weaker
    nor stronger than the truth;
  * the two-point Stirling sandwich the Lean route runs on,
    0 <= log Gamma(y) - log Gamma(x) - (L(y) - L(x)) <= 1/(120 x^2) for
    0 < x <= y, where L(t) = t log t - t - (1/2) log t + 1/(12 t).  This is the
    digamma sandwich of lem:trigamma-bounds integrated once, and it is what makes
    the additive constant of Stirling cancel in a difference;
  * the per-shift expansion W(m,c) = (m+c-1/2) log(1+c/m) - c + 1/(12(m+c))
    - 1/(12 m), with |W(m,c) - (c^2-c)/(2m)| <= 5 (|c|+1)^3 / m^2 for
    m >= 4|c| + 4 -- the explicit constant the Lean statement carries.

mpmath throughout at 60 digits: the fourth-order cancellations here are invisible
to double precision.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

mp.mp.dps = 60

# ---------------------------------------------------------------- shift algebra
a = sp.Symbol('a', positive=True)
SHIFTS = [(sp.Integer(1), a - sp.Rational(1, 2)),   # Gamma(m+a-1/2)
          (sp.Integer(-1), a),                      # / Gamma(m+a)
          (sp.Integer(1), sp.Integer(1)),           # Gamma(m+1)
          (sp.Integer(-1), 2*a - 1)]                # / Gamma(m+2a-1)

b_derived = sp.expand(sum(e*c for e, c in SHIFTS))
s_derived = sp.expand(sum(e*(c**2 - c)/2 for e, c in SHIFTS))
b_paper = sp.Rational(3, 2) - 2*a
s_paper = -2*a**2 + sp.Rational(5, 2)*a - sp.Rational(5, 8)

assert sp.simplify(sum(e for e, _ in SHIFTS)) == 0, \
    'the signed shifts must cancel, or the m log m terms do not'
assert sp.simplify(b_derived - b_paper) == 0
assert sp.simplify(s_derived - s_paper) == 0
print('PASS: the four shifts give sum(eps) = 0, sum(eps c) = 3/2 - 2a = b, and')
print('      sum(eps (c^2-c)/2) = -2a^2 + 5a/2 - 5/8 = s_a, the constants of')
print('      eq:Sm-asymptotic')

C_paper = 2**(2*a - 2)/sp.sqrt(sp.pi)


def s_of(av):
    """s_a at a numeric a, in mpmath."""
    return -2*av**2 + mp.mpf(5)/2*av - mp.mpf(5)/8


def b_of(av):
    return mp.mpf(3)/2 - 2*av


def C_of(av):
    return mp.power(2, 2*av - 2)/mp.sqrt(mp.pi)


def sweight(av, m):
    """S_m = (2a+m-1)_m / (m! Gamma(a+m)^2), the definition of sec:coefficients."""
    x = 2*av + m - 1
    return mp.rf(x, m)/(mp.factorial(m)*mp.gamma(av + m)**2)


def gamma_ratio(av, m):
    """The product of the two gamma ratios left by eq:Sm-gamma-ratio."""
    return (mp.gamma(m + av - mp.mpf(1)/2)/mp.gamma(m + av)
            * mp.gamma(m + 1)/mp.gamma(m + 2*av - 1))


# --------------------------------------------------- eq:Sm-gamma-ratio, exactly
AVALS = ['0.15', '0.5', '0.75', '1', '1.5', '2.25', '4', '9.5']
worst_identity = mp.mpf(0)
for astr in AVALS:
    av = mp.mpf(astr)
    for m in (1, 2, 3, 7, 15, 40, 120):
        lhs = sweight(av, m)
        rhs = C_of(av)*mp.mpf(4)**m/mp.factorial(m)**2*gamma_ratio(av, m)
        rel = abs(lhs - rhs)/lhs
        worst_identity = max(worst_identity, rel)
        assert rel < mp.mpf('1e-45'), (astr, m, rel)
print(f'PASS: eq:Sm-gamma-ratio holds to relative {mp.nstr(worst_identity, 3)} across')
print(f'      {len(AVALS)} values of a and m up to 120, so C_a = 2^(2a-2)/sqrt(pi) is measured')

# --------------------------------------------------- eq:Sm-asymptotic, to O(m^-2)


def scaled_error(av, m):
    """m^2 (S_m/(C_a 4^m/(m!)^2 m^b) - 1 - s_a/m)."""
    g = gamma_ratio(av, m)/mp.power(m, b_of(av))
    return m**2*(g - 1 - s_of(av)/m)


for astr in AVALS:
    av = mp.mpf(astr)
    prev = None
    for m in (400, 1600, 6400, 25600):
        e = scaled_error(av, m)
        if prev is not None:
            # the scaled error settles: successive values agree to O(1/m)
            assert abs(e - prev) < abs(prev)/8 + mp.mpf('1e-6'), (astr, m, e, prev)
        prev = e
    # the limit is finite and nonzero, so m^-2 is the exact order, not a weaker
    # statement of an m^-3 truth
    assert mp.mpf('1e-4') < abs(prev) < 100*(av + 2)**4, (astr, prev)
print('PASS: m^2 (S_m/(C_a 4^m/(m!)^2 m^b) - 1 - s_a/m) converges to a finite nonzero')
print('      limit for every tested a, so eq:Sm-asymptotic is sharp at order m^-2')

# an explicit two-sided remainder is what the Lean statement carries, so check one
for astr in AVALS:
    av = mp.mpf(astr)
    K = 40*(abs(av) + 2)**3
    for m in (60, 100, 250, 1000, 5000):
        if m < 8*abs(av) + 8:
            continue
        g = gamma_ratio(av, m)/mp.power(m, b_of(av))
        assert abs(g - 1 - s_of(av)/m) <= K/mp.mpf(m)**2, (astr, m)
print('PASS: |G_m/m^b - 1 - s_a/m| <= 40(a+2)^3/m^2 on m >= 8a+8, an explicit')
print('      two-sided remainder rather than an O-symbol')

# ------------------------------------------------- the two-point Stirling sandwich


def Lam(t):
    return t*mp.log(t) - t - mp.log(t)/2 + 1/(12*t)


worst_lo = mp.inf
worst_hi = mp.mpf(0)
for xs in ['0.05', '0.3', '1', '2.5', '7', '30', '400']:
    x = mp.mpf(xs)
    for d in ['0', '0.01', '0.4', '1', '3.5', '20', '500', '20000']:
        y = x + mp.mpf(d)
        theta = (mp.loggamma(y) - mp.loggamma(x)) - (Lam(y) - Lam(x))
        worst_lo = min(worst_lo, theta)
        worst_hi = max(worst_hi, theta*120*x**2)
        assert theta >= -mp.mpf('1e-45'), (xs, d, theta)
        assert theta <= 1/(120*x**2) + mp.mpf('1e-45'), (xs, d, theta)
print('PASS: 0 <= log Gamma(y) - log Gamma(x) - (L(y) - L(x)) <= 1/(120 x^2) for every')
print(f'      tested 0 < x <= y; the upper bound is attained to a factor {mp.nstr(worst_hi, 3)}')

# the sandwich is the digamma gap integrated: L'(t) = log t - 1/(2t) - 1/(12 t^2)
t = sp.Symbol('t', positive=True)
Lsym = t*sp.log(t) - t - sp.log(t)/2 + 1/(12*t)
assert sp.simplify(sp.diff(Lsym, t) - (sp.log(t) - 1/(2*t) - 1/(12*t**2))) == 0
print("PASS: L'(t) = log t - 1/(2t) - 1/(12 t^2), so log Gamma - L has derivative")
print('      exactly the digamma gap of lem:trigamma-bounds, which is what makes the')
print('      Stirling constant cancel in a difference')

# ------------------------------------------------------------ the per-shift W bound


def W(m, c):
    return (m + c - mp.mpf(1)/2)*mp.log(1 + c/m) - c + 1/(12*(m + c)) - 1/(12*m)


worst_W = mp.mpf(0)
for cs in ['-3.5', '-1', '-0.5', '0', '0.25', '1', '2', '7.5']:
    c = mp.mpf(cs)
    K = 5*(abs(c) + 1)**3
    for m in (int(mp.ceil(4*abs(c) + 4)), 12, 50, 300, 4000):
        if m < 4*abs(c) + 4:
            continue
        err = abs(W(m, c) - (c**2 - c)/(2*m))
        worst_W = max(worst_W, err*m**2/K)
        assert err <= K/mp.mpf(m)**2, (cs, m, err, K/mp.mpf(m)**2)
print('PASS: |W(m,c) - (c^2-c)/(2m)| <= 5(|c|+1)^3/m^2 on m >= 4|c|+4, worst case')
print(f'      {mp.nstr(worst_W, 3)} of the stated constant')

# and the four W's reassemble s_a, which is the whole point of the decomposition
for astr in AVALS:
    av = mp.mpf(astr)
    cs = [av - mp.mpf(1)/2, av, mp.mpf(1), 2*av - 1]
    eps = [1, -1, 1, -1]
    m = mp.mpf(3000)
    tot = sum(e*W(m, c) for e, c in zip(eps, cs))
    assert abs(tot - s_of(av)/m) <= 400*(abs(av) + 2)**3/m**2, (astr, tot)
print('PASS: the signed sum of the four W(m,c) is s_a/m + O(m^-2), so the exponent')
print('      and the 1/m coefficient of eq:Sm-asymptotic both come out of the same')
print('      per-shift lemma')

# ------------------------------------------- the constants the formalization states
# The Lean statement of eq:Sm-asymptotic is deliberately not sharp: it asserts the
# expansion with remainder 250(a+2)^4/t^2 on t >= 1000(a+2)^3, so that every step of
# the proof is a one-line comparison.  A weaker claim can still be false, so it is
# checked here at the threshold itself, where it is tightest.
for astr in AVALS:
    av = mp.mpf(astr)
    thresh = 1000*(av + 2)**3
    bound = 250*(av + 2)**4
    for factor in ('1', '1.0001', '1.5', '4', '30'):
        t = thresh*mp.mpf(factor)
        g = gamma_ratio(av, t)/mp.power(t, b_of(av))
        assert abs(g - 1 - s_of(av)/t) <= bound/t**2, (astr, factor)
print('PASS: the formalized form -- |G/t^b - 1 - s_a/t| <= 250(a+2)^4/t^2 for every')
print('      t >= 1000(a+2)^3 -- holds at the threshold and above it')

print('ALL PASS')
