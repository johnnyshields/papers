#!/usr/bin/env python3
"""Paper section 2 (Main results), Remark 2.3 (rem:rank-one-threshold), and section 5
(Mixed determinants and coefficientwise positivity, sec:determinant).

Remark 2.3 says the rank-one constant term is shared by the whole family, so that
"the sign of the first nonzero determinant coefficient detects the sharp threshold
in kappa uniformly in a".  What the degree-one coefficient alone supports is the
set identity

    { kappa : Delta_1^(kappa)(a) > 0 for every a > 0 }  =  [1, infinity).

Delta_1^(kappa) is not displayed in the paper; it is eq. (5.2) with M_1 replaced by
M_1^(kappa), i.e. eq. (5.7) scaled by S_0 S_1:

    Delta_1^(kappa)(a) = 2/(a^3 Gamma(a)^4) * [ (kappa-1)/2 (a g)^2 + a g - 1 ],
    g = psi_1(a).

Checked here:
  (1) a g - 1 > 1/(2a) for a > 0                  (eq. (4.2), eq:trig-lower, at y = a)
  (2) kappa >= 1  =>  bracket > 0 on the tested a-grid     (sufficiency of the sign test)
  (3) kappa < 1   =>  bracket < 0 for small a              (necessity of the sign test)
  (4) the bracket is affine and strictly increasing in kappa.

Scope: (2) is a finite grid, so (2)+(4) exhibit the set identity on that grid rather
than prove it for every a; the unconditional statement is eq. (5.2) plus (1), and the
kappa<1 direction is (3).  The positivity for kappa >= 1 at every a > 0 is proved in
the paper, not here.

mpmath at 40 digits; no float arithmetic in the loops.
"""

from mpmath import mp, mpf, psi, gamma

mp.dps = 40


def bracket(a, kappa):
    """(kappa-1)/2 (a g)^2 + a g - 1, the sign of Delta_1^(kappa)(a)."""
    g = psi(1, a)
    ag = a * g
    return (kappa - 1) / mpf(2) * ag**2 + ag - 1


def delta1(a, kappa):
    return 2 / (a**3 * gamma(a) ** 4) * bracket(a, kappa)


LADDER = [mpf(10) ** (-k) for k in range(12, -1, -1)] + [
    mpf(k) / 4 for k in range(1, 41)
] + [mpf(10) ** k for k in range(2, 7)]

# (1) the lower bound a*psi_1(a) - 1 > 1/(2a), i.e. eq. (4.2) at y = a, which the
#     display closing section 5 uses
for a in LADDER:
    lhs = a * psi(1, a) - 1
    assert lhs > 1 / (2 * a), (a, lhs, 1 / (2 * a))
print(f"OK    a*psi_1(a) - 1 > 1/(2a) on {len(LADDER)} values of a "
      f"({min(LADDER)} .. {max(LADDER)})")

# (2) kappa >= 1: bracket, hence Delta_1, is strictly positive at every tested a
for kappa in [mpf(1), mpf(1) + mpf(10) ** -20, mpf(2), mpf(10)]:
    for a in LADDER:
        assert bracket(a, kappa) > 0, (kappa, a, bracket(a, kappa))
        assert delta1(a, kappa) > 0, (kappa, a, delta1(a, kappa))
print("OK    kappa in {1, 1+1e-20, 2, 10}: Delta_1^(kappa)(a) > 0 for every tested a")

# (3) kappa < 1: the bracket goes negative for small a.  a*g ~ 1/a as a -> 0, so the
#     (kappa-1)(ag)^2/2 term dominates; exhibit an explicit witness for each kappa.
#     Report the LARGEST failing a, not the smallest: scanning upward and breaking on
#     the first hit would return the ladder floor for every kappa and hide the
#     kappa-dependence entirely.
print("      kappa        largest tested a with Delta_1^(kappa)(a) < 0")
for kappa in [mpf("0.999999"), mpf("0.99"), mpf("0.5"), mpf(0), mpf(-5)]:
    witness = None
    for a in sorted(LADDER, reverse=True):
        if bracket(a, kappa) < 0:
            witness = a
            break
    assert witness is not None, kappa
    assert delta1(witness, kappa) < 0, (kappa, witness)
    # the witness must move right as kappa falls: failure widens monotonically
    print(f"      {mp.nstr(kappa, 8):>12}  a = {mp.nstr(witness, 6)}   "
          f"Delta_1 = {mp.nstr(delta1(witness, kappa), 6)}")

# (4) strict monotonicity in kappa at fixed a (so the threshold is a single cut)
for a in [mpf("0.01"), mpf("0.5"), mpf(1), mpf(7)]:
    d = bracket(a, mpf(1)) - bracket(a, mpf("0.5"))
    assert d > 0, (a, d)
    # affine in kappa: second difference vanishes
    lo, mid, hi = bracket(a, mpf(0)), bracket(a, mpf(1)), bracket(a, mpf(2))
    assert abs((hi - mid) - (mid - lo)) < mpf(10) ** -30, (a, lo, mid, hi)
print("OK    bracket is affine and strictly increasing in kappa at fixed a")

# eq. (5.7) derived from the coefficient matrices, not restated.  Building
# MD(M_0, M_1^(kappa)) from the entries of section 3 and comparing with the bracket
# is what makes the sign test above a test of the paper rather than of itself.
#   M_0 = [[g, sqrt g],[sqrt g, 1]]  (the display after Theorem 4.2),
#   M_1^(kappa) = [[alpha_1, sqrt g beta_1],[sqrt g beta_1, 1 + g c_1^(kappa)]],
#   alpha_1 = psi_1(a+1), beta_1 = (2a-1)/(2a), c_1^(kappa) = (kappa-1)/2,
#   MD(X,Y) = x11 y22 + x22 y11 - 2 x12 y12.
for a in LADDER:
    g = psi(1, a)
    alpha1 = psi(1, a + 1)
    beta1 = (2 * a - 1) / (2 * a)
    for kappa in (mpf(0), mpf("0.5"), mpf(1), mpf("1.7")):
        c1 = (kappa - 1) / mpf(2)
        MD01 = g * (1 + g * c1) + alpha1 * 1 - 2 * g * beta1        # MD(M_0, M_1^(kappa))
        assert abs(MD01 - bracket(a, kappa) / a**2) < (
            mpf(10) ** -25 * abs(MD01) + mpf(10) ** -30
        ), (a, kappa, MD01)
        # and Delta_1^(kappa) = S_0 S_1 MD(M_0, M_1^(kappa)), S_0 S_1 = 2/(a Gamma(a)^4)
        S0S1 = 2 / (a * gamma(a) ** 4)
        assert abs(delta1(a, kappa) - S0S1 * MD01) < (
            mpf(10) ** -25 * abs(delta1(a, kappa)) + mpf(10) ** -30
        ), (a, kappa)
print("OK    eq. (5.7) MD(M_0,M_1^(kappa)) rebuilt from the section 3 entries,")
print("      and Delta_1^(kappa) = S_0 S_1 MD(M_0,M_1^(kappa)); kappa = 1 is eq. (5.2)")

print("\nCONCLUSION (scope): on the tested a-ladder and for the tested kappa, the data are")
print("consistent with { kappa : Delta_1^(kappa)(a) > 0 for all a > 0 } = [1, inf).")
print("Check (2) samples finitely many a and check (3) reaches kappa = 0.999999, so the")
print("set identity is exhibited here, not proved; it is proved in the paper from")
print("eq. (5.2) and eq. (4.2).  The degree-one sign does not by itself yield positivity")
print("of the higher coefficients -- that is the endpoint argument of sec:determinant.")
print("ALL PASS")
