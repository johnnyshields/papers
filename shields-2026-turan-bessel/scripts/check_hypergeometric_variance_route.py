#!/usr/bin/env python3
r"""Targeted probe, sec:scaling (lem:central-moments, eq:hypergeom-moments): the two
binomial identities the exact variance of the symmetric hypergeometric law is
assembled from.

verify_critical_scaling.py already checks the moments themselves, and
check_tilted_tail.py uses the variance downstream.  What neither checks is the
route: the closed form n^2/(4(2n-1)) is quoted, not derived, and a derivation of it
rests on two exact statements about a row of Pascal's triangle.  They are the steps,
in exact integer arithmetic:

  * sum_k k^2 C(n,k)^2 = n^2 C(2n-2, n-1), which is k C(n,k) = n C(n-1,k-1) squared
    termwise and then Chu-Vandermonde on the shifted row.  This is the only place
    the second moment comes from;
  * n C(2n,n) = 2(2n-1) C(2n-2, n-1), the ratio of consecutive central binomials,
    which is what turns that into a closed form;
  * and the two they sit beside -- sum_k C(n,k)^2 = C(2n,n), and the first moment
    sum_k k C(n,k)^2 = (n/2) C(2n,n), which follows from the reflection k -> n-k
    rather than from a second Vandermonde.

Together they give E K = n/2, E K^2 = n^3/(2(2n-1)) and Var K = n^2/(4(2n-1)), each
checked here against the law summed term by term.  Exact rationals throughout: the
variance is a difference of two quantities that agree to leading order, so a float
route would lose the answer at large n.
"""
from __future__ import annotations
from fractions import Fraction
from math import comb

NMAX = 60

# ------------------------------------------------------------ the two route steps
for n in range(1, NMAX + 1):
    lhs = sum(k**2 * comb(n, k)**2 for k in range(n + 1))
    rhs = n**2 * comb(2*n - 2, n - 1)
    assert lhs == rhs, (n, lhs, rhs)
print(f'PASS: sum_k k^2 C(n,k)^2 = n^2 C(2n-2,n-1) for every 1 <= n <= {NMAX}')

for n in range(1, NMAX + 1):
    assert n * comb(2*n, n) == 2*(2*n - 1) * comb(2*n - 2, n - 1), n
print(f'PASS: n C(2n,n) = 2(2n-1) C(2n-2,n-1) for every 1 <= n <= {NMAX}')

# the termwise identity the first step is built on
for n in range(1, NMAX + 1):
    for k in range(1, n + 1):
        assert k * comb(n, k) == n * comb(n - 1, k - 1), (n, k)
print('PASS: k C(n,k) = n C(n-1,k-1) termwise, the shift the first step squares')

# ------------------------------------------------------- the neighboring identities
for n in range(0, NMAX + 1):
    assert sum(comb(n, k)**2 for k in range(n + 1)) == comb(2*n, n), n
print(f'PASS: sum_k C(n,k)^2 = C(2n,n) (Chu-Vandermonde) for every 0 <= n <= {NMAX}')

for n in range(0, NMAX + 1):
    assert 2 * sum(k * comb(n, k)**2 for k in range(n + 1)) == n * comb(2*n, n), n
print('PASS: 2 sum_k k C(n,k)^2 = n C(2n,n), so the first moment is n/2 by reflection')

# ------------------------------------------------------------------ the moments
for n in range(1, NMAX + 1):
    denom = comb(2*n, n)
    w = [Fraction(comb(n, k)**2, denom) for k in range(n + 1)]
    assert sum(w) == 1, n
    mean = sum(k * wk for k, wk in enumerate(w))
    assert mean == Fraction(n, 2), (n, mean)
    second = sum(k**2 * wk for k, wk in enumerate(w))
    assert second == Fraction(n**3, 2*(2*n - 1)), (n, second)
    var = sum((Fraction(k) - Fraction(n, 2))**2 * wk for k, wk in enumerate(w))
    assert var == Fraction(n**2, 4*(2*n - 1)), (n, var)
    # the paper's normalization, X = (K - n/2)/sqrt(n)
    assert var / n == Fraction(n, 4*(2*n - 1)), n
print(f'PASS: the law sums to 1 with E K = n/2, E K^2 = n^3/(2(2n-1)) and')
print(f'      Var K = n^2/(4(2n-1)) for every 1 <= n <= {NMAX}, so eq:hypergeom-moments')
print('      E_0 X^2 = n/(4(2n-1)) holds exactly, not just asymptotically')

# the variance is a near-cancellation, which is why this is exact arithmetic
n = NMAX
lead = Fraction(n**3, 2*(2*n - 1))
assert abs(lead - Fraction(n**2, 4)) * 4*(2*n - 1) == Fraction(n**2), n
print('PASS: E K^2 and (E K)^2 agree to relative order 1/n, so the variance is a')
print('      cancellation of two quantities of size n^2 down to one of size n/8 --')
print('      the reason the route is carried in exact rationals')

print('ALL PASS')
