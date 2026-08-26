#!/usr/bin/env python3
r"""Paper section `sec:reduction` (Canonical Laurent reduction and eventual degree).

Dependency-free audit of the coefficient recurrence.

Uses only the standard-library `fractions` module -- no SymPy, no mpmath.  A
polynomial in z is an exact list of Fraction coefficients (index = power of z),
and the coefficients P_m(z) of N(t,z)/(Q(t)+z t^r) are built from the exact
recurrence
        sum_{j>=0} d_j(z) P_{m-j}(z) = N_m(z),   d_0 = Q(0),
with d_j the t^j-coefficient of Q(t)+z t^r.  This re-derives, without any CAS:

  * `prop:initial-data`: N |-> (P_0,...,P_{d-1}) is lower triangular with constant
    diagonal Q(0) and determinant Q(0)^d != 0, hence a bijection onto Q[z]^d.
    Checked by prescribing polynomial initial data, mapping it forward to a
    numerator, and recovering it through the recurrence itself -- at r < d, so
    d_r = q_r + z genuinely carries z.
  * `lem:eventual-degree`, `eq:eventual-degree`: deg_z F_M = floor(M/r), at r = 2 and r = 3.
  * `prop:linear-case` (linear case): P_m(z) = (-1)^m R(z)(z+q_1)^m / q_0^{m+1}.
"""
from fractions import Fraction as Fr


# --- exact polynomials in z as Fraction coefficient lists (index = power) ------
def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else Fr(0)) + (b[i] if i < len(b) else Fr(0)) for i in range(n)]


def pscale(a, c):
    return [c * x for x in a]


def pshift(a):                                                     # multiply by z
    return [Fr(0)] + list(a)


def ptrim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def pdeg(a):
    a = ptrim(a)
    return -1 if (len(a) == 1 and a[0] == 0) else len(a) - 1


def peq(a, b):
    return ptrim(a) == ptrim(b)


def coeff_polys(Qt, Nz, r, Mmax):
    r"""P_0..P_Mmax for (sum_m Nz[m] z-poly) / (Qt(t) + z t^r).

    The exact coefficient recurrence sum_j d_j(z) P_{m-j} = N_m, d_0 = Q(0) (`eq:P-generating-intro`,
    `prop:initial-data`), carried out over Q[z] with Fraction arithmetic -- no CAS.
    Qt: list of Fraction t-coefficients of Q (index = power of t), Qt[0] != 0.
    Nz: list (index = power of t) of z-polynomials (each a Fraction list), the numerator.
    """
    q0 = Qt[0]
    P = []
    for m in range(Mmax + 1):
        acc = list(Nz[m]) if m < len(Nz) else [Fr(0)]
        for i in range(1, len(Qt)):
            if m - i >= 0:
                acc = padd(acc, pscale(P[m - i], -Qt[i]))
        if m - r >= 0:
            acc = padd(acc, pscale(pshift(P[m - r]), Fr(-1)))
        P.append(ptrim(pscale(acc, Fr(1) / q0)))
    return P


# ===========================================================================
# `prop:initial-data`: N |-> (P_0,...,P_{d-1}) is a bijection onto Q[z]^d
# ===========================================================================
# The test must run through coeff_polys, the recurrence the proposition is about: a
# hand-inversion of the same triangular system would pass on arbitrary data no matter what
# the rest of the file did.  And it must take r < d, since r = d puts the z-carrying
# coefficient d_r outside the indices 0..d-1, leaving nothing of the Q[z] content.
#
# So: deg Q = 3 and r = 2, giving d = 3 and d_2 = q_2 + z; the initial data are POLYNOMIALS
# in z; the numerator is built by `prop:initial-data`'s forward map; and that numerator is fed through
# coeff_polys, whose first d outputs must return the prescribed data.  That is the
# surjectivity half onto Q[z]^d, closed through the real recurrence.
Qt = [Fr(1), Fr(-3), Fr(2), Fr(-1)]                                # Q = 1 - 3t + 2t^2 - t^3
r, d = 2, 3
assert d == max(len(Qt) - 1, r) and r < d                          # z enters the triangular block


def dj_times(j, P):
    r"""d_j(z) * P where d_j(z) = Q.coeff(j) + [j == r] z."""
    out = pscale(P, Qt[j] if j < len(Qt) else Fr(0))
    return padd(out, pshift(P)) if j == r else out


# arbitrary PRESCRIBED polynomial initial data (P_0, P_1, P_2) in Q[z]
Pgiven = [[Fr(2), Fr(0), Fr(1, 3)],                                # 2 + z^2/3
          [Fr(-5), Fr(7, 2)],                                      # -5 + 7z/2
          [Fr(11, 3), Fr(0), Fr(-1), Fr(4)]]                       # 11/3 - z^2 + 4z^3
# forward map of `prop:initial-data`: N_m = sum_{j=0}^{m} d_j(z) P_{m-j},  0 <= m < d
Nz = []
for m in range(d):
    acc = [Fr(0)]
    for j in range(m + 1):
        acc = padd(acc, dj_times(j, Pgiven[m - j]))
    Nz.append(ptrim(acc))

# z really is carried by d_r: dropping it from the forward map changes N_r
Nz_zfree = []
for m in range(d):
    acc = [Fr(0)]
    for j in range(m + 1):
        acc = padd(acc, pscale(Pgiven[m - j], Qt[j] if j < len(Qt) else Fr(0)))
    Nz_zfree.append(ptrim(acc))
assert not peq(Nz[r], Nz_zfree[r]), 'd_r = q_2 + z did not affect N_r'
assert peq(Nz[0], Nz_zfree[0]), 'd_0 should be z-free'

# feed that numerator through the actual recurrence and recover the prescribed data
Pback = coeff_polys(Qt, Nz, r, d + 4)
for m in range(d):
    assert peq(Pback[m], Pgiven[m]), (m, Pback[m], Pgiven[m])
# the map is injective too: perturbing one coefficient of N changes (P_0,..,P_{d-1})
Nz_p = [list(x) for x in Nz]
Nz_p[1] = padd(Nz_p[1], [Fr(1, 7)])
Pp = coeff_polys(Qt, Nz_p, r, d + 4)
assert not peq(Pp[1], Pgiven[1]), 'perturbing N_1 left P_1 unchanged'
assert peq(Pp[0], Pgiven[0]), 'perturbing N_1 should not touch P_0 (lower triangular)'

# the triangular structure itself: entry (i,j) is d_{i-j} for i >= j and 0 otherwise, and
# the diagonal is the constant d_0 = Q(0) -- z-free, hence a unit of Q[z]
for i in range(d):
    for j in range(d):
        ent = dj_times(i - j, [Fr(1)]) if i >= j else [Fr(0)]
        if i == j:
            assert peq(ent, [Qt[0]]), (i, j, ent)                  # constant diagonal Q(0)
            assert pdeg(ent) == 0                                  # z-free, so a unit
assert Qt[0] != 0
print(f'PASS: `prop:initial-data` through the recurrence: prescribed (P_0,P_1,P_2) in Q[z] recovered '
      f'from N = forward-map(P) via coeff_polys (deg_z N_2 = {pdeg(Nz[2])}, r={r} < d={d} so '
      f'd_r = q_2 + z carries z, shown by comparison against the z-free map); diagonal is '
      f'the constant Q(0)={Qt[0]}, det = Q(0)^{d}; '
      f'perturbing N_1 moves P_1 but not P_0')


# ===========================================================================
# `lem:eventual-degree`, `eq:eventual-degree`: deg_z F_M = floor(M/r)
# ===========================================================================
def Bnum(Bt, Mmax):                                                # univariate B(t) as numerator
    return [[c] for c in Bt] + [[Fr(0)]] * (Mmax + 1)


for (Qt, r, Bt, Mtop) in [
    ([Fr(1), Fr(-6), Fr(11), Fr(-6)], 2, [Fr(1), Fr(2), Fr(1)], 40),   # Q=(1-t)(1-2t)(1-3t)
    ([Fr(1), Fr(-2), Fr(1), Fr(-4), Fr(4)], 3, [Fr(2), Fr(-1), Fr(3)], 45),  # deg Q=4
]:
    F = coeff_polys(Qt, Bnum(Bt, Mtop), r, Mtop)
    bad = [m for m in range(Mtop + 1) if pdeg(F[m]) != m // r]
    # The law is asserted directly.  Reading the threshold off the failures instead --
    # last_bad = max(bad), then asserting only above it -- is a tautology: that range
    # excludes every failure by construction, so it passes on a degree list wrong at
    # every index.
    assert not bad, (r, bad)                                        # `eq:eventual-degree`, every M
    print(f'PASS: deg_z F_M = floor(M/r) for every M in [0,{Mtop}]  (r={r})')


# ===========================================================================
# `prop:linear-case` (linear case): P_m = (-1)^m R(z)(z+q_1)^m / q_0^{m+1}
# ===========================================================================
q0, q1 = Fr(3, 1), Fr(-5, 2)                                       # q_0 > 0, q_1 < 0
Rz = [Fr(1), Fr(1), Fr(0), Fr(1)]                                  # R(z) = 1 + z + z^3
Nz = [Rz]                                                          # N(t,z) = R(z) (deg_t 0)
P = coeff_polys([q0, q1], Nz, 1, 7)
for m in range(8):
    zpq1 = [Fr(1)]                                                 # (z + q_1)^m
    for _ in range(m):
        zpq1 = padd(pshift(zpq1), pscale(zpq1, q1))                # multiply by (z + q_1)
    conv = [Fr(0)] * (len(Rz) + len(zpq1) - 1)                     # R(z) * (z+q_1)^m
    for i, a in enumerate(Rz):
        for j, b in enumerate(zpq1):
            conv[i + j] += a * b
    closed = pscale(conv, Fr((-1)**m) / q0**(m + 1))               # (-1)^m R (z+q_1)^m / q_0^{m+1}
    assert peq(P[m], closed), m
print('PASS: linear case P_m = (-1)^m R(z)(z+q_1)^m / q_0^{m+1} (exact, fractions only)')

print('ALL PASS: check_recurrence_stdlib')
