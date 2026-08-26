#!/usr/bin/env python3
r"""Paper section `sec:reduction` (Canonical Laurent reduction and eventual degree),
`eq:denominator-coordinate-ring` and `lem:laurent-reduction`.

The reduction is intrinsic: N is restricted to the denominator curve rather than
cleared of Laurent denominators, so the index shift is a single integer, the
Laurent valuation lambda_N.  Every
claim here is exact rational/symbolic arithmetic.

  (R1) eq:denominator-coordinate-ring.  In R[t,z]/(D), t is a unit: the paper's
       witness 1 = t * (-(Q_1(t) + z t^{r-1})/Q(0)) is verified as an identity
       modulo D, with Q = Q(0) + t Q_1.  Surjectivity onto R[t,t^-1] is
       exhibited constructively -- t^{-1} is written as a POLYNOMIAL in t and
       g(t), namely t^{-1} = -(t^{r-1} g(t) + (Q(t)-Q(0))/t)/Q(0) -- and the
       kernel is (D) by Gauss: D is primitive in R[t][z] because Q(0) != 0
       makes t coprime to Q, so a quotient with Laurent denominators cannot
       occur.  The primitivity is checked as gcd(Q, t^r) = 1.
  (R2) eq:canonical-Laurent-factorization.  L_N = N(t, g(t)) is a nonzero Laurent
       polynomial, and the factorization
       L_N = t^{lambda_N} B_N with B_N(0) != 0 exists and is unique.
  (R3) eq:canonical-Laurent-division: N = D S_N + t^{lambda_N} B_N exactly,
       with S_N in R[t,t^-1,z].  Verified as a symbolic identity in (t,z).
  (R4) eq:reduction-threshold: the top t-exponent of S_N is STRICTLY below
       E max{q-r,0}, which is what makes eq:reduction-coeff hold from that
       index on.  The bound is also shown ATTAINED, so it is sharp and not
       merely safe.
  (R5) eq:reduced-degree-complexity: deg B_N <= p_N + E_N max{q,r}, the paper's
       names for deg_t N and deg_z N (p and E below are the local variables).
  (R6) eq:reduction-coeff: P_m = [t^{m-lambda_N}] B_N/D for every m at or above
       the threshold, against P_m from the coefficient recurrence -- and, where
       the threshold is positive, shown to FAIL below it, so the threshold is
       load-bearing rather than defensive.
  (R7) eq:exact-eventual-degree-shift: deg P_m = floor((m - lambda_N)/r)
       eventually, the exact formula replacing m/r + O(1).

A randomized sweep over small (q, r, E, p) closes the section.
"""

import random
import sympy as sp

t, z = sp.symbols('t z')


def ok(msg):
    print('  ' + msg)


def curve_map(Q, r):
    """g(t) = -Q(t)/t^r, the parameterization of D = 0."""
    return -sp.expand(Q) / t**r


def _clear(expr, gens):
    """Multiply by the least t^K making expr polynomial; return (K, poly)."""
    e = sp.expand(sp.cancel(sp.together(sp.expand(expr))))
    for K in range(0, 200):
        cand = sp.expand(sp.cancel(sp.together(e * t**K)))
        if cand.is_polynomial(*gens):
            return K, sp.Poly(cand, *gens)
    raise AssertionError('could not clear denominators: %s' % expr)


def laurent_parts(expr):
    """Write a Laurent polynomial in t as (valuation, polynomial)."""
    K, P = _clear(expr, (t,))
    low = min(m[0] for m in P.monoms())
    B = sp.expand(sp.cancel(P.as_expr() / t**low))
    return low - K, B


def canonical(N, Q, r):
    g = curve_map(Q, r)
    L = sp.cancel(sp.together(sp.expand(N.subs(z, g))))
    assert sp.simplify(L) != 0, 'L_N vanished'
    lam, B = laurent_parts(L)
    assert sp.simplify(sp.expand(B).subs(t, 0)) != 0, (B, 'B_N(0) = 0')
    return lam, sp.expand(B), L


def quotient(N, Q, r, lam, B):
    """S_N with N = D S_N + t^lam B, exact."""
    D = sp.expand(Q + z * t**r)
    S = sp.cancel(sp.together(sp.expand(N - t**lam * B) / D))
    assert sp.simplify(sp.expand(D * S + t**lam * B - N)) == 0, 'division failed'
    return sp.expand(S)


def top_t_exponent(S):
    """Largest t-exponent in a Laurent polynomial in t over R[z]."""
    if sp.simplify(S) == 0:
        return -sp.oo
    K, P = _clear(S, (t, z))
    return max(m[0] for m in P.monoms()) - K


def coeff_polys(num, den, M):
    dp = sp.Poly(den, t)
    d = [sp.expand(dp.coeff_monomial(t**j)) for j in range(dp.degree() + 1)]
    npn = sp.Poly(num, t)
    Nc = [sp.expand(npn.coeff_monomial(t**j)) for j in range(npn.degree() + 1)]
    P = []
    for m in range(M + 1):
        rhs = Nc[m] if m < len(Nc) else sp.Integer(0)
        acc = sum(d[j] * P[m - j] for j in range(1, min(m, len(d) - 1) + 1))
        P.append(sp.expand(sp.cancel((rhs - acc) / d[0])))
    return P


def series_coeff(B, Q, r, upto):
    """[t^k] B/D for k = 0..upto, exactly, via the same recurrence."""
    return coeff_polys(sp.expand(B), sp.expand(Q + z * t**r), upto)


# ---------------------------------------------------------------------------
print('=' * 78)
print('R1: the denominator curve is G_m -- R[t,z]/(D) = R[t,t^-1]')
print('=' * 78)
for Q, r in [(1 - t, 1), ((1 - t) * (1 - t / 2), 2), (1 - 3 * t + 2 * t**2, 3),
             (sp.Integer(2) - t, 1), ((1 - t)**3, 2)]:
    Q = sp.expand(Q)
    q0 = Q.subs(t, 0)
    Q1 = sp.expand(sp.cancel((Q - q0) / t))
    D = sp.expand(Q + z * t**r)
    # t is a unit mod D: 1 - t*(-(Q1 + z t^{r-1})/q0) must be a multiple of D
    wit = -(Q1 + z * t**(r - 1)) / q0
    rem = sp.simplify(sp.cancel((1 - t * wit) / D))
    assert sp.simplify(sp.expand(1 - t * wit - D * rem)) == 0 and rem.is_constant(), (Q, r, rem)
    # surjectivity: t^{-1} as a polynomial in t and g(t)
    g = curve_map(Q, r)
    expr = -(t**(r - 1) * g + sp.cancel((Q - q0) / t)) / q0
    assert sp.simplify(sp.expand(sp.cancel(expr - 1 / t))) == 0, (Q, r, sp.simplify(expr))
    # primitivity of D in R[t][z]: gcd(Q, t^r) = 1 because Q(0) != 0
    assert sp.gcd(Q, t**r) == 1 and q0 != 0, (Q, r)
    ok(f'Q={Q}, r={r}: t is a unit mod D (1 - t*w = {rem}*D), '
       f't^-1 lies in R[t, g(t)], and gcd(Q, t^r) = 1 so D is primitive')
ok('so the substitution z -> g(t) is onto R[t,t^-1] with kernel exactly (D)')

# ---------------------------------------------------------------------------
print()
print('=' * 78)
print('R2-R7: canonical reduction on named instances')
print('=' * 78)
CASES = [
    (sp.Integer(1), (1 - t) * (1 - t / 2), 1, 'N = 1'),
    (1 + z * t, (1 - t) * (1 - t / 2), 1, 'N carries z, deg Q > r'),
    (1 + z + z**2 * t, (1 - t) * (1 - t / 2) * (1 - t / 3), 1, 'E = 2, q = 3 > r = 1'),
    (1 + z * t**2, (1 - t), 3, 'q = 1 < r = 3'),
    (2 - t + z * (1 + t), (1 - t) * (1 - t / 4), 2, 'q = r = 2'),
    (7 * t**2 + 8, (1 - t) * (1 - t / 2) * (1 - t / 4), 1, "the paper's figure numerator"),
]
for N, Q, r, tag in CASES:
    N, Q = sp.expand(N), sp.expand(Q)
    q = sp.Poly(Q, t).degree()
    p = sp.Poly(N, t).degree() if N.has(t) else 0
    E = sp.Poly(N, z).degree() if N.has(z) else 0
    d = max(q, r)
    assert p < d, (tag, 'N not proper')
    lam, B, L = canonical(N, Q, r)
    S = quotient(N, Q, r, lam, B)
    thr = E * max(q - r, 0)
    topS = top_t_exponent(S)
    assert topS < thr or S == 0, (tag, topS, thr)
    assert sp.Poly(B, t).degree() <= p + E * max(q, r), (tag, sp.Poly(B, t).degree())
    # R6: P_m against [t^{m-lam}] B/D
    M = 22
    P = coeff_polys(N, sp.expand(Q + z * t**r), M)
    F = series_coeff(B, Q, r, M + abs(lam) + 4)
    good = [m for m in range(max(thr, 0), M + 1)
            if sp.simplify(sp.expand(P[m] - (F[m - lam] if 0 <= m - lam < len(F) else 0))) == 0]
    assert good == list(range(max(thr, 0), M + 1)), (tag, 'reduction fails at or above threshold')
    # R7: exact degree formula
    degs_ok = all(sp.Poly(P[m], z).degree() == (m - lam) // r
                  for m in range(max(thr, 0) + 2 * r + 2, M + 1) if P[m] != 0)
    assert degs_ok, (tag, 'exact degree formula fails')
    sh = f'm - {lam}' if lam >= 0 else f'm + {-lam}'
    ok(f'{tag}: lambda_N = {lam}, deg B_N = {sp.Poly(B,t).degree()} '
       f'(bound {p + E*max(q,r)}), top exp of S_N = {topS} < threshold {thr}; '
       f'P_m = [t^({sh})] B_N/D for every m in [{max(thr,0)}, {M}]; '
       f'deg P_m = floor(({sh})/{r}) exactly')

# threshold sharpness: below it the reduction genuinely fails somewhere
sharp = 0
for N, Q, r, tag in CASES:
    N, Q = sp.expand(N), sp.expand(Q)
    q = sp.Poly(Q, t).degree(); E = sp.Poly(N, z).degree() if N.has(z) else 0
    thr = E * max(q - r, 0)
    if thr == 0:
        continue
    lam, B, _ = canonical(N, Q, r)
    P = coeff_polys(N, sp.expand(Q + z * t**r), 22)
    F = series_coeff(B, Q, r, 26 + abs(lam))
    bad = [m for m in range(0, thr)
           if sp.simplify(sp.expand(P[m] - (F[m - lam] if 0 <= m - lam < len(F) else 0))) != 0]
    if bad:
        sharp += 1
        ok(f'{tag}: and the reduction FAILS at m = {bad}, all below the '
           f'threshold {thr} -- so eq:reduction-threshold is load-bearing')
assert sharp > 0, 'no instance exhibited a genuine transient'

# ---------------------------------------------------------------------------
print()
print('=' * 78)
print('R2-R7: randomized sweep')
print('=' * 78)
random.seed(20260822)
tested = 0
for _ in range(140):
    q = random.randint(1, 4)
    r = random.randint(1, 4)
    if max(q, r) <= 1:
        continue
    xs = [sp.Rational(random.randint(1, 6), random.randint(1, 3)) for _ in range(q)]
    Q = sp.expand(sp.prod([1 - t / x for x in xs]))
    if sp.Poly(Q, t).degree() != q:
        continue
    d = max(q, r)
    p = random.randint(0, d - 1)
    E = random.randint(0, 3)
    N = sp.expand(sum(sp.Integer(random.randint(-4, 4)) * t**random.randint(0, p) * z**b
                      for b in range(E + 1)) + sp.Integer(random.choice([1, -1, 2])) * z**E * t**p)
    if N == 0 or sp.Poly(N, t).degree() >= d:
        continue
    E = sp.Poly(N, z).degree() if N.has(z) else 0
    p = sp.Poly(N, t).degree() if N.has(t) else 0
    try:
        lam, B, _ = canonical(N, Q, r)
    except AssertionError:
        continue
    S = quotient(N, Q, r, lam, B)
    thr = E * max(q - r, 0)
    topS = top_t_exponent(S)
    assert topS < thr or S == 0, (N, Q, r, topS, thr)
    assert sp.Poly(B, t).degree() <= p + E * max(q, r), (N, Q, r)
    M = max(thr, 0) + 3 * r + 4
    P = coeff_polys(N, sp.expand(Q + z * t**r), M)
    F = series_coeff(B, Q, r, M + abs(lam) + 4)
    for m in range(max(thr, 0), M + 1):
        assert sp.simplify(sp.expand(P[m] - (F[m - lam] if 0 <= m - lam < len(F) else 0))) == 0, \
            (N, Q, r, m)
    for m in range(max(thr, 0) + 2 * r + 2, M + 1):
        if P[m] != 0:
            assert sp.Poly(P[m], z).degree() == (m - lam) // r, (N, Q, r, m)
    tested += 1
assert tested >= 60, tested
ok(f'{tested} randomized instances over 1 <= q,r <= 4, 0 <= E <= 3: '
   'the division, the threshold, the degree bound, eq:reduction-coeff and the '
   'exact degree formula all hold with no exception')

print()
print('=' * 78)
print('R8: the tail-shift equivalence -- lambda_N shifts, B_N carries the geometry')
print('=' * 78)
# If L_{N_2} = c t^s L_{N_1} then P_m^{(2)} = c P_{m-s}^{(1)} eventually.  This is
# what makes the paper's three-level reading exact: lambda_N is an index shift,
# and the zero geometry of the tail is B_N's up to a scalar.
for N1, Q, r_, c, sft, tag in [
        (sp.Integer(1),            (1 - t) * (1 - t / 2), 1, sp.Integer(3),  2, 'N=1, c=3, s=2'),
        (1 + z * t,                (1 - t) * (1 - t / 2), 1, sp.Rational(-1, 2), 1, 'N carries z, c=-1/2, s=1'),
        (7 * t**2 + 8, (1 - t) * (1 - t / 2) * (1 - t / 4), 1, sp.Integer(2), 3, 'figure numerator, c=2, s=3'),
]:
    Q, N1 = sp.expand(Q), sp.expand(N1)
    lam1, B1, _ = canonical(N1, Q, r_)
    # build N2 with L_{N2} = c t^s L_{N1}: take N2 = c t^s N1 -- proper only if the
    # t-degree still fits, so drop back to a z-free multiple when it does not
    N2 = sp.expand(c * t**sft * N1)
    d = max(sp.Poly(Q, t).degree(), r_)
    if sp.Poly(N2, t).degree() >= d:
        # reduce N2 modulo D to a proper representative; the coefficient sequence
        # is unchanged because D | (N2 - N2 mod D) contributes nothing to P_m
        N2 = sp.expand(sp.rem(sp.Poly(N2, t), sp.Poly(sp.expand(Q + z * t**r_), t)).as_expr())
    lam2, B2, _ = canonical(N2, Q, r_)
    assert lam2 == lam1 + sft, (tag, lam1, lam2, sft)
    assert sp.simplify(sp.expand(B2 - c * B1)) == 0, (tag, B2, c * B1)
    M = 26
    P1 = coeff_polys(N1, sp.expand(Q + z * t**r_), M)
    P2 = coeff_polys(N2, sp.expand(Q + z * t**r_), M)
    lo = max(sft, 6)
    for m in range(lo, M + 1):
        assert sp.simplify(sp.expand(P2[m] - c * P1[m - sft])) == 0, (tag, m)
    ok(f'{tag}: lambda_(N2) = {lam2} = lambda_(N1) + s and B_(N2) = c B_(N1); '
       f'hence P_m^(2) = c P_(m-s)^(1) for every m in [{lo}, {M}]')
ok('so lambda_N is a pure index/degree shift and the tail geometry is B_N\'s, '
   'up to a nonzero scalar -- the paper\'s three-level reading of the numerator')

print()
print('=' * 78)
print('R9: `rem:canonical-bounds-sharp` -- both bounds are attained, not merely safe')
print('=' * 78)
# (a) the threshold.  For q > r and N = t^(q-1) z^E the top Laurent exponent of S_N is
# EXACTLY E(q-r)-1, one below eq:reduction-threshold, so the reduction can fail at the
# index immediately preceding it.  R4 showed the threshold is load-bearing; this shows
# it is placed at the right index and not merely somewhere safe.
for q, r_, E in [(2, 1, 1), (2, 1, 2), (3, 1, 2), (3, 2, 3), (4, 2, 2), (4, 1, 2)]:
    Q = sp.expand(sp.prod([1 - t / sp.Integer(k + 1) for k in range(q)]))
    N = sp.expand(t**(q - 1) * z**E)
    lam, B, _ = canonical(N, Q, r_)
    S = quotient(N, Q, r_, lam, B)
    thr = E * (q - r_)
    assert top_t_exponent(S) == thr - 1, (q, r_, E, top_t_exponent(S), thr)
    # and the reduction really does fail at that index
    P = coeff_polys(N, sp.expand(Q + z * t**r_), thr + 4)
    F = series_coeff(B, Q, r_, thr + 8 + abs(lam))
    bad = sp.simplify(sp.expand(P[thr - 1] - (F[thr - 1 - lam] if 0 <= thr - 1 - lam < len(F) else 0)))
    assert bad != 0, (q, r_, E, 'no failure at threshold-1')
    ok(f'q={q}, r={r_}, E={E}, N=t^(q-1)z^E: top exp of S_N = {thr-1} = threshold - 1, '
       f'and eq:reduction-coeff genuinely fails at m = {thr-1}')
# (b) the reduced-degree bound, attained in both degree regimes
for q, r_, E, p_ in [(3, 1, 2, 2), (4, 2, 1, 3), (2, 3, 2, 1), (3, 3, 2, 1), (2, 2, 2, 0)]:
    Q = sp.expand(sp.prod([1 - t / sp.Integer(k + 1) for k in range(q)]))
    N = sp.expand((1 + t**p_) * z**E) if q > r_ else sp.expand(t**p_ + sp.Integer(3) * z**E)
    assert sp.Poly(N, t).degree() < max(q, r_), (q, r_, p_)
    lam, B, _ = canonical(N, Q, r_)
    assert lam == -r_ * E, (q, r_, E, p_, lam)
    assert sp.Poly(B, t).degree() == p_ + E * max(q, r_), (q, r_, E, p_)
    ok(f'q={q}, r={r_}, E={E}, p={p_} ({"q>r" if q > r_ else "q<=r"}): lambda_N = {lam} '
       f'= -rE and deg B_N = {sp.Poly(B,t).degree()} = p_N + E_N max(q,r) exactly -- '
       f'eq:reduced-degree-complexity attained')
ok('including q = r with p = 0, where the leading terms would cancel for the wrong '
   'constant; c = 3 avoids it, which is the case the remark singles out')

print()
print('PASS: (R1) R[t,z]/(D) = R[t,t^-1]: t a unit, surjective, D primitive')
print('PASS: (R2) `eq:canonical-Laurent-factorization`: L_N != 0 and the '
      'factorization t^lambda_N B_N is unique')
print('PASS: (R3) the canonical division identity is exact')
print('PASS: (R4) top exp of S_N < E max{q-r,0}, and the threshold is attained')
print('PASS: (R5) deg B_N <= p_N + E_N max{q,r}')
print('PASS: (R6) P_m = [t^(m-lambda_N)] B_N/D at and above the threshold')
print('PASS: (R7) deg P_m = floor((m - lambda_N)/r) eventually')
print('PASS: (R8) tail-shift equivalence: L_(N2) = c t^s L_(N1) => P_m^(2) = c P_(m-s)^(1)')
print('PASS: (R9) both canonical bounds are attained, not merely safe')
print('ALL PASS: check_canonical_reduction')
