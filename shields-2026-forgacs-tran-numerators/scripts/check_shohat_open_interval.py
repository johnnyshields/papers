#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `rem:quadratic-case`: the open-interval form of
Shohat's count.

The remark reads the count off the cited lemma of `Duran2026LinearCombinations`,
which places the guaranteed sign changes in the CLOSED convex hull of the
support, and then concedes the two endpoints to reach `I_{Q,1}`.  The
formalization in `lean/ForgacsTran/QuasiOrthogonalZeros.lean` proves the count
directly in the OPEN interval -- its sign argument never touches an endpoint --
which drops the concession and sharpens the defect from K+2 to K.

That is a claim STRONGER than the paper's, so it is checked here rather than
asserted.  The strengthening is not free: it uses that the weight is strictly
positive throughout the open interval, which the cited lemma does not assume.

  (S1) For a range of weights B and denominators, every F_M with M >= K = deg B
       has at least M-K distinct real zeros of odd multiplicity strictly inside
       I_{Q,1}, and hence at most K zeros elsewhere counted with multiplicity.
  (S2) An adversarial sweep over B: the endpoint-adjacent coefficient is tuned
       across a grid, so that if any weight could push an extra zero out of the
       open interval the sweep would find it.
  (S3) A weight tuned so that F_M vanishes EXACTLY at the upper endpoint.  That
       zero lies outside the open interval and inside the closed one, so it is
       precisely the configuration the paper's endpoint concession exists for.
       The open-interval count must still hold, with that zero charged to the
       budget of K.

Zero locations use mpmath at high precision.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 60

PASSES = 0
SEP = mp.mpf(10) ** -40


def ok(msg):
    global PASSES
    PASSES += 1
    print(f'PASS  {msg}')


def F_coeffs(b, c0, c1, c2, Mmax):
    """F_M = [t^M] B/(q0+q1 t+q2 t^2+z t) as a list of mpmath coefficient lists.

    Each entry is the coefficient list of F_M in z, lowest degree first, built
    from the exact denominator recurrence q0 F_M + (z+q1) F_{M-1} + q2 F_{M-2}
    = b_M.  Polynomials in z are carried as coefficient lists so no symbolic
    algebra is needed at this precision.
    """
    F = []
    for m in range(Mmax + 1):
        rhs = [b[m] if m < len(b) else mp.mpf(0)]
        if m >= 1:
            prev = F[m - 1]
            # -(z + q1) * F_{m-1}
            acc = [mp.mpf(0)] * (len(prev) + 1)
            for i, cf in enumerate(prev):
                acc[i + 1] -= cf
                acc[i] -= c1 * cf
            rhs = [x + y for x, y in zip(rhs + [mp.mpf(0)] * (len(acc) - len(rhs)), acc)]
        if m >= 2:
            prev2 = F[m - 2]
            acc = [-c2 * cf for cf in prev2]
            n = max(len(rhs), len(acc))
            rhs = [(rhs[i] if i < len(rhs) else mp.mpf(0))
                   + (acc[i] if i < len(acc) else mp.mpf(0)) for i in range(n)]
        F.append([x / c0 for x in rhs])
    return F


def zeros(coeffs):
    """Zeros with multiplicity of a polynomial given lowest-degree-first."""
    deg = len(coeffs) - 1
    while deg > 0 and abs(coeffs[deg]) < SEP:
        deg -= 1
    if deg == 0:
        return []
    return mp.polyroots(list(reversed(coeffs[:deg + 1])), maxsteps=8000, extraprec=1200)


def outside_open(rts, lo, hi):
    """Zeros not strictly inside (lo,hi), counted with multiplicity."""
    n = 0
    for w in rts:
        if abs(mp.im(w)) > SEP or not (lo < mp.re(w) < hi):
            n += 1
    return n


def distinct_inside(rts, lo, hi):
    """Distinct real zeros strictly inside (lo,hi)."""
    seen = []
    for w in rts:
        if abs(mp.im(w)) > SEP:
            continue
        x = mp.re(w)
        if not (lo < x < hi):
            continue
        if all(abs(x - y) > mp.mpf('1e-25') for y in seen):
            seen.append(x)
    return len(seen)


CFG = [(mp.mpf(1), mp.mpf(-3) / 2, mp.mpf(1) / 2),
       (mp.mpf(1), mp.mpf(-5) / 4, mp.mpf(1) / 4),
       (mp.mpf(2), mp.mpf(-3), mp.mpf(1))]

BS = [[mp.mpf(1)],
      [mp.mpf(1), mp.mpf(2)],
      [mp.mpf(3), mp.mpf(-1), mp.mpf(2)],
      [mp.mpf(1), mp.mpf(-5), mp.mpf(1), mp.mpf(-2)],
      [mp.mpf(2), mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(1)],
      [mp.mpf(1), mp.mpf(-7), mp.mpf(11)]]

MMAX = 16

# ---------------------------------------------------------------- (S1)
worst = 0
for b in BS:
    K = len(b) - 1
    assert b[0] != 0 and b[K] != 0
    for (c0, c1, c2) in CFG:
        lo = -c1 - 2 * mp.sqrt(c0 * c2)
        hi = -c1 + 2 * mp.sqrt(c0 * c2)
        F = F_coeffs(b, c0, c1, c2, MMAX)
        for M in range(K, MMAX + 1):
            rts = zeros(F[M])
            assert len(rts) == M, (b, M, len(rts))
            out = outside_open(rts, lo, hi)
            ins = distinct_inside(rts, lo, hi)
            assert out <= K, ('S1 outside', b, float(c1), M, out, K)
            assert ins >= M - K, ('S1 inside', b, float(c1), M, ins, M - K)
            worst = max(worst, out)
ok(f'(S1) over {len(BS)} weights, {len(CFG)} denominators and M <= {MMAX}: at least M-K '
   f'distinct real zeros of F_M strictly inside I_(Q,1), hence at most K outside the OPEN '
   f'interval counted with multiplicity (worst observed {worst})')

# ---------------------------------------------------------------- (S2)
c0, c1, c2 = CFG[0]
lo = -c1 - 2 * mp.sqrt(c0 * c2)
hi = -c1 + 2 * mp.sqrt(c0 * c2)
worst2, tried = 0, 0
for num in range(-40, 41):
    lam = mp.mpf(num) / 4
    if lam == 0:
        continue
    b = [mp.mpf(1), lam]
    F = F_coeffs(b, c0, c1, c2, 12)
    for M in range(1, 13):
        rts = zeros(F[M])
        out = outside_open(rts, lo, hi)
        ins = distinct_inside(rts, lo, hi)
        assert out <= 1, ('S2 outside', float(lam), M, out)
        assert ins >= M - 1, ('S2 inside', float(lam), M, ins)
        worst2 = max(worst2, out)
        tried += 1
ok(f'(S2) adversarial sweep, B = 1 + lambda t over 80 values of lambda and M <= 12 '
   f'({tried} polynomials): never more than K = 1 zero outside the open interval '
   f'(worst {worst2})')

# ---------------------------------------------------------------- (S3)
# Choose lambda so that F_M(hi) = 0 at a fixed M: F_M(hi) is affine in lambda,
# so one solve places a zero exactly on the endpoint the paper's concession
# exists for.
placed = 0
for Mstar in range(2, 11):
    def Fval(lam, M=Mstar):
        F = F_coeffs([mp.mpf(1), lam], c0, c1, c2, M)
        cf = F[M]
        return mp.polyval(list(reversed(cf)), hi)
    v0, v1 = Fval(mp.mpf(0)), Fval(mp.mpf(1))
    if abs(v1 - v0) < mp.mpf('1e-30'):
        continue
    lam = -v0 / (v1 - v0)
    F = F_coeffs([mp.mpf(1), lam], c0, c1, c2, Mstar)
    assert abs(mp.polyval(list(reversed(F[Mstar])), hi)) < mp.mpf('1e-40'), Mstar
    rts = zeros(F[Mstar])
    # The endpoint zero sits within rounding of `hi`, so which side of the
    # strict comparison it lands on is not decidable at this precision.  Charge
    # it to the OUTSIDE, which is the reading that makes the assertion hardest:
    # the margin below moves every near-endpoint root out of the open interval.
    marg = mp.mpf('1e-30')
    assert min(abs(mp.re(w) - hi) for w in rts) < marg, ('S3 no endpoint root', Mstar)
    out = outside_open(rts, lo + marg, hi - marg)
    ins = distinct_inside(rts, lo + marg, hi - marg)
    assert out <= 1, ('S3 outside', Mstar, out)
    assert out == 1, ('S3 endpoint uncharged', Mstar, out)
    assert ins >= Mstar - 1, ('S3 inside', Mstar, ins, Mstar - 1)
    placed += 1
assert placed >= 8, placed
ok(f'(S3) with lambda solved so that F_M vanishes exactly at the upper endpoint '
   f'({placed} indices M): the endpoint zero is the single zero outside the open interval '
   f'and the remaining M-1 are strictly inside -- the concession case, and the count '
   f'K = 1 still holds')

print(f'\n{PASSES} checks')
print('ALL PASS: check_shohat_open_interval')
