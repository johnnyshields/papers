#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `sec:geometry`.

Can the `n >= 4` clearance be had from a COEFFICIENT bound instead of the
argument principle?  BANK-39 records the `n = 3` restriction as wanting a
per-root argument, because the Vieta product constrains `n - 2` roots jointly
and cannot bound a minimum.  A coefficient bound on the deflated pencil bounds
each root directly, so it is worth asking before a Rouche development is priced.

Deflate the collision out: `S = D_b / (t - t_c)^2` at the collision point `t_c`,
whose roots are exactly the non-collision roots.  Then a lower bound on `|roots
of S|` is what the separating radius needs.

  (F1) The naive reverse-Cauchy bound `|s_0| / (|s_0| + max_{i>=1} |s_i|)` is
       NOT scale-covariant and is always below 1, so it cannot clear a collision
       radius above 1.  Measured: it clears at eight of nine pencils and fails at
       `a = (1,3,9,27,81)`, where the radius is 1.188.
  (F2) Fujiwara's bound IS scale-covariant -- `|t| >= 1 / (2 max_i (|s_i/s_0|)^(1/i))`
       -- and at the UPPER endpoint it clears at every pencil tested, including
       confluent, 1e4-aspect and `n = 6`.
  (F3) At the LOWER endpoint it FAILS, and not marginally.  So the two endpoints
       differ again in exactly the way this paper's two ends keep differing: the
       same instrument settles one and not the other.

mpmath only.  The collision radius comes from `E(t_c) = 0`; deflation is
synthetic division, applied twice, so `S` is exact rather than fitted.
"""
from mpmath import mp, mpf, mpc, findroot, polyroots, fabs

mp.dps = 40


def qcoeffs(c, a):
    poly = [mpf(c)]
    for ak in a:
        nxt = [mpf(0)] * (len(poly) + 1)
        for i, co in enumerate(poly):
            nxt[i] += co * mpf(ak)
            nxt[i + 1] -= co
        poly = nxt
    return poly[::-1]


def peval(C, t):
    v = mpc(0)
    for co in C:
        v = v * t + co
    return v


def deriv(C):
    d = len(C) - 1
    return [C[i] * (d - i) for i in range(d)] if d > 0 else [mpf(0)]


def deflate(D, root):
    """Synthetic division of D (high->low) by (t - root); returns the quotient."""
    out = [D[0]]
    for c in D[1:]:
        out.append(c + out[-1] * root)
    out.pop()
    return out


def upper_L(a, r=1):
    Q = qcoeffs(1.0, a)
    Qp = deriv(Q)
    E = lambda t: (mpc(t) * peval(Qp, mpc(t)) - r * peval(Q, mpc(t))).real
    step, x = mpf(1) / 2000, mpf(1) / 2000
    prev = E(-x)
    while x < 80:
        cur = E(-(x + step))
        if prev * cur < 0:
            return mpf(findroot(lambda u: E(-u), (x, x + step), solver='bisect',
                                tol=mpf(10)**-30))
        prev, x = cur, x + step
    return None


def lower_ta(a, r=1):
    if sum(1 for x in a if x == min(a)) > 1:
        return None
    Q = qcoeffs(1.0, a)
    Qp = deriv(Q)
    E = lambda t: (mpc(t) * peval(Qp, mpc(t)) - r * peval(Q, mpc(t))).real
    lo = mpf(min(a)) * (1 + mpf(10)**-16)
    hi = mpf(sorted(a)[1]) * (1 - mpf(10)**-16)
    if E(lo) * E(hi) > 0:
        return None
    return mpf(findroot(E, (lo, hi), solver='bisect', tol=mpf(10)**-30))


def deflated(a, tc, r=1):
    Q = qcoeffs(1.0, a)
    z = mpf((-peval(Q, mpc(tc)) / mpc(tc) ** r).real)
    D = [mpf(x) for x in Q]
    D[len(D) - 1 - r] += z
    return deflate(deflate(D, tc), tc)


def fujiwara(S):
    lo2hi = S[::-1]
    s0 = fabs(lo2hi[0])
    m = len(lo2hi) - 1
    if s0 == 0 or m == 0:
        return None
    cand = [(fabs(lo2hi[i]) / s0) ** (mpf(1) / i)
            for i in range(1, m + 1) if fabs(lo2hi[i]) > 0]
    return 1 / (2 * max(cand)) if cand else None


def rev_cauchy(S):
    s = [fabs(c) for c in S]
    s0 = s[-1]
    rest = max(s[:-1]) if len(s) > 1 else mpf(0)
    return s0 / (s0 + rest) if (s0 + rest) > 0 else mpf(0)


FAM = [[mpf(x) for x in base] for base in (
    [1, 1, 1], [1, 1.001, 1.002], [1, 1, 1.0001], [1, 1, 2], [1, 2, 3],
    [1, 1, 1, 1], [1, 1, 1, 1000], [1, 1000, 1000, 1000], [1, 1.01, 1.02, 1.03],
    [1, 2, 3, 4], [1, 1e4, 1e4, 1e4], [1, 1, 1, 1, 1],
    [1, 1.001, 1.002, 1.003, 1.004], [1, 2, 4, 8, 16], [1, 1, 1, 1, 1, 1],
    [1, 3, 9, 27, 81, 243], [0.001, 0.002, 0.003], [1, 3, 9, 27, 81])]

print("a coefficient bound on the deflated pencil, against the argument principle")
print()

# (F1) the naive reverse-Cauchy bound is not scale-covariant
rc_fail = []
for a in FAM:
    L = upper_L(a)
    if L is None:
        continue
    rc = rev_cauchy(deflated(a, -L))
    assert rc < 1, f"reverse-Cauchy returned {mp.nstr(rc,8)} >= 1, which it cannot"
    if rc <= L:
        rc_fail.append(([mp.nstr(x, 5) for x in a], L, rc))
assert rc_fail, ("reverse-Cauchy cleared every pencil here, so this sweep cannot "
                 "show that it is the wrong instrument")
print(f"PASS  (F1) the reverse-Cauchy bound is always below 1 -- it is not "
      f"scale-covariant -- and so fails whenever the collision radius exceeds 1: "
      f"{len(rc_fail)} of {len(FAM)} pencils, e.g. radius "
      f"{mp.nstr(rc_fail[0][1],6)} against bound {mp.nstr(rc_fail[0][2],6)}")

# (F2) Fujiwara clears at the upper endpoint, everywhere
up, upworst, upat = 0, None, None
for a in FAM:
    L = upper_L(a)
    if L is None:
        continue
    f = fujiwara(deflated(a, -L))
    assert f is not None
    ratio = f / L
    assert ratio > 1, (
        f"Fujiwara FAILS at the upper endpoint, a={[mp.nstr(x,5) for x in a]}: "
        f"{mp.nstr(f,8)} against L={mp.nstr(L,8)}")
    up += 1
    if upworst is None or ratio < upworst:
        upworst, upat = ratio, [mp.nstr(x, 5) for x in a]
assert up >= 15, f"only {up} pencils reached the upper endpoint"
print(f"PASS  (F2) Fujiwara's bound clears the collision radius at ALL {up} upper "
      f"pencils -- confluent, 1e4 aspect, n up to 6 -- worst ratio "
      f"{mp.nstr(upworst,8)} at a=({','.join(upat)})")

# (F3) and fails at the lower endpoint
lo, lofail, loworst, loat = 0, 0, None, None
for a in FAM:
    ta = lower_ta(a)
    if ta is None:
        continue
    f = fujiwara(deflated(a, ta))
    if f is None:
        continue
    lo += 1
    ratio = f / ta
    if ratio <= 1:
        lofail += 1
    if loworst is None or ratio < loworst:
        loworst, loat = ratio, [mp.nstr(x, 5) for x in a]
assert lo >= 5, f"only {lo} pencils reached the lower endpoint"
assert lofail > 0, (
    "Fujiwara cleared every lower pencil too, so the asymmetry this row asserts "
    "is not present in this sweep")
print(f"PASS  (F3) at the LOWER endpoint it fails at {lofail} of {lo}, worst ratio "
      f"{mp.nstr(loworst,8)} at a=({','.join(loat)}) -- so the instrument that "
      f"settles one endpoint does not settle the other, which is how these two "
      f"ends have differed at every step")

print()
print("ALL PASS  check_fujiwara_clearance")
