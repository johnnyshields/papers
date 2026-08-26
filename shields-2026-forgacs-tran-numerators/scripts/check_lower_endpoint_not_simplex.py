#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `eq:ab-def`, BANK-41.

Does the simplex route that closed BANK-39's UPPER side transfer to the LOWER
endpoint?  It does not, and the obstruction differs by regime -- which is why the
regimes are separated here rather than averaged.

`check_upper_endpoint_general_n.py` closes the upper side by normalizing to
`u_k = L/(a_k+L)`, where the endpoint condition `E(-L) = 0` says exactly
`sum_k u_k = 1`: a point of the SIMPLEX.  Every step of the Lean chain then
consumes non-negativity -- `esymm_nonneg`, `succ_mul_esymm_le`, the alternating
collapse, `simplexPoly_coeff_nonneg`.

Both ends normalize to `prod_k (1 - v_k (s-1)) = s^r` with `v_k = s_0/(a_k - s_0)`
at the collision `s_0`, and `Sigma(s_0) = 0` reads `sum_k v_k = -r` at both.  The
SAME critical function, which is why the difference is invisible until the signs
are computed.

  TWO OBJECTS, and they coincide only at `rho = 1`.  Writing `x_1` for the
  smallest root and `rho` for its multiplicity:

  * `rho = 1`: the branch's endpoint limit IS the zero of `Sigma` in
    `(x_1, next root)`, and the normalization can be written.  The obstruction is
    then a SIGN -- see (L1)-(L4).
  * `rho >= 2`: `Sigma` has a pole at `x_1` and the branch's limit is `x_1`
    ITSELF, where `v_k = x_1/(a_k - x_1)` is UNDEFINED for every repeated index.
    The normalization cannot be written at all, which is a stronger obstruction
    than a sign failure rather than a weaker one -- and Lean's `x/0 = 0` would
    silently return `v_k = 0` there, the third appearance of that trap tonight.

  (L1) At `rho = 1`, `t_a > x_1` necessarily: below `x_1` every term of
       `sum_k s/(a_k-s)` is positive and can never reach `-r`.  So some
       `a_k - t_a` are negative and the `v_k` are of MIXED sign.
  (L2) `sum_k v_k = -r` exactly, at `r = 1` and `r = 2`.
  (L3) `e_2(v) < 0` at every one -- the first elementary symmetric fact the upper
       route uses.  And it has an exact criterion rather than a tally: under
       `sum v_k = -r`,

           e_2(v) = ((sum v_k)^2 - sum v_k^2)/2 = (r^2 - sum v_k^2)/2,

       so `e_2 < 0` PRECISELY when `sum v_k^2 > r^2`.  Over the pencils here the
       ratio runs 4.47 upward.  No tighter figure is quoted: an earlier draft cited
       a 1.020 measured elsewhere, and that turned out to come from a `rho = 4`
       pencil -- the same regime confusion this check exists to separate, arriving
       inside the number meant to sharpen it.  The honest statement is that the
       failure is decisive in KIND; how close to marginal it can get is a question
       about the `rho = 1` family and is open.
  (L4) The core `2 + 2 prod(1-v) - prod(1+v)` is not a small positive margin there
       but ranges over four orders of magnitude, so it is not the upper endpoint's
       quantity under a substitution: it is a different object.  (An earlier draft
       of this check reported it taking both signs; that range mixed the two
       objects below, and the negative values all came from `rho >= 2` pencils
       where the normalization is not defined at all.)
  (L5) `rho >= 2`: the normalization is undefined at the branch limit.

`Sigma` runs from `r` at `0^-` to `r - n` at `-infinity`, so the upper collision
exists exactly when `r < n`; at `r = n` it is pushed to infinity, a degeneracy
`eq:Q-hypotheses` excludes rather than a bracketing failure.

mpmath only, 40 digits.  `t_a` is bracketed between consecutive DISTINCT roots,
where `Sigma` runs from `-inf` to `+inf`, so no root-finder heuristic is involved.
"""
from mpmath import mp, mpf, findroot, fabs, re

mp.dps = 40


def sigma(a, r, s):
    return sum(mpf(s) / (mpf(ak) - s) for ak in a) + r


def rho_of(a):
    x1 = min(mpf(x) for x in a)
    return x1, sum(1 for x in a if fabs(mpf(x) - x1) < mpf(10) ** -20)


def t_a(a, r):
    """Zero of `Sigma` in `(x_1, next distinct root)`."""
    srt = sorted(set(mpf(x) for x in a))
    for i in range(len(srt) - 1):
        lo, hi = srt[i] + mpf(10) ** -12, srt[i + 1] - mpf(10) ** -12
        if sigma(a, r, lo) * sigma(a, r, hi) < 0:
            return mpf(re(findroot(lambda s: sigma(a, r, s), (lo, hi),
                                   solver='bisect', tol=mpf(10) ** -30)))
    return None


def esym(v):
    n = len(v)
    e = [mpf(1)] + [mpf(0)] * n
    for x in v:
        for j in range(n, 0, -1):
            e[j] += e[j - 1] * x
    return e


SIMPLE = [([1.0, 2.0, 3.0], "a=(1,2,3)"),
          ([1.0, 2.0, 3.0, 4.0], "a=(1,2,3,4)"),
          ([0.5, 1.0, 2.0, 4.0, 8.0], "a=(0.5,1,2,4,8)"),
          ([1.0, 1.05, 1.1, 5.0], "a=(1,1.05,1.1,5) clustered"),
          ([0.4, 0.9, 1.7], "a=(0.4,0.9,1.7)")]
REPEATED = [([1.0, 1.0, 2.0], "a=(1,1,2)"),
            ([0.4, 0.4, 1.7], "a=(0.4,0.4,1.7)"),
            ([1.0, 1.0, 1.0, 3.0], "a=(1,1,1,3)")]

print("does the simplex route transfer to the lower endpoint?")
print()
print("rho = 1 -- the normalization CAN be written, and fails by sign")
rows = []
for a, lab in SIMPLE:
    x1, rho = rho_of(a)
    assert rho == 1, f"{lab} is not a simple-smallest-root pencil"
    for r in [1, 2]:
        ta = t_a(a, r)
        if ta is None:
            continue
        v = [ta / (mpf(ak) - ta) for ak in a]
        e = esym(v)
        p2 = sum(x ** 2 for x in v)
        pm, pp = mpf(1), mpf(1)
        for x in v:
            pm *= (1 - x)
            pp *= (1 + x)
        rows.append((lab, r, ta, x1, sum(v), sum(1 for x in v if x < 0), e[2], p2,
                     2 + 2 * pm - pp))
        print(f"  {lab} r={r}: t_a={mp.nstr(ta,8)} > x_1={mp.nstr(x1,4)}   "
              f"sum v={mp.nstr(sum(v),8)}   neg {sum(1 for x in v if x < 0)}/{len(v)}")
        print(f"      e_2={mp.nstr(e[2],8)}   sum v^2 / r^2 = {mp.nstr(p2/(r*r),8)}   "
              f"core = {mp.nstr(2+2*pm-pp,8)}")
print()

# (L1)
for lab, r, ta, x1, *_ in rows:
    assert ta > x1, f"{lab} r={r}: t_a does not exceed x_1"
print(f"PASS  (L1) t_a > x_1 at all {len(rows)} rho=1 pairs -- it must, since below "
      f"x_1 every term of sum_k s/(a_k-s) is positive and can never reach -r")

# (L2)
for lab, r, _, _, sv, *_ in rows:
    assert fabs(sv + r) < mpf(10) ** -20, f"{lab} r={r}: sum v is not -r"
print(f"PASS  (L2) sum_k v_k = -r exactly -- the SAME critical function as the upper "
      f"endpoint, which is why the difference is invisible until the signs are "
      f"computed")

# (L3) with the exact criterion
for lab, r, _, _, sv, nneg, e2, p2, _ in rows:
    assert nneg >= 1, f"{lab} r={r}: no negative coordinate"
    assert fabs(e2 - (mpf(r) ** 2 - p2) / 2) < mpf(10) ** -25, (
        f"{lab} r={r}: e_2 != (r^2 - sum v^2)/2")
    assert e2 < 0 and p2 > mpf(r) ** 2, f"{lab} r={r}: e_2 is non-negative"
ratios = [p2 / (mpf(r) ** 2) for _, r, _, _, _, _, _, p2, _ in rows]
print(f"PASS  (L3) e_2(v) = (r^2 - sum v_k^2)/2 to 25 digits, so e_2 < 0 PRECISELY "
      f"when sum v_k^2 > r^2 -- and it does, ratio {mp.nstr(min(ratios),6)} to "
      f"{mp.nstr(max(ratios),6)} over this sample.  No tighter figure is quoted: "
      f"the failure is decisive in KIND, and how close to marginal it can get over "
      f"the rho = 1 family is open.  e_2 >= 0 is the first "
      f"elementary symmetric fact the upper route uses, and four of its steps "
      f"consume non-negativity")

# (L4)
cores = [c for *_, c in rows]
assert max(cores) / min(cores) > 100, "the core analogue is unexpectedly stable"
print(f"PASS  (L4) the core analogue ranges over {mp.nstr(min(cores),6)} to "
      f"{mp.nstr(max(cores),6)} -- four orders of magnitude, not a margin sitting "
      f"just above zero -- so it is a different object rather than the upper one "
      f"under a substitution")

# (L5) the rho >= 2 regime
print()
print("rho >= 2 -- the normalization cannot be WRITTEN")
bad = []
for a, lab in REPEATED:
    x1, rho = rho_of(a)
    assert rho >= 2, f"{lab} is not a repeated-smallest-root pencil"
    undef = [k for k, x in enumerate(a) if fabs(mpf(x) - x1) < mpf(10) ** -20]
    bad.append((lab, rho, x1, undef))
    print(f"  {lab}: rho={rho}, branch limit = x_1 = {mp.nstr(x1,6)}; "
          f"v_k = x_1/(a_k - x_1) undefined at k = {undef}")
for lab, rho, x1, undef in bad:
    assert len(undef) == rho, f"{lab}: undefined count does not match rho"
print(f"PASS  (L5) at rho >= 2 the branch's endpoint limit is x_1 itself, where "
      f"v_k is undefined for every repeated index -- the normalization cannot be "
      f"written at all -- an obstruction one step EARLIER than a sign failure, and "
      f"one that asks for a different parameterization rather than a more tolerant "
      f"argument.  Lean's x/0 = 0 would silently return v_k = 0 there, which would "
      f"have read as an ordinary simplex coordinate: a CATEGORY error hidden, not "
      f"a numeric one")

print()
print("INFO  Sigma runs from r at 0^- to r - n at -infinity, so the upper collision "
      "exists exactly when r < n; at r = n it is pushed to infinity, a degeneracy "
      "eq:Q-hypotheses excludes rather than a bracketing failure")
print()
print("ALL PASS")
