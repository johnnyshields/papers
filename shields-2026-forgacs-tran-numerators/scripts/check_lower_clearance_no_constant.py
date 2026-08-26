#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `sec:geometry`,
`eq:ab-def`.

At the `rho = 1` lower endpoint the clearance has NO uniform constant, and this
is the difference between that endpoint and the `r = 1` upper one.

On the upper side the separation is `prod a_k >= 8 L^3` -- a constant, SHARP at
`a_1 = a_2 = a_3` -- so the remaining root clears `8L` and a radius of `2L`
separates every admissible pencil at once.  The lower endpoint has the same
SHAPE: Vieta puts the non-collision roots at `prod a_k / t_a^2`, so at `n = 3`
the clearance is `prod a_k > t_a^3`.  It does not have the same content.

Writing `v_k = t_a/(a_k - t_a)`, the endpoint condition `Sigma(t_a) = 0` is
`sum_k v_k = -r`, and `a_k = t_a (v_k + 1)/v_k`, so

    prod a_k / t_a^3 = prod (1 + 1/v_k).

At `rho = 1` exactly one `v_k` is below `-1` (the zero left of `t_a`) and the
others are positive.  Minimising that product under `sum v_k = -1` gives
`(p+2)^2 / (p(1+p))` at the optimum, which DECREASES in `p` to 1 -- so the
infimum is 1 and it is not attained.

  (C1) The ratio exceeds 1 at every pencil, so a fixed separating radius exists
       PER PENCIL and the endpoint does separate.
  (C2) It approaches 1 as the pencil approaches confluence, at rate ~ sqrt(3) eps
       for `a = (1, 1+eps, 1+2eps)`.  So there is no constant `K > 1` with
       `prod a_k >= K t_a^3` over admissible pencils -- no analogue of the 8.
  (C3) Consequently a radius of `2 t_a`, the transcription of the upper side's
       `2L`, CONTAINS the next root for small `eps` and does not separate.  The
       radius has to be chosen inside `(t_a, prod a_k / t_a^2)`, an interval that
       can be arbitrarily thin.

  (C4) What DOES bound the clearance is the RELATIVE gap:
       `ratio - 1 >= (x_2 - x_1)/x_2`, holding on every pencil tested and sharp
       to second order.  A multiple of the ABSOLUTE gap does NOT work -- that
       quotient falls to 0.247 at `a = (1,100,100)` and keeps falling.

mpmath only.  `t_a` is bracketed STRICTLY inside `(x_1, x_2)` and found by
bisection on `E(t) = t Q'(t) - r Q(t)`.  The bracket matters: `(x_1, max a_k)`
can contain TWO roots of `E`, so its endpoints share a sign and bisection returns
the larger one -- a confident wrong number from a bracket that does not
bracket.
"""
from mpmath import mp, mpf, mpc, findroot, fabs, polyroots

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


def t_a(a, r):
    """The endpoint critical point, bracketed strictly inside (x_1, x_2)."""
    Q = qcoeffs(1.0, a)
    Qp = deriv(Q)
    E = lambda t: (mpc(t) * peval(Qp, mpc(t)) - r * peval(Q, mpc(t))).real
    lo = mpf(min(a)) * (1 + mpf(10)**-16)
    hi = mpf(sorted(a)[1]) * (1 - mpf(10)**-16)
    if E(lo) * E(hi) > 0:
        return None
    return mpf(findroot(E, (lo, hi), solver='bisect', tol=mpf(10)**-32))


def ratio(a, r):
    ta = t_a(a, r)
    if ta is None:
        return None, None
    prod = mpf(1)
    for x in a:
        prod *= mpf(x)
    return prod / ta**3, ta


EPS = [mpf(1) / 2, mpf(1) / 10, mpf(1) / 100, mpf(1) / 1000,
       mpf(10)**-4, mpf(10)**-6]

print("rho = 1 lower endpoint: prod(a)/t_a^3 as the pencil approaches confluence")
print()

rows = []
for e in EPS:
    a = [mpf(1), 1 + e, 1 + 2 * e]
    rt, ta = ratio(a, 1)
    assert rt is not None, f"eps={mp.nstr(e,6)}: no t_a in (x_1, x_2)"
    rows.append((e, ta, rt))
    print(f"  eps={mp.nstr(e,6):9s} t_a={mp.nstr(ta,14):16s} ratio={mp.nstr(rt,10)}")
print()

# (C1) it always exceeds 1 -- the endpoint does separate, per pencil
for e, ta, rt in rows:
    assert rt > 1, f"eps={mp.nstr(e,6)}: ratio {mp.nstr(rt,10)} <= 1"
print(f"PASS  (C1) the ratio exceeds 1 at every pencil, so a fixed separating "
      f"radius EXISTS for each -- the endpoint separates")

# (C2) but the infimum is 1: no uniform constant
assert rows[-1][2] < 1 + mpf(10)**-5, (
    f"the ratio does not approach 1; smallest seen {mp.nstr(rows[-1][2],10)}")
for (e0, _, r0), (e1, _, r1) in zip(rows, rows[1:]):
    assert r1 < r0, "the ratio is not decreasing toward confluence"
rate = (rows[-1][2] - 1) / rows[-1][0]
assert fabs(rate - mp.sqrt(3)) < mpf(1) / 100, (
    f"the approach rate is {mp.nstr(rate,8)}, not ~sqrt(3)")
print(f"PASS  (C2) it decreases monotonically to 1 as eps -> 0, reaching "
      f"{mp.nstr(rows[-1][2],10)} at eps = 1e-6, at rate ~sqrt(3)*eps "
      f"({mp.nstr(rate,8)}) -- so NO constant K > 1 bounds prod(a)/t_a^3 below, "
      f"and there is no analogue of the upper side's 8")

# (C3) so a radius of 2*t_a does not separate
bad = [(e, ta, rt) for e, ta, rt in rows if rt < 2]
assert bad, "no pencil where 2*t_a fails -- (C3) is untestable here"
e, ta, rt = bad[-1]
assert rt * ta < 2 * ta, "arithmetic slip: the next root should be inside 2*t_a"
print(f"PASS  (C3) at eps = {mp.nstr(e,6)} the next root sits at "
      f"{mp.nstr(rt,10)}*t_a, INSIDE a radius of 2*t_a -- so transcribing the "
      f"upper side's 2L as 2*t_a does not separate, and the radius must be chosen "
      f"inside (t_a, prod(a)/t_a^2), an interval that can be arbitrarily thin")

# (C4) What DOES bound it: the RELATIVE gap.  No constant works and no multiple
# of the ABSOLUTE gap works either -- `(ratio-1)/(x_2-x_1)` falls to 0.247 at
# `a = (1,100,100)` and keeps falling.  But
#
#     ratio - 1  >=  (x_2 - x_1) / x_2
#
# holds on every pencil tested, and is sharp to second order: on the tightest
# family `a = (1, 1+g, 1+g)` the slack is `(8/9) g^2 + O(g^3)`.
def clearance(a, r=1):
    ta = t_a(a, r)
    if ta is None:
        return None
    prod = mpf(1)
    for x in a:
        prod *= mpf(x)
    return prod / ta**3


FAM = []
for sv in [mpf(1) + mpf(k) / 20 for k in range(1, 60)] + [mpf(x) for x in (4, 5, 7, 10, 20, 50, 100)]:
    FAM.append([mpf(1), sv, sv])
for ev in [mpf(1) / 2, mpf(1) / 10, mpf(1) / 100, mpf(1) / 1000]:
    FAM.append([mpf(1), 1 + ev, 1 + 2 * ev])
for x2 in (mpf(101) / 100, mpf(13) / 10, mpf(2), mpf(5)):
    for mlt in (mpf(1), mpf(2), mpf(10), mpf(100)):
        FAM.append([mpf(1), x2, x2 * mlt])

FAM_W = FAM
worst, worst_at, tested = None, None, 0
lin_worst = None
for a in FAM:
    rt = clearance(a)
    if rt is None:
        continue
    tested += 1
    rel = (a[1] - a[0]) / a[1]
    slack = (rt - 1) - rel
    if worst is None or slack < worst:
        worst, worst_at = slack, [mp.nstr(x, 6) for x in a]
    lin = (rt - 1) / (a[1] - a[0])
    if lin_worst is None or lin < lin_worst:
        lin_worst = lin
assert tested >= 60, f"only {tested} pencils reached"
assert worst >= 0, (
    f"the relative-gap bound FAILS at a=({','.join(worst_at)}), slack "
    f"{mp.nstr(worst,10)}")
assert lin_worst < mpf(1) / 2, (
    f"the ABSOLUTE-gap quotient did not fall below 1/2 ({mp.nstr(lin_worst,8)}), "
    f"so this sweep cannot show that a linear-in-gap bound fails")
print(f"PASS  (C4) `ratio - 1 >= (x_2-x_1)/x_2` holds at all {tested} pencils "
      f"(worst slack {mp.nstr(worst,8)}), while the ABSOLUTE-gap quotient "
      f"`(ratio-1)/(x_2-x_1)` falls to {mp.nstr(lin_worst,6)} -- so the RELATIVE "
      f"gap bounds the clearance where a constant and an absolute-gap multiple "
      f"both fail")

# sharpness of (C4): the slack vanishes quadratically on the tightest family
tight = []
for k in range(2, 7):
    g = mpf(10)**(-k)
    a = [mpf(1), 1 + g, 1 + g]
    rt = clearance(a)
    assert rt is not None
    tight.append((g, (rt - 1) - g / (1 + g)))
for g, sl in tight:
    assert sl > 0, f"slack {mp.nstr(sl,8)} at g={mp.nstr(g,6)} is not positive"
    assert fabs(sl / g**2 - mpf(8) / 9) < mpf(1) / 50, (
        f"slack/g^2 = {mp.nstr(sl/g**2,8)} at g={mp.nstr(g,6)}, not ~8/9")
print(f"PASS  and it is SHARP to second order: on a = (1, 1+g, 1+g) the slack is "
      f"(8/9)g^2 + O(g^3), positive at every g tested down to 1e-6, so the "
      f"relative gap is the right quantity and not merely a valid one")

# (C5) The target, restated with the pencil removed.  Put `w_k = a_k / t_a`.
# Then the endpoint condition `Sigma(t_a) = 0` is `sum_k 1/(w_k - 1) = -r`, the
# clearance ratio is `prod w_k`, and the relative gap is `1 - w_1/w_2`.  So
#
#     prod a_k / t_a^3 - 1 >= (x_2 - x_1)/x_2     <=>     w_1 w_2 w_3 + w_1/w_2 >= 2
#
# under `sum_k 1/(w_k - 1) = -1` with `0 < w_1 < 1 < w_2 <= w_3` -- the ordering
# saying exactly that `t_a` lies strictly between `x_1` and `x_2`.
#
# That is a three-variable algebraic inequality with one constraint and NO
# polynomial roots in it, which is the shape `eight_mul_pow_le_prod_of_sum_eq_one`
# already took on the upper side.  Stated here because a target in this form is
# reachable where one phrased over pencils is not.
wrows = 0
wmin, wmin_at = None, None
for a in FAM_W:
    ta = t_a(a, 1)
    if ta is None:
        continue
    w = [mpf(x) / ta for x in a]
    cons = sum(1 / (wk - 1) for wk in w)
    scale = max(fabs(1 / (wk - 1)) for wk in w)
    assert fabs(cons + 1) < mpf(10)**-18 * max(mpf(1), scale), (
        f"a={[mp.nstr(x,6) for x in a]}: the w-form of the endpoint condition is "
        f"off by {mp.nstr(fabs(cons+1),6)} against term scale {mp.nstr(scale,6)}")
    assert 0 < w[0] < 1 < w[1] <= w[2] + mpf(10)**-25, (
        f"a={[mp.nstr(x,6) for x in a]}: ordering 0 < w1 < 1 < w2 <= w3 fails")
    val = w[0] * w[1] * w[2] + w[0] / w[1]
    if wmin is None or val < wmin:
        wmin, wmin_at = val, [mp.nstr(x, 6) for x in a]
    wrows += 1
assert wrows >= 50, f"only {wrows} pencils reached the w-form"
assert wmin >= 2, f"the w-form FAILS: min {mp.nstr(wmin,12)} at {wmin_at}"
print(f"PASS  (C5) with w_k = a_k/t_a the endpoint condition is exactly "
      f"sum 1/(w_k - 1) = -r at all {wrows} pencils, the ordering "
      f"0 < w1 < 1 < w2 <= w3 holds, and the clearance target becomes the "
      f"three-variable algebraic inequality w1*w2*w3 + w1/w2 >= 2 -- minimum "
      f"{mp.nstr(wmin,12)} at a=({','.join(wmin_at)}), no polynomial roots in it")

# (C6) `n >= 4`, the exact analogue of the upper side's BANK-39 situation.  With
# `n - 2` non-collision roots sharing the Vieta product, a lower bound on that
# product cannot bound the MINIMUM -- so the closed form settles `n = 3` and no
# more.  Swept anyway, the minimum still clears, but by much less than upstairs.
def polyroots_of(a, r, ta):
    Q = qcoeffs(1.0, a)
    z = mpf((-peval(Q, mpc(ta)) / mpc(ta) ** r).real)
    D = [mpf(0)] * max(0, r + 1 - len(Q)) + list(Q)
    D[len(D) - 1 - r] += z
    while len(D) > 1 and D[0] == 0:
        D = D[1:]
    return sorted(polyroots(D, maxsteps=400, extraprec=700), key=lambda t: fabs(t))


BIG = []
for base in ([1, 2, 3, 4], [1, 1.5, 3, 7], [1, 2, 4, 8], [1, 1.2, 5, 20],
             [1, 2, 3, 4, 5], [1, 1.1, 2, 3, 50], [1, 3, 9, 27, 81]):
    for rr in (1, 2):
        BIG.append(([mpf(x) for x in base], rr))
seps, sworst, sat = [], None, None
for a, rr in BIG:
    ta = t_a(a, rr)
    if ta is None:
        continue
    others = [t for t in polyroots_of(a, rr, ta) if fabs(t - ta) > mpf(10)**-14]
    assert others, f"a={[mp.nstr(x,4) for x in a]}: no non-collision root"
    sep = min(fabs(t) for t in others) / ta
    assert sep > 1, (
        f"a={[mp.nstr(x,4) for x in a]}, r={rr}: a root sits at {mp.nstr(sep,8)}*t_a, "
        f"INSIDE the collision radius -- the rho = 1 separation fails at n >= 4")
    seps.append(sep)
    if sworst is None or sep < sworst:
        sworst, sat = sep, (len(a), rr, [mp.nstr(x, 4) for x in a])
assert len(seps) >= 12, f"only {len(seps)} cases reached"
print(f"PASS  (C6) at n = 4,5 over {len(seps)} cases every non-collision root still "
      f"clears t_a, worst {mp.nstr(sworst,8)} at n={sat[0]}, r={sat[1]}, "
      f"a=({','.join(sat[2])}) -- but the Vieta product cannot establish this, "
      f"since n-2 roots share it, so the closed form settles n = 3 only")
assert sworst < 4, (
    "the lower side's n >= 4 margin is not visibly thinner than the upper side's, "
    "so this row is not showing the asymmetry it claims")
print(f"PASS  and it is much thinner than upstairs: {mp.nstr(sworst,6)} here "
      f"against 8.013 at the r = 1 upper endpoint, which is the same "
      f"no-uniform-constant asymmetry seen at n = 3, persisting into n >= 4")

print()
print("ALL PASS  check_lower_clearance_no_constant")
