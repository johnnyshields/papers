#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; the `_0` retained group
at `rho = 1`, `eq:ab-def`.

**NEGATIVE.**  Whether the normalized separation can be proved through squared
moduli alone.  It cannot, and this file is here so nobody spends a pass finding
that out.

`LowerSeparationNormalized` leaves one inequality unproved: with `v_0 < -1`,
`v_k > 0` for `k != 0`, and `sum_k v_k = -r`,

    prod_k (1 - sigma v_k) = (1 + sigma)^r  and  sigma != 0   ==>   |1 + sigma| > 1.

**The tempting simplification.**  Taking squared moduli removes every complex
number.  With `X = -2 Re sigma` and `Y = |sigma|^2`,

    |1 - sigma v|^2 = 1 + v X + v^2 Y,        |1 + sigma|^2 = 1 - X + Y,

so the equation reads `prod_k (1 + X v_k + Y v_k^2) = (1 - X + Y)^r` and the goal
`|1+sigma| > 1` reads `Y > X`.  Assuming the negation gives three constraints:
`Y > 0` (from `sigma != 0`), `Y <= X` (the negation), and `4Y >= X^2` (since
`Y = |sigma|^2 >= (Re sigma)^2`).  The last two force `X <= 4`, so the region is
compact and it all looks like a finite real problem.

**Why it fails.**  A proof by contradiction in this form needs

    0 < Y <= X,  4Y >= X^2,  v_0 < -1,  v_k > 0,  sum v_k = -r
        ==>  prod_k (1 + X v_k + Y v_k^2)  >  (1 - X + Y)^r

to hold at EVERY admissible `(X, Y, v)` -- because a root satisfies it with
EQUALITY, so a single point of failure destroys the contradiction rather than
weakening it.  That implication is false, at every `n` tested, and the failures
are not near-misses.

The reason is structural: the pencil equation is COMPLEX, two real equations, and
the modulus keeps only one combination of them.  The phase is not slack that a
sharper estimate can recover; it is half the hypothesis.

  (M1) the per-factor reduction is exact -- so the algebra above is right, and it
       is the logic that fails rather than the identity.
  (M2) the modulus-only target is FALSE at n = 2, 3, 4, 5, with worst deficits
       around -0.6 to -0.8.  Not a small-`n` artifact.
  (M3) consistency: at ACTUAL roots the modulus equation holds with equality and
       `|1 + sigma| > 1` still holds, so the failures sit at `(X, Y)` that no root
       realizes.  The complex statement is fine; only this route to it is not.
"""

from mpmath import mp, mpf, mpc, fabs, polyroots, re as mpre

mp.dps = 40


def prod_g(X, Y, v):
    p = mpf(1)
    for vk in v:
        p *= 1 + X * vk + Y * vk * vk
    return p


def root_sigmas(v, r):
    """Roots of prod_k (1 - sigma v_k) - (1 + sigma)^r."""
    P = [mpf(1)]
    for vk in v:
        nxt = [mpf(0)] * (len(P) + 1)
        for i, co in enumerate(P):
            nxt[i] += co
            nxt[i + 1] -= co * vk
        P = nxt
    R = [mpf(0)] * (r + 1)
    b = mpf(1)
    for i in range(r + 1):
        R[i] = b
        b = b * (r - i) / (i + 1)
    m = max(len(P), len(R))
    C = [mpf(0)] * m
    for i, co in enumerate(P):
        C[i] += co
    for i, co in enumerate(R):
        C[i] -= co
    while len(C) > 1 and fabs(C[-1]) < mpf(10) ** -35:
        C.pop()
    if len(C) <= 1:
        return []
    return polyroots(list(reversed(C)), maxsteps=800, extraprec=1200)


def admissible_XY(steps=20):
    out = []
    for i in range(1, steps + 1):
        X = mpf(4) * i / steps
        lo, hi = X * X / 4, X
        if lo > hi:
            continue
        for j in range(0, steps + 1):
            Y = lo + (hi - lo) * j / steps
            if Y > 0:
                out.append((X, Y))
    return out


TAILS = {1: [[mpf("0.01")], [mpf(1)], [mpf(10)]],
         2: [[mpf("0.01")] * 2, [mpf(1), mpf(3)], [mpf(20), mpf("0.1")],
             [mpf("0.001")] * 2],
         3: [[mpf("0.05")] * 3, [mpf(1), mpf(2), mpf(4)],
             [mpf(50), mpf(1), mpf("0.2")], [mpf("0.001")] * 3],
         4: [[mpf("0.02")] * 4, [mpf(1), mpf(1), mpf(5), mpf("0.5")]]}
RS = (1, 2, 3)

print("can the normalized separation go through squared moduli alone?  NO")
print()

# ---- (M1) the per-factor reduction is exact ---------------------------------
worst = mpf(0)
for sg in (mpc(-1, 0), mpc("-0.3", "0.4"), mpc("-1.5", "0.2"), mpc("0.2", "-0.7"),
           mpc("-0.05", "0.01"), mpc(2, 3)):
    X, Y = -2 * mpre(sg), fabs(sg) ** 2
    for v in ([mpf("-3.5"), mpf(1), mpf("0.5")], [mpf("-2.2"), mpf("0.2"), mpf(1)]):
        lhs = mpf(1)
        for vk in v:
            lhs *= fabs(1 - sg * vk) ** 2
        worst = max(worst, fabs(lhs - prod_g(X, Y, v)),
                    fabs(fabs(1 + sg) ** 2 - (1 - X + Y)))
assert worst < mpf(10) ** -25, f"reduction mismatch {mp.nstr(worst,6)}"
print(f"PASS  (M1) |1 - sigma v|^2 = 1 + Xv + Yv^2 and |1+sigma|^2 = 1 - X + Y to "
      f"{mp.nstr(worst,4)}.  The identity is right; what follows is a failure of "
      f"the LOGIC that uses it, not of the algebra")

# ---- (M2) the modulus-only target is false, at every n ----------------------
rows = []
for m in sorted(TAILS):
    fails = tot = 0
    worstd = None
    for r in RS:
        for tail in TAILS[m]:
            v = [-(mpf(r) + sum(tail))] + list(tail)
            assert v[0] < -1 and all(x > 0 for x in v[1:])
            assert fabs(sum(v) + r) < mpf(10) ** -30
            for X, Y in admissible_XY():
                tot += 1
                d = prod_g(X, Y, v) - (1 - X + Y) ** r
                if d <= 0:
                    fails += 1
                    worstd = d if worstd is None else min(worstd, d)
    rows.append((m, fails, tot, worstd))
    print(f"    n = {m + 1}:  {fails}/{tot} admissible (X,Y) fail"
          + (f",  worst deficit {mp.nstr(worstd, 6)}" if worstd is not None else ""))
for m, fails, tot, worstd in rows:
    assert fails > 0, (
        f"no failure at n={m+1} -- if the modulus target holds there after all, "
        f"this file's conclusion is too strong and must be re-read")
    assert worstd < mpf(-1) / 10, (
        f"the worst deficit at n={m+1} is {mp.nstr(worstd,6)}, a near-miss -- "
        f"a sharper estimate might close it and the route is not clearly dead")
print(f"PASS  (M2) the modulus-only target FAILS at every n tested, with deficits "
      f"of order 0.1 or worse rather than near-misses.  A root satisfies the "
      f"modulus equation with EQUALITY, so the contradiction needs the strict "
      f"inequality everywhere admissible; one failure ends it, and there are many")

# ---- (M3) consistency: the complex statement is untouched -------------------
checked = 0
tightest = None
for m in sorted(TAILS):
    for r in RS:
        for tail in TAILS[m]:
            v = [-(mpf(r) + sum(tail))] + list(tail)
            for z in root_sigmas(v, r):
                sg = mpc(z)
                if fabs(sg) < mpf(10) ** -12:
                    continue
                X, Y = -2 * mpre(sg), fabs(sg) ** 2
                # at a root the modulus equation is an EQUALITY -- compared
                # RELATIVELY, since a far-out root makes both sides large and an
                # absolute tolerance then reports a mismatch that is not one
                lhsm = prod_g(X, Y, v)
                rhsm = (1 - X + Y) ** r
                scale = max(fabs(lhsm), fabs(rhsm), mpf(1))
                assert fabs(lhsm - rhsm) / scale < mpf(10) ** -20, (
                    "the modulus equation is not tight at a root")
                mnorm = fabs(1 + sg)
                assert mnorm > 1, (
                    f"|1+sigma| = {mp.nstr(mnorm,8)} <= 1 at an actual root -- the "
                    f"COMPLEX statement would then be false, which contradicts "
                    f"check_lower_separation_normalized.py and must be resolved "
                    f"before either is trusted")
                checked += 1
                tightest = mnorm if tightest is None else min(tightest, mnorm)
print(f"PASS  (M3) at all {checked} actual non-collision roots the modulus equation "
      f"holds with equality and |1 + sigma| > 1 anyway, tightest "
      f"{mp.nstr(tightest,8)}.  So (M2)'s failures sit at (X,Y) that no root "
      f"realizes: the complex statement is intact and it is only this route to it "
      f"that is closed")

print()
print("ALL PASS")
