#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `eq:ab-def`, BANK-40.

Why the `rho = 1` corner composes at all, and which of its three suspected false
binders is actually false.

`thm:weighted-dominance` carries `hrho : 0 < n_0 -> 2 <= rho`.  At `rho = 1` that
looks like a wall.  It is not, because `n_0 = 0`: the collision at `t_a` has
multiplicity EXACTLY two, so the retained lower cluster is the principal pair
alone and the implication is discharged VACUOUSLY.  That mirrors `n_1 = 0` at the
`r = 1` upper endpoint exactly -- and it is the same reason: a double root, not a
collapsing cluster.

  (C1) multiplicity exactly 2 at `t_a`, at `r = 1` and `r = 2`, `n = 3` and `4`.
  (C2) so `n_0 = 0` and every `clusterAlpha` binder is EMPTY rather than false.
  (C3) the clearance is a ratio with no uniform constant, so the retained radius
       must be a formula rather than a multiple of `t_a`.

THE THREE SUSPECTED BINDERS ARE NOT THREE OF A KIND, and the distinction decides
what each needs:

  * `hk_0` is genuinely FALSE at `rho = 1`.  `ftBranchZLower`'s `else 0` hardcodes
    the `rho >= 2` endpoint value `g(x_1) = 0`, so the binder becomes `Q(t_a) = 0`
    and `t_a` is a critical point of `g`, not a root of `Q`.  Needs a repair --
    `ForgacsTran.EndpointLowerRhoOne` supplies it.
  * `clusterAlpha` is VACUOUS, not false.  `n_0 = 0` empties it.  Needs nothing,
    but tests nothing either: at `Fin 0` these clauses discharge by `Fin.elim0`,
    so the content of the block sits in the pair-and-circle clauses.
  * the closed-window `hsimple_1` is false, but the theorem's binder is PUNCTURED
    (`0 < delta`), so the false form is not the one in use.  Needs nothing.

A binder that is false, one that is empty and one that is merely adjacent to a
false statement invite three different responses, and only the first is a defect.

mpmath only, 40 digits.  `t_a` is bracketed between consecutive distinct roots,
where `Sigma` runs from `-inf` to `+inf`.
"""
from mpmath import mp, mpf, mpc, findroot, polyroots, fabs, re

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


def sigma(a, r, s):
    return sum(mpf(s) / (mpf(ak) - s) for ak in a) + r


def t_a(a, r):
    srt = sorted(set(mpf(x) for x in a))
    for i in range(len(srt) - 1):
        lo, hi = srt[i] + mpf(10) ** -14, srt[i + 1] - mpf(10) ** -14
        if sigma(a, r, lo) * sigma(a, r, hi) < 0:
            return mpf(re(findroot(lambda s: sigma(a, r, s), (lo, hi),
                                   solver='bisect', tol=mpf(10) ** -32)))
    return None


def dcoeffs(Q, z, r):
    D = [mpf(0)] * max(0, r + 1 - len(Q)) + list(Q)
    D[len(D) - 1 - r] += z
    while len(D) > 1 and D[0] == 0:
        D = D[1:]
    return D


PENCILS = [([1.0, 2.0, 4.0], 1.0, 1), ([1.0, 2.0, 3.0], 1.0, 1),
           ([0.5, 1.7, 4.0], 1.0, 1), ([1.0, 2.0, 3.0, 4.0], 1.0, 1),
           ([1.0, 2.0, 4.0], 1.0, 2), ([1.0, 2.0, 3.0, 4.0], 1.0, 2)]

print("is the lower retained cluster empty at rho = 1?")
print()
rows = []
for a, c, r in PENCILS:
    Q = qcoeffs(c, a)
    ta = t_a(a, r)
    aend = mpf(re(-peval(Q, mpf(ta)) / mpf(ta) ** r))
    rts = polyroots(dcoeffs(Q, aend, r), maxsteps=500, extraprec=900)
    at_ta = [t for t in rts if fabs(t - ta) < mpf(10) ** -12]
    others = [t for t in rts if fabs(t - ta) >= mpf(10) ** -12]
    ratio = min(fabs(t) / ta for t in others) if others else None
    rows.append((a, r, ta, len(at_ta), len(others), ratio))
    print(f"  a={a} r={r}: t_a={mp.nstr(ta,8)}  multiplicity at t_a = {len(at_ta)}   "
          f"others {len(others)}   nearest |root|/t_a = {mp.nstr(ratio,8)}")
print()

for a, r, ta, m, _, _ in rows:
    assert m == 2, f"a={a} r={r}: multiplicity at t_a is {m}, not 2"
print(f"PASS  (C1) the collision at t_a has multiplicity EXACTLY two at all "
      f"{len(rows)} pencil/r pairs")
print(f"PASS  (C2) so the retained lower cluster is the principal pair alone, "
      f"n_0 = 0, and hrho : 0 < n_0 -> 2 <= rho is discharged VACUOUSLY -- which "
      f"is why the rho = 1 corner composes at all.  Every clusterAlpha binder is "
      f"EMPTY rather than false, and empty binders test nothing: the content sits "
      f"in the pair-and-circle clauses, as it does at the r = 1 upper endpoint")

ratios = [x for *_, x in rows if x]
assert min(ratios) > 1, "a root sits inside t_a"
print(f"PASS  (C3) the clearance |root|/t_a runs {mp.nstr(min(ratios),6)} to "
      f"{mp.nstr(max(ratios),6)} over THIS sample.  No uniform constant is claimed "
      f"from it -- the team lead measured the infimum as 1, unattained, over a "
      f"wider family, so the retained radius must be a FORMULA rather than a "
      f"multiple of t_a.  That figure is cited, not reproduced here")
print()
print("ALL PASS")
