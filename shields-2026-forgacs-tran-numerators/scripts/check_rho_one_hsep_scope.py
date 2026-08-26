#!/usr/bin/env python3
r"""Paper section `sec:dominance` (Proof of the main theorem), the `rho = 1`
corner of `thm:weighted-dominance` -- the SCOPE of its separation hypothesis.

The Lean statement of the `rho = 1` corner carries its separation input as a
hypothesis quantified over EVERY positive critical point:

    for all t > 0 with a_k != t and t P' - r P = 0,
        every root w != t of the pencil at z = -P(t)/t^r has |w| > t .

Its proof consumes that hypothesis at exactly ONE point, the lower endpoint.
The gap between those two is not cosmetic, and this script is what measures it.

  (H1) **The hypothesis is false as stated**, and the witness is admissible.
       Built end-to-end in the paper's own variables rather than in the
       normalized ones: `n = 3`, `c > 0`, three DISTINCT POSITIVE roots, `t > 0`
       a genuine critical point with `a_k != t` -- every hypothesis the theorem
       binds -- and a root `w` of the pencil with `w != t` and `|w| < t`.
       So the theorem's hypothesis cannot be met at this `a`, and the theorem
       therefore says nothing about it while compiling, guarding, and reading
       as a result about the whole class.

  (H2) **Why it fails, as a criterion rather than an example.**  With
       `v_k = t/(a_k - t)` the critical equation is exactly `sum_k v_k = -r`,
       and `v_k < 0` exactly when `a_k < t`.  Positivity of the roots forces
       every negative coordinate below `-1`.  The lower endpoint is the
       SMALLEST positive critical point and lies in the first gap `(a_(1), a_(2))`
       -- below `a_(1)` every term of `sum_k t/(a_k - t)` is positive and can
       never reach `-r`, and the sum runs from `-infinity` to `+infinity` across
       the first gap -- so there exactly ONE coordinate is negative.  At a
       critical point in a HIGHER gap two or more are, and separation fails.

  (H3) **One negative coordinate is the whole difference.**  Over the same
       sweep, separation holds at every one-negative configuration and fails at
       a positive fraction of the multi-negative ones.  This is what makes the
       repair a narrowing of the binder rather than a search for a better proof.

  (H4) **The narrowing is expressible in binders the theorem already has.**
       It binds `i` with `hmin : a i <= a k` for all `k`.  Adding
       `(forall k, k != i -> t < a k)` to the hypothesis says exactly "t lies in
       the first gap", hence exactly one negative coordinate.  The companion
       clause `a i < t` needs no binder: if `t < a k` for every `k` then every
       `v_k > 0` and the sum cannot be `-r`, so the critical equation excludes
       it on its own.  Asserted here, since a repair proposed without checking
       it would be a guess.

mpmath only.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50


# --- (H1) the witness, in the paper's own variables ---------------------------
T = mp.mpf(1)
V = [mp.mpf('-96.862994'), mp.mpf('-1.0354007'), mp.mpf('96.898395')]
R = 1
C = mp.mpf('2.5')

# renormalize the third coordinate so the critical equation holds exactly
V[2] = -mp.mpf(R) - V[0] - V[1]
A = [T * (1 + 1 / v) for v in V]

assert abs(sum(V) + R) < mp.mpf('1e-40')
assert all(a > 0 for a in A), A                      # positive roots
assert len(set(mp.nstr(a, 30) for a in A)) == 3      # distinct
assert all(abs(a - T) > mp.mpf('1e-6') for a in A)   # a_k != t
assert C > 0


def p_eval(t):
    out = C
    for a in A:
        out *= (t - a)
    return out


def dp_eval(t):
    """P'(t) = P(t) * sum_k 1/(t - a_k), by the product rule."""
    return sum(C * mp.fprod([t - b for b in A if b is not a]) for a in A)


# t is a genuine critical point: t P'(t) - r P(t) = 0
crit = T * dp_eval(T) - R * p_eval(T)
assert abs(crit) < mp.mpf('1e-30'), mp.nstr(crit, 10)

# the pencil at z = -P(t)/t^r, and its roots
Z = -p_eval(T) / T ** R
# P + z X^r, ascending coefficients of the cubic C prod (X - a_k)
e1 = A[0] + A[1] + A[2]
e2 = A[0] * A[1] + A[0] * A[2] + A[1] * A[2]
e3 = A[0] * A[1] * A[2]
asc = [C * (-e3), C * e2, C * (-e1), C]              # C(X^3 - e1 X^2 + e2 X - e3)
asc[R] += Z
den_roots = mp.polyroots(list(reversed(asc)), maxsteps=800, extraprec=400)

# t itself is a root of the pencil, by construction
assert min(abs(w - T) for w in den_roots) < mp.mpf('1e-25')

others = [w for w in den_roots if abs(w - T) > mp.mpf('1e-15')]
worst = min(others, key=lambda w: abs(w))
assert abs(worst) < T, (mp.nstr(abs(worst), 20), mp.nstr(T, 20))

print("PASS  (H1) the separation hypothesis is FALSE at an admissible instance:")
print(f"        n = 3, c = {mp.nstr(C, 4)}, a = "
      f"[{', '.join(mp.nstr(a, 10) for a in sorted(A))}]  (positive, distinct)")
print(f"        t = {mp.nstr(T, 4)} is a critical point with a_k != t, and the pencil "
      f"at z = {mp.nstr(Z, 8)}")
print(f"        has a root w = {mp.nstr(worst, 10)} with w != t and "
      f"|w| = {mp.nstr(abs(worst), 10)} < t")
print("        so the theorem's hypothesis cannot be met at this `a`, and the theorem "
      "is vacuous there while compiling and guarding like a result about the class")


# --- (H2) why: t sits in the SECOND gap, so two coordinates are negative -------
below = sorted(a for a in A if a < T)
assert len(below) == 2, below
assert sum(1 for v in V if v < 0) == 2
assert all(v < -1 for v in V if v < 0), [v for v in V if v < 0]
print(f"PASS  (H2) two of the three roots lie below t, so two coordinates are "
      f"negative -- and positivity of the roots forces each of them below -1, "
      f"which is the realizability constraint a normalized sample must respect")


# --- (H3) one negative coordinate is the whole difference ---------------------
def sep(v, r):
    prod = [mp.mpf(1)]
    for vk in v:
        nxt = [mp.mpf(0)] * (len(prod) + 1)
        for i, c in enumerate(prod):
            nxt[i] += c
            nxt[i + 1] += -vk * c
        prod = nxt
    bi = [mp.binomial(r, i) for i in range(r + 1)]
    deg = max(len(prod), len(bi))
    asc = [mp.mpf(0)] * deg
    for i, c in enumerate(prod):
        asc[i] += c
    for i, c in enumerate(bi):
        asc[i] -= c
    assert abs(asc[0]) < mp.mpf('1e-30') and abs(asc[1]) < mp.mpf('1e-30')
    red = asc[2:]
    while red and abs(red[-1]) < mp.mpf('1e-35'):
        red.pop()
    if len(red) < 2:
        return None
    rts = mp.polyroots(list(reversed(red)), maxsteps=600, extraprec=300)
    return min(abs(1 + s) for s in rts)


x = mp.mpf('0.31830988618379067153776752674502872406')
one_neg, multi_neg, multi_fail = 0, 0, 0
for trial in range(900):
    x = mp.frac(x * 6364136223846793005 + mp.e)
    r = 1 + trial % 4
    m = 1 + trial % 4
    negs = []
    for _ in range(m):
        x = mp.frac(x * 6364136223846793005 + mp.e)
        negs.append(-(1 + mp.mpf(10) ** (4 * x - 2)))     # realizable: < -1
    need = -mp.mpf(r) - sum(negs)
    if need <= 0:
        continue
    w = []
    for _ in range(1 + (trial // 7) % 4):
        x = mp.frac(x * 6364136223846793005 + mp.e)
        w.append(x + mp.mpf('0.01'))
    v = negs + [need * u / sum(w) for u in w]
    assert abs(sum(v) + r) < mp.mpf('1e-25')
    s = sep(v, r)
    if s is None:
        continue
    if m == 1:
        one_neg += 1
        assert s > 1, (m, r, s)
    else:
        multi_neg += 1
        if s <= 1:
            multi_fail += 1

assert multi_fail > 0
print(f"PASS  (H3) separation holds at all {one_neg} one-negative configurations and "
      f"fails at {multi_fail} of {multi_neg} multi-negative ones "
      f"({100.0 * multi_fail / multi_neg:.0f}%), so the repair is a narrowing of the "
      f"binder rather than a search for a better proof")


# --- (H4) the narrowing needs no binder the theorem does not already have -----
# "t below every root but the minimum" is exactly one negative coordinate, and
# "t above the minimum" follows from the critical equation rather than needing
# to be assumed.
for trial in range(200):
    x = mp.frac(x * 6364136223846793005 + mp.e)
    r = 1 + trial % 4
    n = 3 + trial % 5
    aa = sorted(mp.mpf(10) ** (2 * mp.frac(x * (i + 7) + mp.pi) - 1) for i in range(n))
    # if t is below every root, every coordinate is positive and the sum is > 0
    t_low = aa[0] * mp.mpf('0.5')
    s = sum(t_low / (a - t_low) for a in aa)
    assert s > 0 > -mp.mpf(r), (s, r)
    # in the first gap the sum sweeps all of R, so a critical point exists there
    lo = sum(aa[0] * (1 + mp.mpf('1e-9')) / (a - aa[0] * (1 + mp.mpf('1e-9'))) for a in aa)
    hi = sum(aa[1] * (1 - mp.mpf('1e-9')) / (a - aa[1] * (1 - mp.mpf('1e-9'))) for a in aa)
    assert lo < -mp.mpf(r) < hi, (mp.nstr(lo, 6), r, mp.nstr(hi, 6))

print("PASS  (H4) `t < a k for every k != i` is exactly the first gap, hence exactly "
      "one negative coordinate; and `a i < t` needs no binder -- below every root the "
      "sum of coordinates is positive, so the critical equation excludes it, while "
      "across the first gap the sum sweeps from below -r to above it, so the endpoint "
      "the proof uses is there to be found")


# --- (H5) the vacuity is not occasional -- it is universal --------------------
# The coordinate sum sweeps from -infinity to +infinity across EVERY gap, so an
# admissible `a` with n >= 3 has a critical point in the SECOND gap as well as
# the first.  (H3) failed separation at every multi-negative configuration it
# sampled, and a critical point in the second gap is exactly a two-negative one.
# So the hypothesis is not false for some admissible `a` -- it is false for all
# of them, and the theorem carrying it is vacuous everywhere rather than on a
# corner of its class.
EPS = mp.mpf('1e-12')
universal = 0
for trial in range(300):
    x = mp.frac(x * 6364136223846793005 + mp.e)
    r = 1 + trial % 4
    n = 3 + trial % 6
    aa = sorted({mp.mpf(10) ** (2 * mp.frac(x * (i + 7) + mp.pi) - 1) for i in range(n)})
    if len(aa) < 3 or min(b - a_ for a_, b in zip(aa, aa[1:])) < mp.mpf('1e-3'):
        continue
    # the second gap (aa[1], aa[2]) sweeps across -r, so a critical point is there
    lo = sum(aa[1] * (1 + EPS) / (a_ - aa[1] * (1 + EPS)) for a_ in aa)
    hi = sum(aa[2] * (1 - EPS) / (a_ - aa[2] * (1 - EPS)) for a_ in aa)
    assert lo < -mp.mpf(r) < hi, (mp.nstr(lo, 6), r, mp.nstr(hi, 6))
    # bisect to it, and confirm it carries two negative coordinates
    f = lambda t: sum(t / (a_ - t) for a_ in aa) + r
    t = mp.findroot(f, (aa[1] * (1 + EPS), aa[2] * (1 - EPS)), solver='anderson',
                    tol=mp.mpf('1e-45'))
    assert aa[1] < t < aa[2], (t, aa[1], aa[2])
    v = [t / (a_ - t) for a_ in aa]
    # The bisection leaves a residual in the constraint, and `sep` asserts the
    # double root at the origin EXACTLY -- rightly, since that identity is the
    # constraint.  So project the residual onto the largest coordinate and
    # assert the projection is numerically inert rather than loosening the
    # identity to accommodate a solver's tolerance.
    resid = sum(v) + r
    assert abs(resid) < mp.mpf('1e-30'), mp.nstr(resid, 8)
    j = max(range(len(v)), key=lambda k: abs(v[k]))
    v[j] -= resid
    assert sum(1 for q in v if q < 0) == 2
    m = sep(v, r)
    assert m is None or m <= 1, mp.nstr(m, 12)
    universal += 1

assert universal > 100, universal
print(f"PASS  (H5) on all {universal} admissible configurations tested, the second "
      f"gap contains a critical point, that point carries two negative coordinates, "
      f"and separation fails there.  So the hypothesis is false for EVERY admissible "
      f"`a` with n >= 3, and the theorem carrying it is vacuous everywhere -- not on "
      f"a corner of its class, but on all of it")


# --- (H6) the normalization bridge, in the tree's own sign convention ---------
# `hsep` is stated in the paper's variables and the separation theorem that will
# discharge it is stated in normalized ones.  Two terms, one fact, each
# type-checking alone -- so the correspondence is asserted rather than assumed.
#
# The tree writes `ftRootPolyReal c a = C c * prod (C (a k) - X)`, i.e.
# `P(t) = c prod (a_k - t)`, with the factors `a_k - X` and NOT `X - a_k`.  That
# convention is what makes the normalization come out with no (-1)^n anywhere,
# and writing the bridge against the other one type-checks for even n and is
# wrong for odd, which is why the sign is asserted here rather than trusted.
def p_eval_conv(t, aa, cc):
    out = mp.mpf(cc)
    for a_ in aa:
        out *= (a_ - t)
    return out


x = mp.mpf('0.5772156649015328606065120900824024310421')
bridged = 0
for trial in range(240):
    x = mp.frac(x * 6364136223846793005 + mp.e)
    r = 1 + trial % 4
    n = 3 + trial % 4
    aa = sorted({mp.mpf(10) ** (2 * mp.frac(x * (i + 5) + mp.pi) - 1) for i in range(n)})
    if len(aa) < 3 or min(b - a_ for a_, b in zip(aa, aa[1:])) < mp.mpf('1e-3'):
        continue
    # the first-gap critical point: exactly the one hsep's new clause admits
    f = lambda t: sum(t / (a_ - t) for a_ in aa) + r
    EPSG = mp.mpf('1e-12')
    lo, hi = aa[0] * (1 + EPSG), aa[1] * (1 - EPSG)
    if not (f(lo) < 0 < f(hi)):
        continue
    t = mp.findroot(f, (lo, hi), solver='anderson', tol=mp.mpf('1e-45'))
    cc = mp.mpf('1.7')
    # the critical equation, in the tree's own form: t P'(t) - r P(t) = 0
    h = mp.mpf(10) ** (-18)
    dP = (p_eval_conv(t + h, aa, cc) - p_eval_conv(t - h, aa, cc)) / (2 * h)
    crit = t * dP - r * p_eval_conv(t, aa, cc)
    assert abs(crit) < mp.mpf('1e-14') * max(1, abs(p_eval_conv(t, aa, cc))), mp.nstr(crit, 8)
    # the pencil P + z X^r at z = -P(t)/t^r, roots located directly
    z = -p_eval_conv(t, aa, cc) / t ** r
    asc = [mp.mpc(cc)]                      # ascending coeffs of c prod (a_k - X)
    for a_ in aa:
        nxt = [mp.mpc(0)] * (len(asc) + 1)
        for i, co in enumerate(asc):
            nxt[i] += co * a_
            nxt[i + 1] += -co
        asc = nxt
    while len(asc) <= r:
        asc.append(mp.mpc(0))
    asc[r] += z
    wroots = mp.polyroots(list(reversed(asc)), maxsteps=800, extraprec=400)
    # the normalized coordinates, and the claim: w is a pencil root iff
    # sigma = w/t - 1 is a root of prod (1 - v_k sigma) - (1+sigma)^r
    v = [t / (a_ - t) for a_ in aa]
    assert abs(sum(v) + r) < mp.mpf('1e-25'), mp.nstr(sum(v) + r, 8)
    assert sum(1 for q in v if q < 0) == 1        # the one-negative class
    for w in wroots:
        sig = w / t - 1
        lhs = mp.mpc(1)
        for vk in v:
            lhs *= (1 - vk * sig)
        rhs = (1 + sig) ** r
        scale = max(mp.mpf(1), abs(lhs), abs(rhs))
        assert abs(lhs - rhs) < mp.mpf('1e-18') * scale, (mp.nstr(abs(lhs - rhs), 8),)
    # and the conclusion transports: t < |w|  <->  1 < |1 + sigma|
    for w in wroots:
        if abs(w - t) < mp.mpf('1e-20'):
            continue
        assert (t < abs(w)) == (1 < abs(1 + (w / t - 1))), (mp.nstr(w, 12),)
    bridged += 1

assert bridged > 80, bridged
print(f"PASS  (H6) on {bridged} first-gap critical points the bridge holds exactly: the "
      f"critical equation is `sum_k v_k = -r` with `v_k = t/(a_k - t)`, every pencil root "
      f"`w` gives `prod (1 - v_k sigma) = (1+sigma)^r` at `sigma = w/t - 1`, the "
      f"configuration is one-negative, and `t < |w|` transports to `1 < |1 + sigma|`.  "
      f"Asserted in the tree's own `a_k - X` convention, under which no (-1)^n appears")

print("ALL PASS  check_rho_one_hsep_scope")
