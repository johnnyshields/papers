#!/usr/bin/env python3
"""Paper section `sec:saturation-proof` (The repeated-block inverse);
result `thm:repeated-block-saturation`.

Test the REPEATED-BLOCK SATURATION theorem.

Claim.  Fix k >= 2 and 0 <= c < d.  Let A = (a_1,...,a_k ; c^{k-1}) be a
constant-gap inner diagram with a = a_1, b = a_k, I = (a_2,...,a_{k-1}),
subject to
    a, b > c + d,      a_i > max(2c, d)  for 2 <= i <= k-1.
Put z = a + b - d and
    A_m = A^{o_d m} = (a, I, (z,I)^{m-1}, b ; c^{m(k-1)}).
For a composition alpha with M = |alpha| >= 2 and length l,
    F_alpha = A_{alpha_1} ._d ... ._d A_{alpha_l}      ( ._d joins with gap d ).
Then against ARBITRARY connected skew diagrams
    Cl(F_alpha) = { F_beta, F_beta* : beta in R(alpha) },
with cardinality
    |Cl(F_alpha)| = |R(alpha)|   if A = A*,
                    2|R(alpha)|  otherwise.

The halving at a symmetric inner is the sharp, surprising part and is the main
target here: it predicts a DIFFERENT class size for two sources that differ only
in whether the inner block is palindromic.

Completeness of the class computation.  Row count is a Schur invariant, and for
every k the multiset of k-row overlaps is a Schur invariant
(Reiner-Shaw-van Willigenburg); k=1 gives the row-length multiset, k=2 the
adjacent-overlap multiset.  So every connected mate carries both multisets, and
enumerating their orderings yields a SUPERSET of the class, which filtering by
Jacobi-Trudi equality cuts down to the class exactly.  Not a sample.

Also tested: the parameter formulas (6), the literal geometric realization
F_alpha = alpha o_(d) A in attachment case (a), and the two stated boundaries --
M = 1 and d = c -- which must FAIL, or the hypotheses are not doing work.
"""

import importlib.util
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ENGINE = os.path.join(HERE, "_composition_engine.py")
spec = importlib.util.spec_from_file_location("eng", ENGINE)
E = importlib.util.module_from_spec(spec)
spec.loader.exec_module(E)

FAILURES = []


def fail(m):
    FAILURES.append(m)
    print("FAIL  " + m)


def build(L, g):
    return E.cells_from_rho_a(list(L), [x + 1 for x in g])


def prof(c):
    ri = E.row_intervals(c)
    if ri is None:
        return None
    idx = sorted(ri)
    if idx != list(range(idx[0], idx[0] + len(idx))):
        return None
    L = tuple(ri[i][1] - ri[i][0] + 1 for i in idx)
    g = tuple(min(ri[idx[t]][1], ri[idx[t + 1]][1])
              - max(ri[idx[t]][0], ri[idx[t + 1]][0]) for t in range(len(idx) - 1))
    return (L, g)


def schur(cells):
    return tuple(sorted(dict(E.jt_of_cells(cells)).items()))


def A_m(a, I, b, c, d, m):
    z = a + b - d
    L = (a,) + I
    for _ in range(m - 1):
        L = L + (z,) + I
    L = L + (b,)
    k = 2 + len(I)
    return L, (c,) * (m * (k - 1))


def F_alpha(a, I, b, c, d, alpha):
    L, g = (), ()
    for i, m in enumerate(alpha):
        Lm, gm = A_m(a, I, b, c, d, m)
        if i:
            g = g + (d,)
        L = L + Lm
        g = g + gm
    return L, g


def full_class(L, g):
    D = build(L, g)
    tgt = schur(D)
    n = len(L)
    out = set()
    cnt = 0
    for Lp in set(itertools.permutations(L)):
        for gp in set(itertools.permutations(g)):
            cnt += 1
            if any(gp[i] + 1 > min(Lp[i], Lp[i + 1]) for i in range(n - 1)):
                continue
            c2 = build(Lp, gp)
            if len(c2) != len(D) or not E.is_connected_skew(c2):
                continue
            if prof(c2) != (Lp, gp):
                continue
            if schur(c2) == tgt:
                out.add(E.normalize(c2))
    return out, cnt


def ribbon_class(alpha):
    M = sum(alpha)
    comps = []
    for kk in range(1, M + 1):
        for cut in itertools.combinations(range(1, M), kk - 1):
            pts = (0,) + cut + (M,)
            comps.append(tuple(pts[i + 1] - pts[i] for i in range(kk)))
    d = {}
    for b in comps:
        cells = E.cells_from_rho_a(list(b), [1] * (len(b) - 1))
        d.setdefault(schur(cells), []).append(b)
    for v in d.values():
        if tuple(alpha) in v:
            return v
    return [tuple(alpha)]


def is_selfrot(L, g):
    D = build(L, g)
    return E.normalize(D) == E.rotate(D)


print("=" * 78)
print("REPEATED-BLOCK SATURATION: is the class the outer ribbon class,")
print("and does a SYMMETRIC inner block halve it?")
print("=" * 78)

# (a, I, b, c, d)  with a,b > c+d and interior rows > max(2c,d)
CASES = [
    (4, (),   5, 1, 2, (1, 2)),   # k=2 asymmetric inner
    (4, (),   4, 1, 2, (1, 2)),   # k=2 SYMMETRIC inner  A=(4,4;1)
    (3, (),   5, 1, 2, (1, 2)),   # k=2 asymmetric
    (3, (),   3, 1, 2, (1, 2)),   # k=2 SYMMETRIC
    (4, (),   5, 0, 1, (1, 2)),   # c=0
    (4, (),   4, 0, 1, (1, 2)),   # c=0 SYMMETRIC
    (5, (),   6, 1, 3, (1, 2)),   # larger d
    (4, (),   5, 1, 2, (2, 1)),   # reversed outer
]

for (a, I, b, c, d, alpha) in CASES:
    k = 2 + len(I)
    if not (a > c + d and b > c + d and all(x > max(2 * c, d) for x in I)):
        print(f"\n-- ({a},{I},{b};c={c},d={d}) violates (1), skipped")
        continue
    M = sum(alpha)
    ell = len(alpha)
    L, g = F_alpha(a, I, b, c, d, alpha)
    Acells = build((a,) + I + (b,), (c,) * (k - 1))
    sym = E.normalize(Acells) == E.rotate(Acells)
    R = ribbon_class(alpha)
    pred = len(R) if sym else 2 * len(R)

    print(f"\n-- A=({a}{',' + str(I) if I else ''},{b}; {c}^{k-1})  d={d}  "
          f"alpha={alpha}  A symmetric: {sym}  |R(alpha)|={len(R)}")
    print(f"   F_alpha = {L} ; {g}")

    # parameter formulas (6)
    n_pred = M * (k - 1) + ell
    area_pred = M * (a + sum(I) + b) - (M - ell) * d
    D = build(L, g)
    ok_n = len(L) == n_pred
    ok_area = len(D) == area_pred
    print(f"   n={len(L)} (pred {n_pred})  area={len(D)} (pred {area_pred})  "
          f"{'ok' if ok_n and ok_area else '*** MISMATCH ***'}")
    if not (ok_n and ok_area):
        fail(f"A=({a},{b}) alpha={alpha}: parameter formula (6) wrong")

    if not E.is_connected_skew(D):
        fail(f"A=({a},{b}) alpha={alpha}: F_alpha not connected")
        continue

    cls, searched = full_class(L, g)
    tag = "ok " if len(cls) == pred else "*** MISMATCH ***"
    print(f"   |Cl| = {len(cls)}   predicted {pred}   {tag}   "
          f"(searched {searched})")
    if len(cls) != pred:
        fail(f"A=({a},{b};{c}) d={d} alpha={alpha}: |Cl|={len(cls)}, "
             f"predicted {pred} (sym={sym})")

    # is the class exactly the predicted set of F_beta and rotations?
    want = set()
    for beta in R:
        Lb, gb = F_alpha(a, I, b, c, d, beta)
        Db = build(Lb, gb)
        if E.is_connected_skew(Db):
            want.add(E.normalize(Db))
            want.add(E.rotate(Db))
    if cls != want:
        fail(f"A=({a},{b}) alpha={alpha}: class is not exactly "
             f"{{F_beta, F_beta*}} ({len(cls)} vs {len(want)})")
    else:
        print(f"   class is exactly {{F_beta, F_beta* : beta in R(alpha)}}")

# ---- the geometric realization: F_alpha = alpha o_(d) A, case (a) ---------
print("\n" + "-" * 78)
print("GEOMETRIC REALIZATION: is F_alpha literally alpha o_(d) A in case (a)?")
for (a, I, b, c, d, alpha) in CASES:
    k = 2 + len(I)
    # condition (1) is a HYPOTHESIS of the theorem; testing outside it is
    # testing nothing; (3,5) and (3,3), for example, violate a,b > c+d.
    if not (a > c + d and b > c + d and all(x > max(2 * c, d) for x in I)):
        continue
    Ac = build((a,) + I + (b,), (c,) * (k - 1))
    ribbon = E.cells_from_rho_a(list(alpha), [1] * (len(alpha) - 1))
    hit = None
    for (B, T, case, v, hv) in E.w_candidates(Ac, require_hyp_I=True):
        if len(B) != d:
            continue
        out = E.compose(ribbon, Ac, B, T, case, v)
        if out is None:
            continue
        if prof(out) == prof(build(*F_alpha(a, I, b, c, d, alpha))):
            hit = (case, len(B), hv)
            break
    if hit:
        print(f"   A=({a},{b};{c}) d={d} alpha={alpha}: reproduced by a legal "
              f"|W|={hit[1]} chart, case {hit[0]}, hypV={hit[2]}")
    else:
        print(f"   A=({a},{b};{c}) d={d} alpha={alpha}: NO legal |W|={d} chart "
              f"reproduced it")
        fail(f"geometric realization failed for A=({a},{b}) alpha={alpha}")

# ---- boundaries: both must FAIL or the hypotheses do nothing -------------
print("\n" + "-" * 78)
print("BOUNDARY CHECKS -- these must BREAK the conclusion")

print("\n  (i) d = c should let inner ambiguity survive")
# This needs an AMBIGUOUS inner block -- one that itself has a nonrotation
# mate.  A rigid two-row inner has no ambiguity for d=c to preserve, so
# probing with one tests nothing.  A_0 and A_1 below are the source's own pair.
A0 = ((4, 7, 4, 10, 7), (1, 1, 1, 1))
A1 = ((4, 10, 7, 4, 7), (1, 1, 1, 1))
amb = (schur(build(*A0)) == schur(build(*A1))
       and E.normalize(build(*A0)) != E.rotate(build(*A1))
       and E.normalize(build(*A0)) != E.normalize(build(*A1)))
print(f"      inner blocks A_0={A0[0]}, A_1={A1[0]} with gaps 1^4 are a "
      f"nonrotation equal pair: {amb}")
if not amb:
    fail("the stated ambiguous inner pair is not a nonrotation equality")


def join(L1, g1, L2, g2, dd):
    return L1 + L2, g1 + (dd,) + g2


surv = {}
for dd in (1, 2, 3):
    P = build(*join(A0[0], A0[1], A0[0], A0[1], dd))
    Q = build(*join(A1[0], A1[1], A1[0], A1[1], dd))
    same = schur(P) == schur(Q)
    rot = E.normalize(P) == E.rotate(Q) or E.normalize(P) == E.normalize(Q)
    surv[dd] = same and not rot
    rel = "d = c" if dd == 1 else "d > c"
    print(f"      {rel} (d={dd}, c=1): joined blocks Schur-equal and "
          f"nonrotation: {surv[dd]}")
if not surv[1]:
    fail("at d=c the inner ambiguity did NOT survive, contradicting (39)")
if surv[2] or surv[3]:
    fail("at d>c the inner ambiguity DID survive, so d>c is not sufficient")
if surv[1] and not surv[2] and not surv[3]:
    print("      => the d>c hypothesis is exactly what kills inner ambiguity")

print("\n  (ii) M = 1 should NOT force rigidity (F_(1) = A)")
for (a, I, b, c, d) in [(4, (), 5, 1, 2)]:
    L, g = F_alpha(a, I, b, c, d, (1,))
    Ac = build((a,) + I + (b,), (c,) * (1 + len(I)))
    same = E.normalize(build(L, g)) == E.normalize(Ac)
    print(f"      F_(1) equals A: {same}  (the theorem excludes M=1 for this "
          f"reason)")
    if not same:
        fail("F_(1) is not A, so the stated M=1 exception is mis-stated")

print("\n" + "=" * 78)
print(f"failures: {len(FAILURES)}")
print("RESULT: " + ("FAIL" if FAILURES else "ALL PASS"))
sys.exit(1 if FAILURES else 0)
