#!/usr/bin/env python3
"""Paper section `sec:inflation-proof` (The exact inflation threshold);
result `thm:sharp-inflation`.

Test the SHARP INFLATION-COLLAPSE claim.

Claim under test.  Fix 1 <= c < a < b, put p = a-c.  With
    E_m = (a, (a+b)^{m-1}, b ; c^m)                 (near-concatenation power)
    F_alpha = E_{alpha_1} . ... . E_{alpha_l}       ( . concatenates with gap 0 )
    I_t(D) = (L_1+t,...,L_n+t ; g_1+t,...,g_{n-1}+t)
the full connected Schur class satisfies
    |Cl(I_t F_alpha)| = 2 |R(alpha)|   for 0 <= t < p,
    |Cl(I_t F_alpha)| = 2              for t >= p,
where R(alpha) = { beta : r_beta = r_alpha }.  So the class survives whole below
the threshold and collapses to a rotation orbit at it, permanently.

HOW THE CLASS IS COMPUTED, and why the search is complete rather than a sample.
Two standard invariants bound any mate:
  - the row count is a Schur invariant;
  - for every k, the multiset of k-row overlaps is a Schur invariant
    (Reiner-Shaw-van Willigenburg), and k=1 gives the row-length multiset while
    k=2 gives the adjacent-overlap multiset.
So every connected mate of D has D's row-length multiset and D's adjacent-overlap
multiset.  Enumerating all orderings of those two multisets therefore enumerates a
SUPERSET of the class, and filtering by equality of the Jacobi-Trudi polynomial
gives the class exactly.  This is a complete determination, not a census.

The threshold is what is being tested, so nothing about p is assumed: the class
size is measured at every t from 0 upward and the first collapse is located.
"""

import importlib.util
import itertools
import os
import sys
from collections import defaultdict

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


def E_m(a, b, c, m):
    return ((a,) + (a + b,) * (m - 1) + (b,), (c,) * m)


def F_alpha(a, b, c, alpha):
    L, g = (), ()
    for i, m in enumerate(alpha):
        Lm, gm = E_m(a, b, c, m)
        if i:
            g = g + (0,)          # concatenation inserts a zero gap
        L = L + Lm
        g = g + gm
    return L, g


def inflate(L, g, t):
    return tuple(x + t for x in L), tuple(x + t for x in g)


def schur(cells):
    return tuple(sorted(dict(E.jt_of_cells(cells)).items()))


def full_class(L, g):
    """Every connected diagram with D's row multiset and overlap multiset whose
    Jacobi-Trudi polynomial equals D's.  Complete by the two invariants."""
    D = build(L, g)
    target = schur(D)
    n = len(L)
    out = set()
    seen_rows = set(itertools.permutations(L))
    seen_gaps = set(itertools.permutations(g))
    for Lp in seen_rows:
        for gp in seen_gaps:
            if any(gp[i] + 1 > min(Lp[i], Lp[i + 1]) for i in range(n - 1)):
                continue
            c2 = build(Lp, gp)
            if len(c2) != len(D) or not E.is_connected_skew(c2):
                continue
            if prof(c2) != (Lp, gp):
                continue
            if schur(c2) == target:
                out.add(E.normalize(c2))
    return out, len(seen_rows) * len(seen_gaps)


def ribbon_class_size(alpha):
    """|R(alpha)| = number of compositions with the same ribbon Schur function."""
    M = sum(alpha)
    comps = []
    for k in range(1, M + 1):
        for cut in itertools.combinations(range(1, M), k - 1):
            pts = (0,) + cut + (M,)
            comps.append(tuple(pts[i + 1] - pts[i] for i in range(k)))
    ribbon = {}
    for b in comps:
        L = tuple(b)
        g = (0,) * (len(b) - 1)
        cells = E.cells_from_rho_a(list(L), [1] * (len(b) - 1))
        ribbon.setdefault(schur(cells), []).append(b)
    for k, v in ribbon.items():
        if tuple(alpha) in v:
            return len(v), v
    return None, None


print("=" * 78)
print("SHARP INFLATION-COLLAPSE: does the class survive to t=p-1 and die at t=p?")
print("=" * 78)

CASES = [
    (2, 3, 1, (1, 2)),
    (2, 3, 1, (2, 1)),
    (3, 4, 1, (1, 2)),
    (2, 4, 1, (1, 2)),
    (3, 5, 2, (1, 2)),
    (2, 5, 1, (1, 2)),
    (3, 4, 2, (1, 2)),
    (2, 3, 1, (1, 3)),
]

for (a, b, c, alpha) in CASES:
    p = a - c
    rsize, rmembers = ribbon_class_size(alpha)
    L0, g0 = F_alpha(a, b, c, alpha)
    print(f"\n-- E=({a},{b};{c})  alpha={alpha}  p=a-c={p}  "
          f"|R(alpha)|={rsize} {rmembers}")
    print(f"   F_alpha = {L0} ; {g0}   area={sum(L0)}")
    predicted = {t: (2 * rsize if t < p else 2) for t in range(0, p + 3)}
    for t in range(0, p + 3):
        L, g = inflate(L0, g0, t)
        D = build(L, g)
        if not E.is_connected_skew(D):
            print(f"   t={t}: NOT CONNECTED, skipped")
            continue
        cls, searched = full_class(L, g)
        rot = {E.normalize(D), E.rotate(D)}
        pred = predicted[t]

        # SET-LEVEL, not merely cardinality: comparing sizes alone does
        # not establish
        #     Cl(I_t F_alpha) = I_t( Cl(F_alpha) )   for t < p.
        # Equal cardinality is compatible with the inflated class containing
        # some diagram that is not an inflate of an original member, so the
        # transport claim needs the set.
        if t < p:
            want = set()
            for beta in rmembers:
                Lb, gb = inflate(*F_alpha(a, b, c, beta), t)
                Db = build(Lb, gb)
                if E.is_connected_skew(Db):
                    want.add(E.normalize(Db))
                    want.add(E.rotate(Db))
        else:
            want = rot

        size_ok = len(cls) == pred
        set_ok = cls == want
        tag = "ok " if (size_ok and set_ok) else "*** MISMATCH ***"
        note = "rotation orbit only" if cls == rot else f"{len(cls)} members"
        print(f"   t={t}: |Cl| = {len(cls):2d}  predicted {pred:2d}  "
              f"set matches: {set_ok}  {tag}  "
              f"({note}; searched {searched} candidates)")
        if not size_ok:
            fail(f"E=({a},{b};{c}) alpha={alpha} t={t}: |Cl|={len(cls)}, "
                 f"predicted {pred}")
        if not set_ok:
            fail(f"E=({a},{b};{c}) alpha={alpha} t={t}: class is the right "
                 f"SIZE but not the predicted SET "
                 f"(|Cl|={len(cls)}, |want|={len(want)}, "
                 f"|Cl \\ want|={len(cls - want)})")

# ---- the paper's own smallest example, checked literally -------------------
print("\n" + "-" * 78)
print("THEIR SECTION 6 EXAMPLE, checked against the stated profiles and separator")
P = ((3, 4, 3, 6, 4), (2, 1, 2, 2))
Q = ((3, 6, 4, 3, 4), (2, 2, 1, 2))
L12, g12 = inflate(*F_alpha(2, 3, 1, (1, 2)), 1)
L21, g21 = inflate(*F_alpha(2, 3, 1, (2, 1)), 1)
print(f"  I_1 F_(1,2) = {L12};{g12}   claimed P = {P[0]};{P[1]}   "
      f"{'MATCH' if (L12, g12) == P else '*** MISMATCH ***'}")
print(f"  I_1 F_(2,1) = {L21};{g21}   claimed Q = {Q[0]};{Q[1]}   "
      f"{'MATCH' if (L21, g21) == Q else '*** MISMATCH ***'}")
if (L12, g12) != P or (L21, g21) != Q:
    fail("the section 6 profiles do not match the construction")

cP, cQ = build(*P), build(*Q)
eq = schur(cP) == schur(cQ)
print(f"  s_P == s_Q : {eq}   (the claim is that inflation SEPARATED them)")
if eq:
    fail("P and Q are still Schur-equal at t=1: no collapse")
else:
    print("  => collapse confirmed at t = 1 = p")

dP = dict(E.jt_of_cells(cP))
dQ = dict(E.jt_of_cells(cQ))
mono = tuple(sorted((9, 6, 3, 2), reverse=True))
gp = next((v for k, v in dP.items() if tuple(sorted(k, reverse=True)) == mono), 0)
gq = next((v for k, v in dQ.items() if tuple(sorted(k, reverse=True)) == mono), 0)
print(f"  [h_2 h_3 h_6 h_9] s_P = {gp}   claimed -1")
print(f"  [h_2 h_3 h_6 h_9] s_Q = {gq}   claimed  0")
if (gp, gq) != (-1, 0):
    fail(f"separator coefficients are ({gp},{gq}), claimed (-1,0)")


def negdata(cells):
    lam, mu = E.lam_mu_of(cells)
    n = len(lam)
    mu = list(mu) + [0] * (n - len(mu))
    b = [sum(1 for j in range(n) if lam[i] - mu[j] - i + j < 0) for i in range(n)]
    return sum(b), tuple(b)


for nm, cc, want in (("P", cP, (0, 0, 1, 1, 3)), ("Q", cQ, (0, 0, 1, 2, 2))):
    nu, mask = negdata(cc)
    ok = (len(cc) == 20 and nu == 5 and mask == want)
    print(f"  {nm}: area={len(cc)} nu={nu} mask={mask}  claimed area=20 nu=5 "
          f"mask={want}  {'ok' if ok else '*** MISMATCH ***'}")
    if not ok:
        fail(f"{nm} area/nu/mask disagree with section 6")

# ---- control: the threshold must actually bite somewhere ------------------
print("\n-- control --")
L0, g0 = F_alpha(3, 5, 2, (1, 2))     # p = 1
c0, _ = full_class(L0, g0)
c1, _ = full_class(*inflate(L0, g0, 1))
if len(c0) <= len(c1):
    fail(f"control did not fire: class did not shrink ({len(c0)} -> {len(c1)})")
else:
    print(f"  control fires: |Cl| drops {len(c0)} -> {len(c1)} across t=0 -> 1")

print("\n" + "=" * 78)
print(f"failures: {len(FAILURES)}")
print("RESULT: " + ("FAIL" if FAILURES else "ALL PASS"))
sys.exit(1 if FAILURES else 0)
