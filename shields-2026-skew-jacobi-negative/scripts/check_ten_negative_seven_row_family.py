#!/usr/bin/env python3
"""Verify the proposed NEW seven-row exceptional family at ten negatives.

Claim under test, in the profile convention (rows ; adjacent overlap MINUS one):

  F_B = (a+d, b+d, a+b+d, 2b+d, a+2b+d, a+2b+d, 3b+d ;
             d, a+d, b+d, a+b+d, a+b+d, 2b+d)
  H_B = (a+d, b+d, a+b+d, 2b+d, a+2b+d, 3b+d, a+2b+d ;
             d, a+d, b+d, a+b+d, 2b+d, a+b+d)

with rho(F_B) = (3,3,2,1,1) and rho(H_B) = (4,2,2,1,1), both nu = 10 and
n_min = 7, common area 4a + 11b + 7d, and Cl(F_B) = {F_B, F_B*, H_B, H_B*}.

The proposed legal factorization is

  D_B = (2,3,3,3; 1,2,2),   E = (a+d, b+d; d),   W = (a+d),   case (c),

with Wsw = the first A cells of row 1 and Wne = row 0, where A = a+d.

Why this matters beyond one more family.  The four members do NOT share a
negative shape: rho(F_B) and rho(H_B) differ, and rotation conjugates each.
So a single Schur equality class SPANS several negative-shape strata.  That is
exactly the configuration a stratum-local classification cannot see, and it is
checked explicitly below rather than assumed.

The chart is submitted to the engine for judgement: it must appear in
w_candidates(E, require_hyp_I=True), the engine's attachment case must be (c),
and compose() must return F_B and H_B.
"""

import importlib.util
import os
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ENGINE = os.path.join(HERE, "check_composition_irreducibility.py")
spec = importlib.util.spec_from_file_location("eng", ENGINE)
E = importlib.util.module_from_spec(spec)
spec.loader.exec_module(E)

FAILURES = []
CHECKED = 0


def fail(m):
    FAILURES.append(m)
    print("FAIL  " + m)


def build(L, g):
    return E.cells_from_rho_a(list(L), [x + 1 for x in g])


def negshape(cells):
    """(nu, rho) with rho the negative partition of the full JT board."""
    lam, mu = E.lam_mu_of(cells)
    n = len(lam)
    mu = list(mu) + [0] * (n - len(mu))
    b = [sum(1 for j in range(n) if lam[i] - mu[j] - i + j < 0) for i in range(n)]
    rho = tuple(x for x in sorted(b, reverse=True) if x > 0)
    return sum(b), rho


def conj(r):
    return tuple(sum(1 for x in r if x > j) for j in range(r[0])) if r else ()


def nmin(r):
    return 1 + max(x + (i + 1) for i, x in enumerate(r)) if r else 0


def FB(a, b, d):
    return ((a + d, b + d, a + b + d, 2 * b + d, a + 2 * b + d,
             a + 2 * b + d, 3 * b + d),
            (d, a + d, b + d, a + b + d, a + b + d, 2 * b + d))


def HB(a, b, d):
    return ((a + d, b + d, a + b + d, 2 * b + d, a + 2 * b + d,
             3 * b + d, a + 2 * b + d),
            (d, a + d, b + d, a + b + d, 2 * b + d, a + b + d))


print("=" * 78)
print("THE TEN-NEGATIVE SEVEN-ROW FAMILY")
print("=" * 78)

# domain: legality needs beta = b-1 >= A = a+d (Hyp I) and b-a-d+1 >= 2 (Hyp II)
DOM = [(a, b, d) for a in range(1, 7) for d in range(0, 5)
       for b in range(a + d + 1, a + d + 9)]

print(f"\n-- 1. shape, negative count and area over {len(DOM)} parameter points --")
nrows = set()
nus = set()
rhoF = set()
rhoH = set()
area_ok = 0
for (a, b, d) in DOM:
    CHECKED += 1
    F = build(*FB(a, b, d))
    H = build(*HB(a, b, d))
    if not (E.is_connected_skew(F) and E.is_connected_skew(H)):
        fail(f"(a,b,d)=({a},{b},{d}): not connected")
        continue
    nrows.add(len(set(i for i, _ in F)))
    nrows.add(len(set(i for i, _ in H)))
    nuF, rF = negshape(F)
    nuH, rH = negshape(H)
    nus.add(nuF)
    nus.add(nuH)
    rhoF.add(rF)
    rhoH.add(rH)
    if len(F) == 4 * a + 11 * b + 7 * d and len(H) == len(F):
        area_ok += 1
    else:
        fail(f"(a,b,d)=({a},{b},{d}): area {len(F)}/{len(H)}, "
             f"formula gives {4*a+11*b+7*d}")
print(f"  row counts observed: {sorted(nrows)}")
print(f"  negative counts observed: {sorted(nus)}")
print(f"  rho(F_B) observed: {sorted(rhoF)}")
print(f"  rho(H_B) observed: {sorted(rhoH)}")
print(f"  area = 4a+11b+7d at {area_ok}/{len(DOM)} points")
if sorted(nrows) != [7]:
    fail(f"row count is not constantly 7: {sorted(nrows)}")
if sorted(nus) != [10]:
    fail(f"negative count is not constantly 10: {sorted(nus)}")
if rhoF != {(3, 3, 2, 1, 1)}:
    fail(f"rho(F_B) is not (3,3,2,1,1): {sorted(rhoF)}")
if rhoH != {(4, 2, 2, 1, 1)}:
    fail(f"rho(H_B) is not (4,2,2,1,1): {sorted(rhoH)}")

print("\n-- 2. the equality, and that it is a genuine nonrotation class --")
eq = 0
for (a, b, d) in DOM:
    CHECKED += 1
    F = build(*FB(a, b, d))
    H = build(*HB(a, b, d))
    if dict(E.jt_of_cells(F)) != dict(E.jt_of_cells(H)):
        fail(f"(a,b,d)=({a},{b},{d}): s_F != s_H")
        continue
    if E.normalize(F) == E.normalize(H) or E.normalize(F) == E.rotate(H):
        fail(f"(a,b,d)=({a},{b},{d}): F and H are equal or a rotation pair")
        continue
    if len({E.normalize(F), E.rotate(F), E.normalize(H), E.rotate(H)}) != 4:
        fail(f"(a,b,d)=({a},{b},{d}): the four members are not distinct")
        continue
    eq += 1
print(f"  s_F = s_H, nonrotation, four distinct members: {eq}/{len(DOM)}")

print("\n-- 3. THE CLASS SPANS SEVERAL NEGATIVE-SHAPE STRATA --")
CHECKED += 1
a, b, d = 2, 5, 1
F = build(*FB(a, b, d))
H = build(*HB(a, b, d))
members = {"F_B": F, "F_B*": E.rotate(F), "H_B": H, "H_B*": E.rotate(H)}
shapes = {}
for name, c in members.items():
    nu, r = negshape(c)
    shapes[name] = r
    print(f"    {name:5s}  nu={nu}  rho={r}  n_min={nmin(r)}")
distinct = set(shapes.values())
print(f"  distinct negative shapes inside ONE Schur class: {len(distinct)}")
if len(distinct) < 2:
    fail("the four members share one negative shape -- the spanning claim fails")
else:
    print("  => a stratum-local classification cannot see this class whole")
CHECKED += 1
if conj(shapes["F_B"]) != shapes["F_B*"] or conj(shapes["H_B"]) != shapes["H_B*"]:
    fail("rho(D*) = rho(D)' fails on this family")
else:
    print(f"  rho(D*) = rho(D)' holds: {shapes['F_B']}' = {shapes['F_B*']}, "
          f"{shapes['H_B']}' = {shapes['H_B*']}")

print("\n-- 4. the proposed factorization, engine as judge --")
DB = build((2, 3, 3, 3), (1, 2, 2))
DBs = E.rotate(DB)
good = 0
for (a, b, d) in DOM:
    CHECKED += 1
    A = a + d
    B = b + d
    beta = b - 1
    Ec = E.normalize(frozenset((0, j) for j in range(beta, beta + A))
                     | frozenset((1, j) for j in range(0, B)))
    if Ec != build((A, B), (d,)):
        fail(f"(a,b,d)=({a},{b},{d}): E cells disagree with profile (A,B;d)")
        continue
    # Wsw = first A cells of the bottom row; Wne = the whole top row
    ri = E.row_intervals(Ec)
    lo1 = ri[1][0]
    lo0, hi0 = ri[0]
    Wsw = frozenset((1, lo1 + j) for j in range(A))
    Wne = frozenset((0, j) for j in range(lo0, hi0 + 1))
    hit = None
    for (Bc, T, case, v, hv) in E.w_candidates(Ec, require_hyp_I=True):
        if frozenset(Bc) == Wsw and frozenset(T) == Wne:
            hit = (case, v)
            break
    if hit is None:
        fail(f"(a,b,d)=({a},{b},{d}): chart NOT in the engine's legal I-IV list")
        continue
    case, v = hit
    if case != 'c':
        fail(f"(a,b,d)=({a},{b},{d}): engine case {case}, claim (c)")
        continue
    got = E.compose(DB, Ec, Wsw, Wne, case, v)
    gotH = E.compose(DBs, Ec, Wsw, Wne, case, v)
    wantF = build(*FB(a, b, d))
    wantH = build(*HB(a, b, d))
    if got is None or E.normalize(got) != E.normalize(wantF):
        fail(f"(a,b,d)=({a},{b},{d}): D_B o_W E != F_B")
        continue
    if gotH is None or E.normalize(gotH) not in (E.normalize(wantH),
                                                 E.rotate(wantH)):
        fail(f"(a,b,d)=({a},{b},{d}): D_B* o_W E is neither H_B nor H_B*")
        continue
    good += 1
print(f"  legal case-(c) chart reproducing F_B and H_B: {good}/{len(DOM)}")

print("\n-- controls (each must fire) --")
CHECKED += 1
pert = list(FB(2, 5, 1)[1])
pert[3] += 1
if dict(E.jt_of_cells(build(FB(2, 5, 1)[0], tuple(pert)))) == \
   dict(E.jt_of_cells(build(*HB(2, 5, 1)))):
    fail("control did not fire: a perturbed gap still gives the equality")
else:
    print("  perturbed-gap control fires")

CHECKED += 1
bad = 0
for (a, b, d) in DOM[:12]:
    A = a + d
    Ec = build((A, b + d), (d,))
    ri = E.row_intervals(Ec)
    Wsw = frozenset((1, ri[1][0] + j) for j in range(A - 1))   # too small
    Wne = frozenset((0, j) for j in range(ri[0][0], ri[0][1]))
    if not any(frozenset(Bc) == Wsw and frozenset(T) == Wne
               for (Bc, T, c_, v_, h_) in E.w_candidates(Ec, require_hyp_I=True)):
        bad += 1
if bad == 0:
    fail("control did not fire: a truncated W was accepted as legal")
else:
    print(f"  truncated-W control fires at {bad}/12 probes")

CHECKED += 1
if len(DOM) < 100:
    fail(f"non-vacuity: only {len(DOM)} parameter points")
else:
    print(f"  non-vacuity: {CHECKED} checks over {len(DOM)} parameter points")

print("\n" + "=" * 78)
print(f"checks run: {CHECKED}   failures: {len(FAILURES)}")
print("RESULT: " + ("FAIL" if FAILURES else "ALL PASS"))
sys.exit(1 if FAILURES else 0)
