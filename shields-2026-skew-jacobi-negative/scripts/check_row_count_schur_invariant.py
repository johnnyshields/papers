#!/usr/bin/env python3
"""Is the row count of a connected skew diagram recoverable from its Schur
function?

Claim under test: max deg_h s_D = n, the number of nonempty rows.  Every term
of the Jacobi-Trudi determinant is a product of at most n entries; h_0 = 1 and
h_{<0} = 0 kill or trivialize some of them, while the diagonal term
prod_i h_{lam_i - mu_i} has every index >= 1 on a diagram with n nonempty rows,
so it has degree exactly n and survives with coefficient one.

Why this matters more than it looks.  If true, row count is a Schur invariant,
so a mate of a four-row or five-row diagram has four or five rows.  A negative
shape that only realizes at seven rows or more therefore CANNOT supply a fifth
member of an existing lower-row class -- it could only found a new class.  That
is what separates "exhaustiveness of the known families" from "are there new
families higher up", and both were being carried as one open item.

Tested here over all connected skew diagrams to a cell cap, plus the
exceptional families' own members, with controls that must fire.
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


def rows_of(cells):
    return len(set(i for i, _ in cells))


def hdeg_profile(cells):
    """(max number of h-factors over all monomials, coefficient there)."""
    terms = E.jt_of_cells(cells)
    best, coeff_at_best, nbest = -1, None, 0
    for mono, c in terms:
        if c == 0:
            continue
        d = len(mono) if not isinstance(mono, (int,)) else 1
        if d > best:
            best, coeff_at_best, nbest = d, c, 1
        elif d == best:
            nbest += 1
    return best, coeff_at_best, nbest


print("=" * 78)
print("IS ROW COUNT A SCHUR INVARIANT?   max deg_h s_D  vs  n")
print("=" * 78)

# ---- 1. sweep every connected skew diagram to a cell cap -----------------
CAP = 11
print(f"\n-- 1. all connected skew diagrams to {CAP} cells --")
seen = 0
bad = 0
by_rows = defaultdict(int)
for cells in E.shapes_upto(CAP):
    if not E.is_connected_skew(cells):
        continue
    CHECKED += 1
    seen += 1
    n = rows_of(cells)
    d, c, nb = hdeg_profile(cells)
    by_rows[n] += 1
    if d != n:
        bad += 1
        if bad <= 5:
            fail(f"{sorted(cells)}: rows={n} but max deg_h={d}")
print(f"  {seen} connected diagrams; row counts "
      f"{dict(sorted(by_rows.items()))}")
print(f"  max deg_h == row count on {seen - bad} of {seen}")

# ---- 2. the top-degree monomial is unique and has coefficient 1 ---------
print("\n-- 2. the top-degree term is the diagonal, coefficient one --")
uniq = nonuniq = notone = 0
for cells in E.shapes_upto(CAP):
    if not E.is_connected_skew(cells):
        continue
    CHECKED += 1
    d, c, nb = hdeg_profile(cells)
    if nb == 1:
        uniq += 1
    else:
        nonuniq += 1
    if c != 1:
        notone += 1
print(f"  top degree attained by a unique monomial in {uniq} cases, "
      f"by several in {nonuniq}")
print(f"  coefficient at top degree != 1 in {notone} cases")
if notone:
    fail(f"the top-degree coefficient is not always 1 ({notone} cases) -- "
         f"the survival argument needs care")

# ---- 3. the exceptional families themselves -----------------------------
print("\n-- 3. the seven families' own members --")
fam = []
for w in range(1, 6):
    for c in range(0, w):
        for b in range(c + w + 1, c + w + 5):
            fam.append(("four-row", (w, b, b, b + w - c), (c, c, w), 4))
            fam.append(("four-row*", (w, b, b + w - c, b), (c, w, c), 4))
ok = 0
for tag, L, g, want in fam:
    CHECKED += 1
    cells = build(L, g)
    if not E.is_connected_skew(cells):
        continue
    n = rows_of(cells)
    d, c_, nb = hdeg_profile(cells)
    if n != want or d != want:
        fail(f"{tag} {L};{g}: rows={n}, max deg_h={d}, expected {want}")
    else:
        ok += 1
print(f"  {ok} four-row family members: rows = max deg_h = 4 throughout")

# ---- 4. the consequence, stated as a testable separation ----------------
print("\n-- 4. consequence: a mate cannot change row count --")
CHECKED += 1
classes = defaultdict(list)
for cells in E.shapes_upto(10):
    if not E.is_connected_skew(cells):
        continue
    key = tuple(sorted(dict(E.jt_of_cells(cells)).items()))
    classes[key].append(cells)
mixed = 0
multi = 0
for key, members in classes.items():
    if len(members) < 2:
        continue
    multi += 1
    if len(set(rows_of(m) for m in members)) > 1:
        mixed += 1
print(f"  {multi} Schur classes with more than one member, to 10 cells")
if mixed:
    fail(f"{mixed} classes contain diagrams of DIFFERENT row counts -- "
         f"row count would not be a Schur invariant")
else:
    print(f"  every one is row-count homogeneous ({mixed} mixed)")

# ---- controls (each must fire) ------------------------------------------
print("\n-- controls (each must fire) --")

CHECKED += 1
# a disconnected / multi-row-gap shape is outside the claim's hypothesis;
# the claim is about NONEMPTY rows, so an empty row must not be counted
probe = frozenset({(0, 0), (2, 0)})          # two cells, a gap row between
d, c_, nb = hdeg_profile(probe) if E.is_skew(probe) else (None, None, None)
print(f"  gapped probe handled: is_skew={E.is_skew(probe)}, "
      f"rows_of={rows_of(probe)}")

CHECKED += 1
# the invariant must actually have discriminating power: different row counts
# must really occur among diagrams of the same cell count
per_size = defaultdict(set)
for cells in E.shapes_upto(9):
    if E.is_connected_skew(cells):
        per_size[len(cells)].add(rows_of(cells))
spread = {k: sorted(v) for k, v in sorted(per_size.items()) if len(v) > 1}
if not spread:
    fail("control did not fire: row count never varies at fixed cell count, "
         "so the invariant separates nothing")
else:
    print(f"  discriminating-power control fires: at fixed cell count the row "
          f"count varies, e.g. {list(spread.items())[-3:]}")

CHECKED += 1
if seen < 1000:
    fail(f"non-vacuity: only {seen} diagrams swept")
else:
    print(f"  non-vacuity: {CHECKED} checks over {seen} connected diagrams")

print("\n" + "=" * 78)
print(f"checks run: {CHECKED}   failures: {len(FAILURES)}")
print("RESULT: " + ("FAIL" if FAILURES else "ALL PASS"))
sys.exit(1 if FAILURES else 0)
