#!/usr/bin/env python3
"""Which board statistics are constant on a skew Schur equality class?

The ten-negative seven-row family showed one class carrying FOUR distinct
negative shapes, all at nu = 10.  That kills rho as a class invariant and
raises the question the paper actually depends on: is the negative COUNT nu
class-invariant in general, or did it merely happen to be constant there?

The paper stratifies by nu.  If nu is not class-invariant, a class can straddle
two strata and a stratum-local classification is incomplete by construction --
not as a technicality but at its foundation.  So this is checked directly,
over every connected skew diagram to a cell cap, rather than inferred.

Candidate statistics, each tested for constancy across a full Schur class:

    rows            number of nonempty rows
    cols            number of nonempty columns
    nu              full-board Jacobi-Trudi negative count
    rho             the negative partition itself
    rowmult         multiset of row lengths
    colmult         multiset of column lengths
    nmin            1 + max_i(rho_i + i), the minimum realizing row count
    area            cell count

A statistic that varies on even one class is not an invariant, and the witness
is printed.  A statistic constant on every class here is a CANDIDATE invariant
on this range -- never a theorem, and the range is stated with the verdict.
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

CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 12


def stats(cells):
    lam, mu = E.lam_mu_of(cells)
    n = len(lam)
    mu2 = list(mu) + [0] * (n - len(mu))
    b = [sum(1 for j in range(n) if lam[i] - mu2[j] - i + j < 0) for i in range(n)]
    rho = tuple(x for x in sorted(b, reverse=True) if x > 0)
    nmin = 1 + max(x + (i + 1) for i, x in enumerate(rho)) if rho else 0
    ri = E.row_intervals(cells)
    rowmult = tuple(sorted(ri[i][1] - ri[i][0] + 1 for i in ri))
    cols = defaultdict(int)
    for _, j in cells:
        cols[j] += 1
    colmult = tuple(sorted(cols.values()))
    return dict(rows=len(set(i for i, _ in cells)),
                cols=len(cols),
                nu=sum(b),
                rho=rho,
                rowmult=rowmult,
                colmult=colmult,
                nmin=nmin,
                area=len(cells))


print("=" * 78)
print(f"CLASS INVARIANTS OF SKEW SCHUR EQUALITY, all connected diagrams to {CAP} cells")
print("=" * 78)

classes = defaultdict(list)
total = 0
for cells in E.shapes_upto(CAP):
    if not E.is_connected_skew(cells):
        continue
    total += 1
    key = tuple(sorted(dict(E.jt_of_cells(cells)).items()))
    classes[key].append(cells)

multi = {k: v for k, v in classes.items() if len(v) > 1}
nontriv = {}
for k, v in multi.items():
    orbit = {E.normalize(v[0]), E.rotate(v[0])}
    if any(E.normalize(c) not in orbit for c in v):
        nontriv[k] = v

print(f"\n  {total} connected diagrams in {len(classes)} Schur classes")
print(f"  {len(multi)} classes with more than one member")
print(f"  {len(nontriv)} NONROTATION classes (a member outside the first member's "
      f"rotation orbit)")

FIELDS = ["rows", "cols", "nu", "rho", "rowmult", "colmult", "nmin", "area"]
varies = defaultdict(list)
for k, members in multi.items():
    st = [stats(c) for c in members]
    for f in FIELDS:
        vals = {s[f] for s in st}
        if len(vals) > 1:
            varies[f].append((members, sorted(vals, key=repr)))

print(f"\n{'statistic':10s}  {'verdict':28s}  witness")
print("-" * 78)
for f in FIELDS:
    if not varies[f]:
        print(f"{f:10s}  CONSTANT on every class      --")
    else:
        members, vals = varies[f][0]
        m0 = sorted(members[0])
        print(f"{f:10s}  VARIES on {len(varies[f])} class(es)".ljust(42)
              + f"{vals[0]} vs {vals[1]}")

print("\n-- the classes where the negative SHAPE varies --")
if varies["rho"]:
    print(f"  {len(varies['rho'])} classes carry more than one negative shape")
    for members, vals in varies["rho"][:3]:
        prof = []
        for c in members:
            ri = E.row_intervals(c)
            L = tuple(ri[i][1] - ri[i][0] + 1 for i in sorted(ri))
            prof.append(L)
        print(f"    rows={stats(members[0])['rows']} area={len(members[0])} "
              f"nu={stats(members[0])['nu']}  shapes={vals}")
        print(f"      member row words: {prof}")
else:
    print("  none in this range -- the four-shape family lies above the cap")

print("\n-- controls (each must fire) --")
bad = 0
if len(multi) < 50:
    print(f"FAIL  non-vacuity: only {len(multi)} multi-member classes")
    bad += 1
else:
    print(f"  non-vacuity: {len(multi)} multi-member classes, "
          f"{len(nontriv)} of them nonrotation")

# a statistic that is NOT expected to be invariant, as a firing control
ctl = 0
for k, members in multi.items():
    vals = {tuple(sorted(c)) for c in members}
    if len(vals) > 1:
        ctl += 1
if ctl == 0:
    print("FAIL  control did not fire: the literal cell set never varies, "
          "so classes are singletons and nothing is being tested")
    bad += 1
else:
    print(f"  literal-cell-set control fires on {ctl} classes "
          f"(members really are different diagrams)")

print("\n" + "=" * 78)
print("RESULT: " + ("FAIL" if bad else "ALL PASS")
      + f"   (range: connected, area <= {CAP})")
sys.exit(1 if bad else 0)
