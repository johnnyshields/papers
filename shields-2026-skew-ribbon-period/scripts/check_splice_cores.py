r"""Paper section `app:coincident` (Positive coincident attachment phases).

Set identities of the two splices of a coincident source.

Paper: app:coincident, lem:coincident-reader (eq:coincident-full-flags): the first window
(rows: contact row r g + tau and the parent rows up to r g + u; columns: parent columns up to
r g + u) and the last window (rows: parent rows >= B g shifted down by B g; columns: tau and the
parent columns >= B g shifted) have the same zero-free core, and every unit on which they differ is
a private position strictly between the contacts tau and r g + tau.

The parent is synthetic: literal marked windows J, K (tau in neither), the extra top mark row
L g + tau and bottom mark column tau, and private records whose row-only / column-only status is
the same in every band while the units (both or neither) vary freely.  Mirrors `SpliceParent`,
`core_eq` and `diff_units` in `SkewRibbonPeriod/Coincident/Clock/SpliceCore.lean`.
"""
import random

random.seed(20260101)


def build(g, u, r, B, tau, J, K, status, units):
    L = r + B
    rows, cols = set(), set()
    for i in range(L + 1):
        for d in J:
            rows.add(i * g + d)
        for d in K:
            cols.add(i * g + d)
    rows.add(L * g + tau)
    cols.add(tau)
    for i in range(L):
        for d in range(u + 1, g):
            s = status[d]
            if s == "row":
                rows.add(i * g + d)
            elif s == "col":
                cols.add(i * g + d)
            elif units[(i, d)]:
                rows.add(i * g + d)
                cols.add(i * g + d)
    return rows, cols


def windows(rows, cols, g, u, r, B, tau):
    m = r * g + u
    rc = r * g + tau
    s = B * g
    rowsE = {rc} | {x for x in rows if x <= m}
    colsE = {y for y in cols if y <= m}
    rowsF = {x - s for x in rows if x >= s}
    colsF = {tau} | {y - s for y in cols if y >= s}
    return rowsE, colsE, rowsF, colsF


def check(g, u, r, B, tau):
    J = {u} | {d for d in range(1, u) if d != tau and random.random() < 0.5}
    K = {0} | {d for d in range(1, u) if d != tau and random.random() < 0.5}
    status = {d: random.choice(["row", "col", "none"]) for d in range(u + 1, g)}
    units = {(i, d): random.random() < 0.5 for i in range(r + B) for d in range(u + 1, g)}
    rows, cols = build(g, u, r, B, tau, J, K, status, units)
    rE, cE, rF, cF = windows(rows, cols, g, u, r, B, tau)
    assert rF - cF == rE - cE, (g, u, r, B, tau)
    assert cF - rF == cE - rE, (g, u, r, B, tau)
    ZE, ZF = rE & cE, rF & cF
    rc = r * g + tau
    for z in ZE ^ ZF:
        assert tau < z < rc, (z, tau, rc)
    return len(ZE ^ ZF)


diff = 0
runs = 0
for g in range(4, 9):
    for u in range(3, g):
        for tau in range(1, u):
            for r in range(1, 5):
                for B in range(1, 4):
                    for _ in range(5):
                        diff += check(g, u, r, B, tau)
                        runs += 1
assert diff > 0
print(f"splice cores: {runs} sources, {diff} differing units, all strictly between the contacts")
