#!/usr/bin/env python3
"""Construct diagrams with at least 16 Schur-equal members.

Take each member of an eight-member nonrotation class from the census (r = 3) as the outer D and
each marked inner (E, W) with E != E* and period q <= QMAX, built from connected inners of at
most EMAX cells.  Every factor reversal of D o_W E is Schur-equal to it (sufficiency, Olson-Harris
Thm 5.3.10), and D ranges over a class of 8, so the 16 diagrams D' o_W E and D' o_{W*} E* are
Schur-equal.  Report the smallest area at which all 16 are distinct.
"""
import hashlib, importlib.util, json, sys
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PIN = HERE.parent / 'census-rs' / '_pinned'
SNAP = json.loads((PIN / 'snapshot.json').read_bytes())
def load(n):
    p = PIN / n
    assert hashlib.sha256(p.read_bytes()).hexdigest() == SNAP['files'][n]['sha256']
    s = importlib.util.spec_from_file_location('pin_' + p.stem, p); m = importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
C = load('skew_core.py'); K = load('skew_compose.py')
EMAX, QMAX = 6, 3
eights = []
for a in range(1, 34):
    d = json.loads((HERE.parent / 'census-rs' / 'results' / f'area-{a:02}.json').read_bytes())
    eights += [[C.cells((tuple(p[0]), tuple(p[1]))) for p in cl] for cl in d['nonrotation'] if len(cl) == 8]
assert len(eights) == 34
inners = []
for n in range(2, EMAX + 1):
    for F in C.all_profiles(n):
        E = C.cells(F)
        if K.rotate(E) == E:
            continue
        for (B, T, case, v, q) in K.marks(E):
            if q <= QMAX:
                inners.append((E, B, T, case, v, q))
best = None
for cl in sorted(eights, key=lambda c: len(next(iter(c)))):
    for (E, B, T, case, v, q) in inners:
        Er, Br, Tr, cr, vr = K.rotate_mark(E, B, T, case, v)
        V = set()
        for D in cl:
            V.add(K.compose(D, E, B, T, case, v)); V.add(K.compose(D, Er, Br, Tr, cr, vr))
        if len(V) == 16 and all(K.is_connected_skew(F) for F in V):
            area = len(next(iter(V)))
            if best is None or area < best[0]:
                best = (area, C.fmt(C.profile_of_cells(next(iter(cl)))), C.fmt(C.profile_of_cells(E)), case, q)
assert best is not None and best[0] == 48, best
# The construction the paper states: the 20-cell eight-member class, the ribbon (1,2;0), case (c), period 2.
assert best[2:] == ('(1,2;0)', 'c', 2)
twenty = [c for c in eights if len(next(iter(c))) == 20]
assert len(twenty) == 1
E = C.cells(((1, 2), (0,)))
marks = [m for m in K.marks(E) if m[2] == 'c' and m[4] == 2]
assert len(marks) == 1
B, T, case, v, q = marks[0]
Er, Br, Tr, cr, vr = K.rotate_mark(E, B, T, case, v)
V = {K.compose(D, E, B, T, case, v) for D in twenty[0]} | {K.compose(D, Er, Br, Tr, cr, vr) for D in twenty[0]}
assert len(V) == 16 and all(len(F) == 48 and K.is_connected_skew(F) for F in V)
print('PASS: the 20-cell eight-member class composed with the ribbon (1,2;0), case (c), period 2, and with its '
      'rotation, gives 16 distinct connected diagrams of 48 cells; no smaller such construction with inners of at '
      f'most {EMAX} cells and period at most {QMAX}')
