#!/usr/bin/env python3
"""Row inners: the affine profile action and the class transport it induces.

Checks the two lemmas on row inners in the section on period words and line
inners, on every connected diagram in a stated range, built from cells.

* Composition with the case-(a) row mark of period q and width w is placed cell
  by cell from the diagonal-rank offsets and compared with the affine profile
  formula (r;g) -> (qr+w; qg+w); the mark's copies, middle and hats are read
  from the cells.
* Beta lists, Jacobi-Trudi indices and negative positions transform as stated,
  and the profile map commutes with rotation.
* The congruence form of the divisibility condition is compared with the
  gcd-and-offset form it replaces, over every parent in range.
* The homogenized substitution carries s_D to s_{L D} exactly, with skew Schur
  polynomials expanded by signed permutations of the Jacobi-Trudi board.
* For every image of at most CLASS_CELLS cells, the set of connected diagrams
  with the image's polynomial equals the image of the outer's set.  Only
  connected diagrams are enumerated, so this is the class statement among
  connected diagrams.
* For every outer of at most CLASS_CELLS cells and every period and width, two
  outers of one size and row count have equal polynomials exactly when their
  images do.  This reaches the nonrotation classes in range, whose images are
  too large to enumerate around.

Firing controls: dropping the h_w padding breaks the substitution identity;
comparing the offset without reducing it modulo the period breaks the
equivalence; and a non-uniform map, shifting rows but not overlaps, splits
every nonrotation class in range.  Standard library only.
"""
from __future__ import annotations

from collections import defaultdict
from math import gcd
from functools import reduce
import sys

OUTER_CELLS = 7      # outers for the action, beta-list and substitution checks
PARENT_CELLS = 11    # parents for the congruence-equivalence check
CLASS_CELLS = 10     # images whose full connected classes are enumerated
PERIODS = (2, 3, 4)


def profiles(size):
    """All connected profiles (r;g) with exactly `size` cells."""
    out = []

    def extend(rows, gaps, remaining):
        if remaining == 0:
            out.append((tuple(rows), tuple(gaps)))
            return
        for r in range(1, remaining + 1):
            if not rows:
                extend([r], [], remaining - r)
            else:
                for g in range(0, min(rows[-1], r)):
                    extend(rows + [r], gaps + [g], remaining - r)

    extend([], [], size)
    return out


def beta(profile):
    """Beta lists from zeta_n = 0, r_i = xi_i - zeta_i, g_i = xi_{i+1} - zeta_i."""
    r, g = profile
    n = len(r)
    xi, zeta = [0] * n, [0] * n
    zeta[n - 1] = 0
    xi[n - 1] = r[n - 1]
    for i in range(n - 2, -1, -1):
        zeta[i] = xi[i + 1] - g[i]
        xi[i] = zeta[i] + r[i]
    return tuple(xi), tuple(zeta)


def cells(profile):
    """Cells (row, column), rows downward; row i holds contents zeta_i+1..xi_i."""
    xi, zeta = beta(profile)
    return frozenset((i, c + i) for i in range(len(xi)) for c in range(zeta[i] + 1, xi[i] + 1))


def profile_of(cellset):
    """Profile of a cell set, asserting it is a connected skew diagram."""
    rows = defaultdict(list)
    for i, j in cellset:
        rows[i].append(j)
    keys = sorted(rows)
    assert keys == list(range(keys[0], keys[0] + len(keys))), "missing row"
    spans = []
    for i in keys:
        cols = sorted(rows[i])
        assert cols == list(range(cols[0], cols[-1] + 1)), "row not an interval"
        spans.append((cols[0], cols[-1]))
    for (lo, hi), (lo2, hi2) in zip(spans, spans[1:]):
        assert lo2 <= lo and hi2 <= hi, "not a skew shape"
    r = tuple(hi - lo + 1 for lo, hi in spans)
    g = []
    for (lo, hi), (lo2, hi2) in zip(spans, spans[1:]):
        common = min(hi, hi2) - max(lo, lo2) + 1
        assert common >= 1, "disconnected"
        g.append(common - 1)
    return r, tuple(g)


def row_mark(q, w):
    """The row E=(q+w) with lower copy on contents [0,w-1], upper on [q,q+w-1]."""
    E = frozenset((0, c) for c in range(q + w))
    low = frozenset((0, c) for c in range(w))
    high = frozenset((0, c) for c in range(q, q + w))
    v = (0, q)
    return E, low, high, v


def check_mark_legal(q, w):
    E, low, high, v = row_mark(q, w)
    assert frozenset((i + v[0], j + v[1]) for i, j in low) == high
    assert w < q                                                   # II: separation
    for copy in (low, high):                                       # I: bands are all of E
        diags = {j - i for i, j in copy}
        assert {x for x in E if x[1] - x[0] in diags} == copy
    for copy in (low, high):                                       # III: a row remains
        rest = E - copy
        assert profile_of(rest) == ((q,), ())
    middle = E - low - high                                        # IV: middle hat empty
    hat = {x for x in middle if (x[0] + 1, x[1] + 1) in middle}
    assert not hat


def compose(outer, q, w):
    """Place a copy of the row inner at t*v + i*e for each outer cell (i, i+t)."""
    E, _, _, v = row_mark(q, w)
    out = set()
    for i, j in cells(outer):
        t = j - i
        origin = (t * v[0] + i, t * v[1] + i)
        out |= {(origin[0] + a, origin[1] + b) for a, b in E}
    return frozenset(out)


def lift(profile, q, w):
    r, g = profile
    return tuple(q * x + w for x in r), tuple(q * x + w for x in g)


def rotate(profile):
    r, g = profile
    return tuple(reversed(r)), tuple(reversed(g))


def schur(profile):
    """Skew Schur polynomial: sorted tuples of positive h-indices -> coefficient."""
    xi, zeta = beta(profile)
    n = len(xi)
    poly = defaultdict(int)

    def walk(i, used, indices, sign):
        if i == n:
            poly[tuple(sorted(x for x in indices if x > 0))] += sign
            return
        for j in range(n):
            if j in used:
                continue
            k = xi[i] - zeta[j]
            if k < 0:
                continue
            inv = sum(1 for u in used if u > j)
            walk(i + 1, used | {j}, indices + [k], -sign if inv % 2 else sign)

    walk(0, frozenset(), [], 1)
    return {m: c for m, c in poly.items() if c}


def substitute(poly, n, q, w, pad=True):
    out = defaultdict(int)
    for mono, coeff in poly.items():
        new = [q * k + w for k in mono]
        if pad and w > 0:
            new += [w] * (n - len(mono))
        out[tuple(sorted(new))] += coeff
    return {m: c for m, c in out.items() if c}


def key(poly):
    return frozenset(poly.items())


def main():
    action = substitution = negatives = 0
    for q in PERIODS:
        for w in range(q):
            check_mark_legal(q, w)

    for size in range(1, OUTER_CELLS + 1):
        for D in profiles(size):
            n = len(D[0])
            xi, zeta = beta(D)
            sD = schur(D)
            for q in PERIODS:
                for w in range(q):
                    F = lift(D, q, w)
                    assert profile_of(compose(D, q, w)) == F, (D, q, w)
                    xiF, zetaF = beta(F)
                    assert xiF == tuple(q * x + w for x in xi) and zetaF == tuple(q * z for z in zeta)
                    assert tuple((x - w) // q for x in xiF) == xi and tuple(z // q for z in zetaF) == zeta
                    assert lift(rotate(D), q, w) == rotate(F)
                    negD = {(i, j) for i in range(n) for j in range(n) if xi[i] < zeta[j]}
                    negF = {(i, j) for i in range(n) for j in range(n) if xiF[i] < zetaF[j]}
                    assert negD == negF
                    assert substitute(sD, n, q, w) == schur(F), (D, q, w)
                    action += 1
                    substitution += 1
                    negatives += len(negD)

    # Congruence form against the gcd-and-offset form, over every parent in range.
    equivalence = 0
    for size in range(2, PARENT_CELLS + 1):
        for F in profiles(size):
            r, g = F
            if len(r) < 2:
                continue
            Q = reduce(gcd, [r[i] - g[i] for i in range(len(g))] + [r[i + 1] - g[i] for i in range(len(g))])
            eta = beta(F)[0][-1] % Q
            for d in range(2, max(r) + 2):
                for t in range(d):
                    gcd_form = Q % d == 0 and eta % d == t
                    residue_form = all(x % d == t for x in r + g)
                    assert gcd_form == residue_form, (F, d, t)
                    if residue_form:
                        D = (tuple((x - t) // d for x in r), tuple((x - t) // d for x in g))
                        assert all(x >= 1 for x in D[0])
                        assert all(0 <= D[1][i] < min(D[0][i], D[0][i + 1]) for i in range(len(g)))
                        assert lift(D, d, t) == F
                    equivalence += 1

    # Full connected classes of every image of at most CLASS_CELLS cells, both directions.
    classes = defaultdict(set)
    polys = {}
    for size in range(1, CLASS_CELLS + 1):
        for P in profiles(size):
            k = key(schur(P))
            polys[P] = k
            classes[(size, k)].add(P)
    transported = 0
    for size in range(1, CLASS_CELLS + 1):
        for D in profiles(size):
            for q in PERIODS:
                for w in range(q):
                    F = lift(D, q, w)
                    if sum(F[0]) > CLASS_CELLS:
                        continue
                    source = classes[(size, polys[D])]
                    target = classes[(sum(F[0]), polys[F])]
                    assert {lift(P, q, w) for P in source} == target, (D, q, w)
                    for P in source:                       # the cited invariants, corroborated
                        assert len(P[0]) == len(D[0])
                        assert sorted(P[0]) == sorted(D[0]) and sorted(P[1]) == sorted(D[1])
                    transported += 1

    # Images of every class of at most CLASS_CELLS cells, at every period and width:
    # two outers of one size and row count have equal functions exactly when their images
    # do.  This reaches the nonrotation classes, whose images lie beyond the enumeration.
    nontrivial = [sorted(c) for c in classes.values() if len({min(P, rotate(P)) for P in c}) > 1]
    assert nontrivial, "no nonrotation class in range"
    image_pairs = 0
    for q in PERIODS:
        for w in range(q):
            by_shape = defaultdict(dict)
            for P, k in polys.items():
                by_shape[(sum(P[0]), len(P[0]))].setdefault(k, set()).add(key(schur(lift(P, q, w))))
            for shape, groups in by_shape.items():
                images = [next(iter(v)) for v in groups.values()]
                assert all(len(v) == 1 for v in groups.values()), (q, w, shape)
                assert len(set(images)) == len(images), (q, w, shape)
                image_pairs += len(groups)

    # Firing controls.
    pad_fired = sum(1 for size in range(2, 6) for D in profiles(size) if len(D[0]) > 1
                    and substitute(schur(D), len(D[0]), 2, 1, pad=False) != schur(lift(D, 2, 1)))
    assert pad_fired > 0, "dropping the h_w padding was not detected"

    # The unreduced offset differs only when the offset reaches the trial period, which
    # needs wider rows than the exhaustive range; two-row parents reach it cheaply.
    offset_fired = 0
    two_rows = [((a, b), (c,)) for a in range(1, 30) for b in range(1, 30) for c in range(min(a, b))]
    for r, g in two_rows:
        Q = gcd(r[0] - g[0], r[1] - g[0])
        eta = beta((r, g))[0][-1] % Q
        for d in range(2, max(r) + 2):
            for t in range(d):
                assert (Q % d == 0 and eta % d == t) == all(x % d == t for x in r + g)
                if (Q % d == 0 and eta == t) != all(x % d == t for x in r + g):
                    offset_fired += 1
    assert offset_fired > 0, "an unreduced offset was not detected"

    uneven_fired = 0
    for members in nontrivial:                                     # rows shifted, overlaps not
        images = [(tuple(2 * x + 1 for x in P[0]), tuple(2 * x for x in P[1])) for P in members]
        if len({key(schur(F)) for F in images}) > 1:
            uneven_fired += 1
    assert uneven_fired > 0, "a non-uniform profile map was not detected"

    print(f"row marks legal: periods {PERIODS}, every width")
    print(f"action, beta lists, rotation, negative positions, substitution: {action} (outer, q, w) cases "
          f"through {OUTER_CELLS} cells; {negatives} negative positions preserved")
    print(f"congruence form = gcd-and-offset form: {equivalence} (parent, d, t) cases through {PARENT_CELLS} cells")
    print(f"full connected classes transported: {transported} images of at most {CLASS_CELLS} cells")
    print(f"class images separated and unsplit: {image_pairs} (class, q, w) cases through {CLASS_CELLS} cells, "
          f"{len(nontrivial)} nonrotation classes among them")
    print(f"controls fired: padding {pad_fired}, unreduced offset {offset_fired}, non-uniform map on {uneven_fired} of {len(nontrivial)} nonrotation classes")
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
