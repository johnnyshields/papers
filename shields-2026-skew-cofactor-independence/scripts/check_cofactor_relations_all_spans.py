#!/usr/bin/env python3
"""Paper section `sec:cofactors` (Linear relations among cofactors).  Target `thm:cofactor-relations` for EVERY
dense core of order n = 2, 3, 4, whatever its span.

The other scripts take every core up to a span.  Here the span is removed.  A dense core has every label
L_ij = a_i - b_j positive, so each signed cofactor D_ij is a polynomial in the distinct generators h_L, L a label.
Two cores of the same order whose labels satisfy the same equalities L_ij = L_kl (the same *label pattern*)
have cofactors that are images of one another under an injective renaming of generators, hence the same
rational relation space.  The rotation condition `eq:rotation-condition`, a_i + b_{n+1-i} = N, reads
L_{i,n} = L_{1,n+1-i}, so symmetry is a pattern property too.  At fixed order the theorem is therefore a
statement about finitely many patterns.

  (1) The realizable patterns are enumerated exactly.  In the gaps u_i = a_i - a_{i+1} > 0,
      w_j = b_j - b_{j+1} > 0 and the free gap a_n - b_1 > 0, an equality L_ij = L_kl with i < k forces j < l
      and reads sum_{i<=s<k} u_s = sum_{j<=s<l} w_s; the patterns are the faces of this arrangement in the open
      positive orthant.  A depth-first search fixes each hyperplane to <, = or > and prunes by exact Fourier-
      Motzkin feasibility over the rationals (the cone is homogeneous, so strict inequalities become >= 1).
  (2) Every realizable pattern is met by an integer core in a search box, found by enumeration, so the pattern
      list is complete and every pattern has a witness.
  (3) On each witness: rank n^2 when C != C*, rank n(n+1)/2 when C = C* with every e_ij - e_{n+1-j,n+1-i} a
      relation (so the relation space is exactly their span), by exact rational elimination.
  (4) The reduction itself: on every pair of cores of one pattern in a box, the second core's cofactors are
      the first's under the label renaming, coefficient for coefficient.
"""
import itertools
import sys
from collections import Counter
from fractions import Fraction

from check_cofactor_dilation import cofactors, rank


def hyperplanes(n):
    """(i, k, j, l): sum u_i..u_{k-1} = sum w_j..w_{l-1}, i < k, j < l."""
    return [(i, k, j, l) for i in range(n) for k in range(i + 1, n) for j in range(n) for l in range(j + 1, n)]


def row(hp, n):
    i, k, j, l = hp
    v = [Fraction(0)] * (2 * (n - 1))
    for s in range(i, k):
        v[s] += 1
    for s in range(j, l):
        v[n - 1 + s] -= 1
    return v


def feasible(eqs, ges):
    """Exact feasibility of {e.x = 0 for e in eqs, g.x >= 1 for g in ges} by elimination."""
    eqs = [list(e) for e in eqs]
    ges = [(list(g), Fraction(1)) for g in ges]
    nv = len(ges[0][0]) if ges else len(eqs[0])
    # substitute equalities
    while eqs:
        e = eqs.pop()
        piv = next((p for p in range(nv) if e[p] != 0), None)
        if piv is None:
            continue
        def subst(v):
            if v[piv] == 0:
                return v
            f = v[piv] / e[piv]
            return [v[p] - f * e[p] for p in range(nv)]
        eqs = [subst(x) for x in eqs]
        ges = [(subst(g), r) for g, r in ges]
    # Fourier-Motzkin on g.x >= r
    for var in range(nv):
        pos = [(g, r) for g, r in ges if g[var] > 0]
        neg = [(g, r) for g, r in ges if g[var] < 0]
        zer = [(g, r) for g, r in ges if g[var] == 0]
        new = list(zer)
        for gp, rp in pos:
            for gn, rn in neg:
                a, b = gp[var], -gn[var]
                new.append(([b * gp[p] + a * gn[p] for p in range(nv)], b * rp + a * rn))
        seen = set()
        ges = []
        for g, r in new:
            key = (tuple(g), r)
            if key not in seen:
                seen.add(key)
                ges.append((g, r))
        if len(ges) > 4000:
            ges = prune(ges)
    return all(r <= 0 for g, r in ges)


def prune(ges):
    """Drop constraints dominated by a positive multiple of another (same direction, weaker bound)."""
    best = {}
    for g, r in ges:
        lead = next((x for x in g if x != 0), None)
        if lead is None:
            best.setdefault(("0",), (g, r))
            if r > best[("0",)][1]:
                best[("0",)] = (g, r)
            continue
        s = abs(lead)
        key = tuple(x / s for x in g)
        if key not in best or r / s > best[key][1]:
            best[key] = (g, r / s)
    return [(list(k) if k != ("0",) else v[0], v[1]) for k, v in best.items()]


def faces(n):
    hps = hyperplanes(n)
    rows = [row(hp, n) for hp in hps]
    nv = 2 * (n - 1)
    unit = [[Fraction(int(p == q)) for p in range(nv)] for q in range(nv)]
    out = []

    def dfs(idx, eqs, ges, signs):
        if not feasible(eqs, unit + ges):
            return
        if idx == len(hps):
            out.append(tuple(signs))
            return
        r = rows[idx]
        dfs(idx + 1, eqs + [r], ges, signs + [0])
        dfs(idx + 1, eqs, ges + [r], signs + [1])
        dfs(idx + 1, eqs, ges + [[-x for x in r]], signs + [-1])

    dfs(0, [], [], [])
    return hps, out


def pattern(a, b, hps):
    n = len(a)
    u = [a[s] - a[s + 1] for s in range(n - 1)]
    w = [b[s] - b[s + 1] for s in range(n - 1)]
    sig = []
    for i, k, j, l in hps:
        d = sum(u[i:k]) - sum(w[j:l])
        sig.append((d > 0) - (d < 0))
    return tuple(sig)


def core(u, w, gap):
    n = len(u) + 1
    b = [0] * n
    for s in range(n - 2, -1, -1):
        b[s] = b[s + 1] + w[s]
    a = [0] * n
    a[n - 1] = b[0] + gap
    for s in range(n - 2, -1, -1):
        a[s] = a[s + 1] + u[s]
    return tuple(a), tuple(b)


def is_symmetric(a, b):
    n, N = len(a), a[0]
    return all(a[i] + b[n - 1 - i] == N for i in range(n))


def check_order(n, box):
    hps, fs = faces(n)
    wit = {}
    for vals in itertools.product(range(1, box + 1), repeat=2 * (n - 1)):
        u, w = vals[:n - 1], vals[n - 1:]
        a, b = core(u, w, 1)
        sig = pattern(a, b, hps)
        if sig not in wit:
            wit[sig] = (a, b)
    assert set(wit) == set(fs), (n, len(wit), len(fs), set(fs) - set(wit))
    n_sym = 0
    for sig, (a, b) in sorted(wit.items()):
        cofs = cofactors(a, b)
        flat = [cofs[i][j] for i in range(n) for j in range(n)]
        r = rank(flat)
        if is_symmetric(a, b):
            n_sym += 1
            assert r == n * (n + 1) // 2, (a, b, r)
            for i in range(n):
                for j in range(n):
                    diff = Counter(cofs[i][j])
                    diff.subtract(cofs[n - 1 - j][n - 1 - i])
                    assert not +diff and not -diff, (a, b, i, j)
        else:
            assert r == n * n, (a, b, r)
    assert n_sym > 0
    print("order %d: %d realizable label patterns (exact face enumeration of %d hyperplanes), each met by a "
          "core with gaps <= %d; rank n^2 on %d nonsymmetric, n(n+1)/2 with the reflection relations on %d "
          "symmetric: thm:cofactor-relations for every dense core of order %d"
          % (n, len(fs), len(hps), box, len(fs) - n_sym, n_sym, n))


def check_renaming(n, box):
    """The reduction itself: a second core with the same pattern has exactly the renamed cofactors."""
    hps = hyperplanes(n)
    first, n_pairs = {}, 0
    for vals in itertools.product(range(1, box + 1), repeat=2 * (n - 1)):
        for gap in (1, 3):
            a, b = core(vals[:n - 1], vals[n - 1:], gap)
            sig = pattern(a, b, hps)
            if sig not in first:
                first[sig] = (a, b)
                continue
            a0, b0 = first[sig]
            ren = {a0[i] - b0[j]: a[i] - b[j] for i in range(n) for j in range(n)}
            assert all(ren[a0[i] - b0[j]] == a[i] - b[j] for i in range(n) for j in range(n))
            assert len(set(ren.values())) == len(ren)                     # injective
            c0, c1 = cofactors(a0, b0), cofactors(a, b)
            for i in range(n):
                for j in range(n):
                    mapped = Counter({tuple(sorted(ren[x] for x in m)): v for m, v in c0[i][j].items()})
                    assert mapped == Counter(c1[i][j]), (a0, b0, a, b, i, j)
            n_pairs += 1
    assert n_pairs > 10
    print("order %d: on %d same-pattern pairs the cofactors are the renamed cofactors, coefficient for "
          "coefficient" % (n, n_pairs))


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    orders = [int(x) for x in sys.argv[1:]] or [2, 3]
    boxes = {2: 4, 3: 6, 4: 7}
    for n in orders:
        check_renaming(n, min(boxes[n], 5))
        check_order(n, boxes[n])
    print("ALL PASS")
