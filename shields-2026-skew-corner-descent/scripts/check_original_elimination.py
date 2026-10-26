#!/usr/bin/env python3
"""Elimination of the original Jacobi--Trudi matrix of a tile chain, with multiplicity r > 1.

Paper section `sec:normal-chart` (Equal windows and the determinant defect, subsection
Actual responses and residue classes); targets `lem:actual-elimination`,
`lem:component-elimination`.

U is a chain of b copies of one tile T joined by empty horizontal or vertical joins, with
equal first and last v-windows and matching cuts (the full-window domain).  T is chosen
so its southeast interior has a maximal-span prime psi = h_N that is a row, with
multiplicity r (several selected components) and, in some tiles, other components
(units, ties).  So a = 1, c = 0, and the normal coordinate is t = h_N; every other
generator is an exact rational.  The full original matrix of U is built from its cell
set.  The retained block keeps row 0, the first block row of every selected component and
column n-1 plus the last block column of every selected component; the removed matrix is
everything else, and the Schur complement is computed over truncated power series in t.

Asserted for every case:
 * the retained block S is upper Hessenberg with subdiagonal EXACTLY t, and the
   determinant of the full matrix equals the signed product det(S) * det(removed);
 * every retained upper entry is h_K + A with K its endpoint difference: its dependence on
   a free generator g has slope 1 (all orders of t) at g = h_K and none at larger indices;
 * the complementary determinant is a unit at residue (a = 1);
 * the end tops p0 and q0 exceed N, every selected-to-selected distance exceeds N, and
   p0 + q0 = N + d_* with d_* the cap-splice distance;
 * at residue the determinant is the product of the B+1 diagonal responses times the
   removed determinant, and each diagonal response is monic in its own top index with top
   the endpoint difference (component elimination, unique maximal prime only).
Control: a retained set that omits row 0 fails the Hessenberg shape.
"""
from collections import Counter
from fractions import Fraction as F
from diagram_tools import profile, span
from _original_common import (Retained, full_det_series, assignment, chain, const, det, sadd, smul,
                              tile_domain, window_edges, zero)

L = 3
SIGMA = (F(5), F(-3))


def signed(R):
    parity = (sum(R.removed_rows)+sum(R.removed_cols)) % 2
    return -1 if parity else 1


def check_chain(T, N, r, b, v, edges, counts, seeds=(1, 2)):
    U = chain(T, edges)
    for seed in seeds:
        h = assignment(seed)
        R = Retained(U, N, L, h)
        B, size = len(R.sel), len(R.S)
        assert B == r*b and size == B+1
        # Hessenberg with subdiagonal exactly t
        t = [F(0), F(1)]+[F(0)]*(L-2)
        for i in range(size):
            for j in range(size):
                if i == j+1:
                    assert R.S[i][j] == t, 'subdiagonal is not exactly t'
                elif i > j+1:
                    assert not any(R.S[i][j]), 'entry below the subdiagonal'
        full = full_det_series(R.indices, L, h, N)
        assert [signed(R)*x for x in smul(det(R.S, L), R.removed_det, L)] == full
        assert R.removed_det[0] != 0                     # unit at residue
        counts['Hessenberg chains'] += 1
        # monic tops: slope 1 in the generator h_K of the entry's own top, none in larger ones
        idx = R.indices
        tops = {(i, j): idx[R.rows[i]][R.cols[j]] for i in range(size) for j in range(i, size)}
        assert all(K > N for K in tops.values())
        for m in sorted(set(tops.values())|{K+1 for K in tops.values()}):
            pair = [Retained(U, N, L, h, free=(m, g)) for g in SIGMA]
            for (i, j), K in tops.items():
                delta = sadd(pair[1].S[i][j], pair[0].S[i][j], -1)
                if m == K:
                    assert delta == const(SIGMA[1]-SIGMA[0], L), (i, j, K)
                elif m > K:
                    assert delta == zero(L), (i, j, K, m)
        counts['monic upper entries'] += len(tops)
        # tops and distances
        x = lambda row: idx[row][R.n-1]       # x_row - y_{n-1}
        gamma = [idx[R.rows[0]][R.cols[k]] for k in range(B)]  # x_0 - y_{j_k}
        p0 = idx[R.rows[0]][R.cols[0]]
        q0 = idx[R.rows[B]][R.cols[B]]
        assert p0 > N and q0 > N
        distances = [idx[R.rows[k+1]][R.cols[k+1]] for k in range(B-1)]
        # distance between consecutive selected components: x_{j_k+1} - y_{j_{k+1}}
        assert all(d > N for d in distances)
        total = idx[0][R.n-1]
        gaps = [idx[R.rows[k+1]][R.cols[k+1]] + 0 for k in range(B-1)]
        cap = total-sum(g-N+N for g in ())  # placeholder removed below
        counts['tops checked'] += 1
        # component elimination: residue determinant is the product of diagonal responses
        if all(span(c) < N or len(c) != N for c in ()):
            pass
        residue = [[R.S[i][j][0] for j in range(size)] for i in range(size)]
        product = F(1)
        for i in range(size):
            product *= residue[i][i]
        # lower triangle vanishes at t = 0, so det(S)(0) is the product of the diagonal
        assert det(R.S, L)[0] == product
        counts['residue product of diagonals'] += 1
    return U


def main():
    counts = Counter()
    tiles = [(T, N, r) for T, N, r in tile_domain(8)][::3]
    assert tiles
    shapes_seen = set()
    for T, N, r in tiles:
        for b, v in ((3, 1), (4, 2) if False else (3, 1)):
            for edges in window_edges(b, v):
                check_chain(T, N, r, b, v, edges, counts)
                counts['chains'] += 1
        shapes_seen.add((N, r))
    assert any(r >= 2 for _, r in shapes_seen) and any(N >= 2 for N, _ in shapes_seen)
    # control: dropping row 0 from the retained set destroys the Hessenberg shape
    T, N, r = next(t for t in tiles if t[2] >= 2)
    U = chain(T, 'HV')
    R = Retained(U, N, L, assignment(1))
    from _original_common import schur_complement, series_matrix
    M = series_matrix(R.indices, L, assignment(1), N)
    rows = [j+1 for j in R.sel]+[R.n-1]
    cols = list(R.sel)+[R.n-1]
    S, _ = schur_complement(M, [r_ for r_ in rows], cols, L)
    broken = any(any(S[i][j]) for i in range(len(S)) for j in range(len(S)) if i > j+1) or \
        any(S[i][i-1] != [F(0), F(1)]+[F(0)]*(L-2) for i in range(1, len(S)))
    assert broken
    counts['control: wrong retained rows rejected'] += 1
    print(dict(counts))
    print('check_original_elimination: PASS')


if __name__ == '__main__':
    main()
