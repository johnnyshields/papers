#!/usr/bin/env python3
r"""`subsec:marked-geometry`: the boundary-word facts about a marked composition that the chart transport
consumes, asserted on actual cell unions.

For a connected skew diagram S let the content diagonals be indexed k = 0, ..., N-1 from the southwest
cell, with row interval [l_k, h_k] on diagonal k, and put A_k = l_{k-1} - l_k, B_k = h_{k-1} - h_k,
H_k = h_k - l_k + 1.  Over a box of inners with every legal positive mark (all four attachment cases) and
every connected nonrow outer D of small area, composed by the engine's cell union, the script asserts:

  - every internal step is binary and H_k - H_{k-1} = A_k - B_k, with H_k > 0;
  - the full membership words of the beta lists (Y normalized to start at 0): A(j) = 1 if j is in Y,
    B(j) = 1 if j is in X, and H(j) = #{y in Y: y <= j} - #{x in X: x <= j}, on the composite and the outer;
  - the composite has N = M q + w diagonals; its phases satisfy 1 <= sigma <= w, 0 <= tau < w and
    tau < sigma in the mixed cases;
  - the periodic slot table of each case (a)-(d) for 1 <= j < M, the initial and terminal values
    at tau, sigma and N - w + tau, N - w + sigma, and q-periodicity of each word away from the residues
    at which the table names it;
  - at empty width the composite words are q-periodic except at residue zero.

Integer arithmetic on cells only.  Each case is required to occur, so the table cannot pass vacuously.
"""
from collections import Counter
from itertools import product

from check_chart_inflation import candidate_marks, content, diagonal_intervals, mark_failures, phases, span
from _composition_engine import (
    beta_from_cells, cells_from_rho_a, compose, enum_rho_a, is_connected_skew, normalize, sw_cell,
)


def words(S):
    iv = diagonal_intervals(S)
    base = content(sw_cell(S))
    N = span(S)
    lo = [iv[base + k][0] for k in range(N)]
    hi = [iv[base + k][1] for k in range(N)]
    A = {k: lo[k - 1] - lo[k] for k in range(1, N)}
    B = {k: hi[k - 1] - hi[k] for k in range(1, N)}
    H = {k: hi[k] - lo[k] + 1 for k in range(N)}
    return A, B, H, N


def check_beta_words(S):
    """The full membership words of the beta lists (normalized so the smallest column beta is 0)."""
    A, B, H, N = words(S)
    x, y = beta_from_cells(S)
    t = min(y)
    X, Y = [v - t for v in x], [v - t for v in y]
    assert min(Y) == 0 and len(set(X)) == len(X) and len(set(Y)) == len(Y)
    for k in range(1, N):
        assert A[k] == int(k in Y) and B[k] == int(k in X), ("membership word", k)
    for k in range(N):
        assert H[k] == sum(1 for v in Y if v <= k) - sum(1 for v in X if v <= k), ("height", k)


def main():
    counts = Counter()
    outers = sorted({cells_from_rho_a(rows, ov) for rows, ov in enum_rho_a(4, minsize=2) if len(rows) > 1},
                    key=lambda c: (len(c), sorted(c)))
    for n in range(1, 4):
        for rows in product(range(1, 6), repeat=n):
            if not 2 <= sum(rows) <= 9:
                continue
            for ov in product(*(range(1, min(a, b) + 1) for a, b in zip(rows, rows[1:]))):
                inner = cells_from_rho_a(rows, ov)
                for lower, upper, case, disp in candidate_marks(inner):
                    if mark_failures(inner, lower, upper, case, disp):
                        continue
                    q, w = content(disp), span(lower) if lower else 0
                    for D in outers:
                        S = compose(D, inner, lower, upper, case, disp)
                        assert is_connected_skew(S)
                        A, B, H, N = words(S)[:4]
                        check_beta_words(S)
                        AD, BD, HD, M = words(D)
                        check_beta_words(D)
                        assert all(v in (0, 1) for v in list(A.values()) + list(B.values()))
                        assert all(h > 0 for h in H.values())
                        assert all(H[k] - H[k - 1] == A[k] - B[k] for k in range(1, N))
                        assert N == M * q + w, (N, M, q, w)
                        if w == 0:
                            for k in range(1, N - q):
                                if k % q:
                                    assert A[k] == A[k + q] and B[k] == B[k + q], ("empty width", case, k)
                            counts['empty'] += 1
                            continue
                        tau, sigma = phases(inner, lower, upper, disp)
                        assert 0 <= tau < w and 1 <= sigma <= w
                        if case in 'cd':
                            assert tau < sigma
                        slots = {'a': (('A', tau, 'A', 1), ('B', sigma, 'B', 1)),
                                 'b': (('B', tau, 'A', -1), ('A', sigma, 'B', -1)),
                                 'c': (('B', tau, 'A', -1), ('B', sigma, 'B', 1)),
                                 'd': (('A', tau, 'A', 1), ('A', sigma, 'B', -1))}[case]
                        W = {'A': A, 'B': B}
                        Dw = {'A': AD, 'B': BD}
                        slot_res = {'A': set(), 'B': set()}
                        for word, off, src, sgn in slots:
                            slot_res[word].add(off % q)
                            for j in range(1, M):
                                want = Dw[src][j] if sgn == 1 else 1 - Dw[src][j]
                                assert W[word][j * q + off] == want, ("slot", case, word, j, off)
                        for word in 'AB':
                            for k in range(1, N - q):
                                if k % q not in slot_res[word]:
                                    assert W[word][k] == W[word][k + q], ("periodic", case, word, k)
                        # initial and terminal values (indices outside 1..N-1 are the omitted steps)
                        init = {'a': (('A', tau, 1), ('B', sigma, 0)),
                                'b': (('B', tau, 0), ('A', sigma, 1)),
                                'c': (('B', tau, 0), ('B', sigma, 0)),
                                'd': (('A', tau, 1), ('A', sigma, 1))}[case]
                        term = {'a': (('A', N - w + tau, 0), ('B', N - w + sigma, 1)),
                                'b': (('B', N - w + tau, 1), ('A', N - w + sigma, 0)),
                                'c': (('B', N - w + tau, 1), ('B', N - w + sigma, 1)),
                                'd': (('A', N - w + tau, 0), ('A', N - w + sigma, 0))}[case]
                        for word, k, val in init + term:
                            if 1 <= k <= N - 1:
                                assert W[word][k] == val, ("boundary value", case, word, k, val)
                                counts['boundary_checked'] += 1
                        counts[case] += 1
    for key in 'abcd':
        assert counts[key] > 0, ("case never occurs", key)
    assert counts['empty'] > 0 and counts['boundary_checked'] > 0
    print("marked boundary words: slot table, initial and terminal values, periodicity and phases on", dict(sorted(counts.items())))
    print("ALL PASS")


if __name__ == "__main__":
    main()
