r"""Paper sections `sec:unit-restoration` (Complete unit restoration), `sec:fixed-caps` (Rigidity with the
same literal cap) and `sec:stationary` (Finite stationary separation).  Target labels:
`sc:linearized-coframe`, `sc:linearized-prefix`, `sc:gap-coface`, `sc:fcp-numerator-flags`,
`sc:fcp-recursive-cap`, `sc:component-column`, `sc:common-top-column`, `sc:component-ratio`,
`sc:two-endpoints`, `sc:native-shift-identity`, `sc:exact-shift-cap`, `sc:finite-operator`.

The displayed identities inside the proofs that no census of whole theorems reaches.  SymPy builds every
object from full flags (`_coframes`): matrices keep common betas as coherent units.

  (A) `sc:linearized-coframe` and `sc:linearized-prefix`: the first variation of the complete coframe under
      constant vacancy weights is the displayed combination of pulses with P_b = [H G]_b and the proper
      matrix of the baseline, on every connected zero-free board through span four, for random rational
      weights; the prefix compensation formula is the same solve restricted to a leading block.
  (B) `sc:gap-coface`, `sc:fcp-numerator-flags`, `sc:fcp-recursive-cap`: for every zero-free connected board
      and every cut of its proper matrix into a leading block P and a next strict block E, the numerator
      determinant is det P times the displayed Schur complement, the numerator lists are connected with the
      stated rows and columns, and after translation by the least column of E the numerator is literally the
      splice of the stated cap K_E onto E.
  (C) `sc:two-endpoints`, `sc:component-column`, `sc:common-top-column`, `sc:component-ratio`,
      `sc:native-shift-identity`: on every coequal pair through span five, [T(zH^p)]_M = -E_0 and
      [T(zH^p)]_{M+1} = -E_1 - G_1 E_0 for p = 2, 3, 4; the coframes are affine in the top proper letter with
      derivative -z^a g/k, where g and k belong to the highest strict proper component; the first observation's
      derivative in that letter is the difference of the two component ratios; and, whenever both native
      equations at the maximal proper row hold, the whole cap polynomial of `sc:exact-shift-cap` vanishes.
"""
import random
from collections import defaultdict
from itertools import combinations

import sympy as sp

from _coframes import (
    z, theta, epsilon, letter, determinant, right_coframe, clock, coefficient, clip, operator, zero,
    connected, connected_boards, splice, vacancies, restore, matrix, raw, vacancy_pulse,
)

random.seed(20261026)


def proper_blocks(board):
    """Strict components of the proper matrix as (row slice, column slice) pairs, from the top.  A cut after
    k proper rows is valid when the next proper row lies below the k-th proper column."""
    rows, cols = board
    R, C = rows[1:], cols[:-1]
    cuts = [k for k in range(1, len(R)) if R[k] < C[k - 1]]
    bounds = [0] + cuts + [len(R)]
    return [(R[a:b], C[a:b]) for a, b in zip(bounds, bounds[1:])]


def component_board(rows_, cols_):
    """The component as a diagram: lists translated so that its least column is zero."""
    a = cols_[-1]
    return tuple(x - a for x in rows_), tuple(y - a for y in cols_)


# ---------------------------------------------------------------- (A)

def check_linearized_coframe():
    n = 0
    for span in range(2, 5):
        for board in connected_boards(span):
            rows, cols = board
            if set(rows) & set(cols):
                continue
            positions = vacancies(board)
            if not positions:
                continue
            m = span
            g = right_coframe(board, unit=1)
            H = clock(m, unit=1)
            weights = {b: sp.Rational(random.randint(-5, 5), random.randint(1, 4)) for b in positions}
            if all(w == 0 for w in weights.values()):
                weights[positions[0]] = 1
            I, S = rows[1:], cols[:-1]
            D0 = matrix(rows[1:], cols[:-1], unit=1) if I else None
            # exact first variation: derivative in epsilon of the coframe of the weighted restoration, linear
            # in the weights by superposition of single restorations
            Q = sp.S.Zero
            for b in positions:
                Pb = coefficient(clip(H * g, m), b)
                vb = sp.Matrix([raw(i - b, 1) for i in I])
                feedback = sp.S.Zero
                if I:
                    solved = D0.inv() * vb
                    feedback = sp.Add(*(sp.cancel(c) * z ** s for c, s in zip(solved, S)))
                pulse = -Pb * (z ** b - feedback)
                Q += weights[b] * pulse
                # the single-restoration pulse agrees with the derivative of the restored board's coframe
                restored = restore(board, b)
                series = sp.series(sp.cancel(right_coframe(restored, unit=1, scale=epsilon)), epsilon, 0, 2).removeO()
                assert zero(series.coeff(epsilon, 1) - pulse), (board, b)
            Q = sp.expand(Q)
            assert coefficient(Q, 0) == 0
            assert sp.Poly(Q, z).degree() < m
            for b in positions:
                assert zero(coefficient(Q, b) + weights[b] * coefficient(clip(H * g, m), b))
            assert all(zero(coefficient(clip(H * Q, m + 1), i)) for i in I)
            # linearized-prefix: the leading-block compensation reproduces the proper-column part of Q
            if I:
                low = [Q.coeff(z, j) for j in range(0, m)]
                comp = -D0.inv() * sp.Matrix(
                    [sum(raw(x - j, 1) * low[j] for j in range(m) if j not in S) for x in I])
                for s, c in zip(S, comp):
                    assert zero(Q.coeff(z, s) - c), (board, s)
            n += 1
    assert n > 5
    print("PASS (A) sc:linearized-coframe and sc:linearized-prefix on %d zero-free boards" % n)


# ---------------------------------------------------------------- (B)

def translate(board, t):
    return tuple(x - t for x in board[0]), tuple(y - t for y in board[1])


def check_numerator_blocks():
    n = 0
    for span in range(3, 8):
        for board in connected_boards(span):
            rows, cols = board
            if set(rows) & set(cols):
                continue
            blocks = proper_blocks(board)
            m = span
            for k in range(1, len(blocks)):
                rowsP = tuple(x for blk in blocks[:k] for x in blk[0])
                colsP = tuple(y for blk in blocks[:k] for y in blk[1])
                rowsE, colsE = blocks[k]
                t, a0 = rowsE[0], colsE[-1]
                # numerator flags and its connectivity
                XN = tuple(sorted((m,) + rowsP + tuple(x for x in rowsE if x != t), reverse=True))
                YN = tuple(sorted(colsP + colsE, reverse=True))
                assert len(XN) == len(YN)
                assert all(XN[i] > YN[i] for i in range(len(XN)))
                assert all(XN[i + 1] >= YN[i] for i in range(len(XN) - 1)), (board, XN, YN)
                # the cap K_E and the literal splice K_E <| E after translation by a0
                XK = tuple(sorted((m - t,) + tuple(x - t for x in rowsP), reverse=True))
                YK = tuple(sorted(tuple(y - t for y in colsP) + (0,), reverse=True))
                K = (XK, YK)
                assert connected(K), (board, K)
                E = component_board(rowsE, colsE)
                assert connected(E) and E[0][0] == t - a0 and (t - a0) < m
                joined = splice(K, E)
                assert joined == translate((XN, YN), a0), (board, joined, (XN, YN))
                assert joined[0][0] == m - a0 > t - a0
                # the Schur complement of the gap-coface numerator
                T = matrix(rows[1:], cols[:-1], unit=1)
                P = matrix(rowsP, colsP, unit=1)
                nonzero = determinant((XN, YN), unit=1)
                assert nonzero != 0
                for b in [v for v in vacancies(board) if v < colsP[-1]]:
                    num_rows = (m,) + rowsP
                    num_cols = colsP + (b,)
                    row0 = sp.Matrix([[raw(m - y, 1) for y in colsP]])
                    colb = sp.Matrix([raw(x - b, 1) for x in rowsP])
                    coface = raw(m - b, 1) - (row0 * P.inv() * colb)[0]
                    nb = determinant((num_rows, num_cols), unit=1)
                    assert zero(nb - (-1) ** len(rowsP) * P.det() * coface), (board, b)
                    assert not zero(nb)
                    ok = (all(num_rows[i] > num_cols[i] for i in range(len(num_rows)))
                          and all(num_rows[i + 1] >= num_cols[i] for i in range(len(num_rows) - 1)))
                    assert ok, (board, b, num_rows, num_cols)
                    assert not zero(coface)
                n += 1
    assert n > 0
    print("PASS (B) sc:fcp-numerator-flags, sc:fcp-recursive-cap, sc:gap-coface on %d (board, cut) pairs" % n)


# ---------------------------------------------------------------- (C)

def check_coequal_identities():
    groups = defaultdict(list)
    for span in range(3, 6):
        for board in connected_boards(span):
            groups[(span, determinant(board, unit=1))].append(board)
    n_pairs = n_top = n_cap = 0
    for (span, _), boards in groups.items():
        for a_board, b_board in combinations(boards, 2):
            M, m = span, span - 1
            g, c = right_coframe(a_board), right_coframe(b_board)
            H = clock(M)                                  # includes the top letter of degree M
            delta = sp.expand(c - g)
            for p in (2, 3, 4):
                E0 = coefficient(clip(H ** p * delta, M + 1), m)
                E1 = coefficient(clip(H ** p * delta, M + 2), M) - coefficient(delta, 1) * coefficient(
                    clip(H ** p * g, M + 1), m)
                Tfull = sp.expand(g * clip(z * H ** p * c, M) - c * clip(z * H ** p * g, M))
                assert zero(coefficient(Tfull, M) + E0), (a_board, b_board, p)
                assert zero(coefficient(Tfull, M + 1) + E1 + coefficient(g, 1) * E0), (a_board, b_board, p)
            # both native equations at the maximal proper row: then the cap polynomial of exact-shift-cap is zero
            if m in a_board[0][1:] and m in b_board[0][1:]:
                n_top += 1
                y = letter(m)
                ga, cb = sp.diff(g, y), sp.diff(c, y)
                assert zero(sp.diff(g, y, 2)) and zero(sp.diff(c, y, 2))        # affine in the top proper letter
                ba, bb = proper_blocks(a_board)[0], proper_blocks(b_board)[0]
                for board, deriv, blk in ((a_board, ga, ba), (b_board, cb, bb)):
                    comp = component_board(*blk)
                    L = comp[0][0]
                    aa = blk[1][-1]
                    if L == 0:
                        gc, k = sp.S.One, theta
                    else:
                        gc = right_coframe(comp)
                        k = coefficient(clip(clock(L) * gc, L + 1), L)
                    assert zero(deriv + z ** aa * gc / k), (board, aa)
                La, Lb = ba[0][0] - ba[1][-1], bb[0][0] - bb[1][-1]
                comp_a, comp_b = component_board(*ba), component_board(*bb)

                def ratio(comp, L, p):
                    if L == 0:
                        return theta ** (p - 1)
                    gc = right_coframe(comp)
                    k = coefficient(clip(clock(L) * gc, L + 1), L)
                    return coefficient(clip(clock(L) ** p * gc, L + 1), L) / k
                for p in (2, 3, 4):
                    lhs = sp.diff(coefficient(clip(H ** p * delta, M + 1), m), y)
                    assert zero(lhs - (ratio(comp_a, La, p) - ratio(comp_b, Lb, p))), (a_board, b_board, p)
                # whole cap polynomial vanishes when the maximal-row native equations hold on both sides
                Ha = clock(M)
                scalar_a = coefficient(clip(Ha * g, M), m)
                scalar_b = coefficient(clip(Ha * c, M), m)
                assert zero(scalar_a) and zero(scalar_b)
                full = sp.expand(g * clip(z * Ha * c, M) - c * clip(z * Ha * g, M) - z * operator(g, c, Ha, M))
                assert zero(full)
                n_cap += 1
            n_pairs += 1
    assert n_pairs > 0 and n_top > 0
    print("PASS (C) sc:two-endpoints, sc:component-column, sc:common-top-column, sc:component-ratio, "
          "sc:native-shift-identity on %d coequal pairs (%d with the maximal proper row on both sides)"
          % (n_pairs, n_top))


if __name__ == "__main__":
    check_linearized_coframe()
    check_numerator_blocks()
    check_coequal_identities()
    print("ALL PASS")
