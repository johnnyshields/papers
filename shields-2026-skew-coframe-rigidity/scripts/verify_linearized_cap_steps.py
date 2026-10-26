r"""Paper section `sec:unit-restoration` (Complete unit restoration), inside the proof of `sc:linearized-cap`.
Targets `sc:linearized-prefix`, `sc:linearized-zero-range`, `sc:linearized-direct-zeros`,
`sc:strict-block-variation`.

Physical letters, h_0 = 1, as in the theorem.  Objects are built from full flags (`_coframes`).

  (A) `sc:linearized-prefix` at every cut, not only the whole proper matrix.  For every connected zero-free
      board through span SPAN_A, every prefix P made of the first k strict proper blocks (least column a), and
      random rational weights on the vacancies below a and zero above it (the induction has removed those),
      the exact first variation Q of the coframe satisfies
          Q_prefix = -P^{-1} (sum_{j<a} h_{x-j} Q_j)_{x in rows P}.
      Control: a nonzero weight on a vacancy above a breaks the formula on some board, so the zero weights
      above the prefix are a load-bearing input.
  (B) `sc:linearized-zero-range` as the implication the proof uses, with GENERIC coefficients.  For every
      connected zero-free cap K through span CAP_B, every child span m through M_B and every raw ceiling
      R < m: give Q = sum_{j<m} q_j z^j independent unknown coefficients (functions of letters through R
      only), impose that every coefficient of a letter h_k with k > max(R, v-1) in [z^{m+v}] H C_K Q vanish,
      and solve.  Asserted: the solution space is exactly {q_j = 0 for j < m+v-max(R, v-1)}, every other
      q_j free; so the range is sharp from these equations, and R < v forces Q = 0.
  (C) `sc:linearized-direct-zeros`: for R >= v, the indices m-R and x-R (every proper row x < m) lie in the
      range of (B), symbolically in m, R, v and x.
  (D) `sc:strict-block-variation` as a polynomial identity in SYMBOLIC weights.  For every connected
      zero-free board through span SPAN_D and every cut into a prefix P and next strict block E (head t,
      least column a_0) in the branch R = t > S of the proof, put independent symbols rho_b on the
      vacancies of E, impose the direct zeros of (C) (Q_{m-t} = 0 and Q_{x-t} = 0 for x in rows P) as
      polynomial identities in the letters, which are linear equations on the weights, solve them, and
      differentiate [H Q]_m in h_t for the constrained weights.  Asserted: the derivative is
      s_E sdot_N - s_N sdot_E times a nonzero factor free of every rho_b, where N is the numerator with the
      stated flags and sdot is the weighted restoration polynomial of `sc:restoration-polynomial`; so the
      vanishing derivative is exactly the displayed equation.  Control: without the direct zeros the
      derivative is not proportional to it on some cut.
"""
import random

import sympy as sp

from _coframes import (
    z, letter, right_coframe, left_coframe, clock, coefficient, clip, matrix, raw, zero, connected,
    connected_boards, determinant, restoration_polynomial,
)
from verify_proof_identities import proper_blocks

random.seed(20261103)

SPAN_A = 7
CAP_B = 4
M_B = 7
SPAN_D = 9


def first_variation(board, weights):
    """Q = -sum_b rho_b P_b (z^b - sum_s (D_0^{-1} v_b)_s z^s), P_b = [H G]_b (`sc:linearized-coframe`)."""
    rows, cols = board
    m = rows[0]
    g = right_coframe(board, unit=1)
    H = clock(m, unit=1)
    I, S = rows[1:], cols[:-1]
    D0inv = matrix(I, S, unit=1).inv() if I else None
    Q = sp.S.Zero
    for b, w in weights.items():
        if w == 0:
            continue
        Pb = coefficient(clip(H * g, m), b)
        feedback = sp.S.Zero
        if I:
            solved = D0inv * sp.Matrix([raw(i - b, 1) for i in I])
            feedback = sp.Add(*(sp.cancel(c) * z ** s for c, s in zip(solved, S)))
        Q += w * (-Pb * (z ** b - feedback))
    return sp.expand(Q)


def prefix_formula_holds(board, weights, k):
    rows, cols = board
    m = rows[0]
    blocks = proper_blocks(board)
    rowsP = tuple(x for blk in blocks[:k] for x in blk[0])
    colsP = tuple(y for blk in blocks[:k] for y in blk[1])
    a = colsP[-1]
    Q = first_variation(board, weights)
    low = {j: sp.cancel(Q.coeff(z, j)) for j in range(a)}
    rhs = -matrix(rowsP, colsP, unit=1).inv() * sp.Matrix(
        [sp.Add(*(raw(x - j, 1) * low[j] for j in range(a))) for x in rowsP])
    return all(zero(Q.coeff(z, s) - c) for s, c in zip(colsP, rhs))


def check_prefix():
    n_cuts = n_control = 0
    for span in range(2, SPAN_A + 1):
        for board in connected_boards(span):
            rows, cols = board
            if set(rows) & set(cols) or len(rows) < 2:
                continue
            vac = [b for b in range(1, span) if b not in rows and b not in cols]
            if not vac:
                continue
            blocks = proper_blocks(board)
            for k in range(1, len(blocks) + 1):
                a = blocks[k - 1][1][-1]
                below = [b for b in vac if b < a]
                above = [b for b in vac if b > a]
                weights = {b: sp.Rational(random.randint(1, 9), random.randint(1, 4)) * random.choice((1, -1))
                           for b in below}
                if below:
                    assert prefix_formula_holds(board, weights, k), (board, k)
                    n_cuts += 1
                if above:
                    bad = dict(weights)
                    bad[above[-1]] = sp.Integer(1)
                    if not prefix_formula_holds(board, bad, k):
                        n_control += 1
    assert n_cuts > 20 and n_control > 0, (n_cuts, n_control)
    print("PASS (A) sc:linearized-prefix at %d (board, prefix cut) pairs through span %d; a weight above the "
          "prefix breaks it on %d" % (n_cuts, SPAN_A, n_control))


def zero_free_caps(vmax):
    for v in range(1, vmax + 1):
        for K in connected_boards(v):
            if not set(K[0]) & set(K[1]):
                yield v, K


def check_zero_range():
    n = 0
    for v, K in zero_free_caps(CAP_B):
        CK = sp.expand(left_coframe(K, unit=1))
        for m in range(2, M_B + 1):
            q = sp.symbols("q0:%d" % m)
            Q = sp.Add(*(q[j] * z ** j for j in range(m)))
            H = 1 + sp.Add(*(letter(k) * z ** k for k in range(1, m + v + 1)))
            E = sp.expand(H * CK * Q).coeff(z, m + v)
            for R in range(1, m):
                Rp = max(R, v - 1)
                eqs = [sp.expand(sp.diff(E, letter(k))) for k in range(Rp + 1, m + v + 1)]
                # the high letters enter only through H, so E is affine in each of them
                assert all(sp.diff(E, letter(k), 2) == 0 for k in range(Rp + 1, m + v + 1))
                sol = sp.solve(eqs, q, dict=True) if eqs else [{}]
                assert len(sol) == 1, (K, m, R)
                sol = sol[0]
                assert all(zero(val) for val in sol.values()), (K, m, R, sol)
                forced = {j for j in range(m) if q[j] in sol}
                expected = {j for j in range(m) if j < m + v - Rp}
                assert forced == expected, (K, m, R, forced, expected)
                if R < v:
                    assert expected == set(range(m))
                n += 1
    print("PASS (B) sc:linearized-zero-range: Q_j = 0 exactly for j < m+v-max(R,v-1), on %d (cap, m, R) cases "
          "with generic coefficients; R < v gives Q = 0" % n)


def check_direct_zeros():
    m, R, v, x = sp.symbols("m R v x", integer=True, positive=True)
    # R >= v, so max(R, v-1) = R and the range is j < m + v - R
    bound = m + v - R
    assert sp.simplify(bound - (m - R)) == v                     # m - R is v below the bound, v >= 1
    # a proper row satisfies x <= m - 1, so x - R <= m - 1 - R < bound
    assert sp.simplify(bound - (m - 1 - R)) == v + 1
    print("PASS (C) sc:linearized-direct-zeros: m-R and x-R (x < m) lie in the zero range whenever R >= v")


def check_strict_block_variation():
    n_ok = n_control = n_vacuous = 0
    for span in range(4, SPAN_D + 1):
        for board in connected_boards(span):
            rows, cols = board
            if set(rows) & set(cols):
                continue
            blocks = proper_blocks(board)
            for k in range(1, len(blocks)):
                rowsP = tuple(x for blk in blocks[:k] for x in blk[0])
                colsP = tuple(y for blk in blocks[:k] for y in blk[1])
                rowsE, colsE = blocks[k]
                t, a0, a = rowsE[0], colsE[-1], colsP[-1]
                if rowsP[0] - a >= t or span - t >= a:
                    continue            # S >= t, or the zero range already passes a: the other branch
                kill = {span - t} | {x - t for x in rowsP}
                assert all(j < a for j in kill)
                vac = [b for b in range(a0 + 1, t) if b not in rows and b not in cols]
                if not vac:
                    continue
                rho = {b: sp.Symbol("rho%d" % b) for b in vac}
                Q = first_variation(board, rho)
                # the direct zeros as polynomial identities in the letters: linear equations on the weights
                eqs = []
                for j in kill:
                    num = sp.numer(sp.together(Q.coeff(z, j)))
                    hs = sorted(num.free_symbols - set(rho.values()), key=str)
                    eqs += sp.Poly(sp.expand(num), *hs).coeffs() if hs else [num]
                syms = list(rho.values())
                eqs = [e for e in eqs if e != 0]
                sol = list(sp.linsolve(eqs, syms)) if eqs else [tuple(syms)]
                assert len(sol) == 1, (board, k)
                rho_d = dict(zip(rho, sol[0]))
                free = set().union(*(sp.sympify(v).free_symbols for v in rho_d.values())) & set(rho.values())
                if not free:
                    n_vacuous += 1
                    continue
                H = clock(span, unit=1)
                Qd = first_variation(board, rho_d)
                assert all(zero(Qd.coeff(z, j)) for j in kill)
                lhs = sp.cancel(sp.diff(coefficient(clip(H * Qd, span + 1), span), letter(t)))
                raw_lhs = sp.cancel(sp.diff(coefficient(clip(H * Q, span + 1), span), letter(t)))
                XN = tuple(sorted((span,) + rowsP + tuple(x for x in rowsE if x != t), reverse=True))
                YN = tuple(sorted(colsP + colsE, reverse=True))
                Nb = (tuple(x - a0 for x in XN), tuple(y - a0 for y in YN))
                Eb = (tuple(x - a0 for x in rowsE), tuple(y - a0 for y in colsE))
                assert connected(Nb) and connected(Eb)
                sN, sE = determinant(Nb, unit=1), determinant(Eb, unit=1)
                dN = sp.Add(*(rho_d[b] * restoration_polynomial(Nb, b - a0) for b in vac))
                dE = sp.Add(*(rho_d[b] * restoration_polynomial(Eb, b - a0) for b in vac))
                target = sp.expand(sE * dN - sN * dE)
                assert target != 0, (board, k)
                ratio = sp.cancel(lhs / target)
                assert ratio != 0 and not (ratio.free_symbols & set(rho.values())), (board, k, ratio)
                n_ok += 1
                rawN = sp.Add(*(rho[b] * restoration_polynomial(Nb, b - a0) for b in vac))
                rawE = sp.Add(*(rho[b] * restoration_polynomial(Eb, b - a0) for b in vac))
                raw_ratio = sp.cancel(raw_lhs / sp.expand(sE * rawN - sN * rawE))
                if raw_ratio.free_symbols & set(rho.values()):
                    n_control += 1
    assert n_ok >= 10 and n_control > 0, (n_ok, n_control)
    print("PASS (D) sc:strict-block-variation: the h_t-derivative is s_E sdot_N - s_N sdot_E times a weight-free "
          "nonzero factor at %d cuts through span %d (%d more where the direct zeros force every weight to "
          "zero); without the direct zeros it is not, at %d" % (n_ok, SPAN_D, n_vacuous, n_control))


if __name__ == "__main__":
    check_prefix()
    check_zero_range()
    check_direct_zeros()
    check_strict_block_variation()
    print("ALL PASS")
