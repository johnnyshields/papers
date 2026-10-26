r"""Paper section `sec:unit-restoration` (Complete unit restoration), inside the proof of `sc:linearized-cap`,
and `sec:fixed-caps`, inside the proof of `sc:fixed-cap`.  Targets the quotient inside `sc:strict-block-variation`
and `sc:fcp-numerator-flags`.

The inverse column of the complete proper matrix selected by the head row t of a strict block E, closed by
a cut so that nothing below it overlaps E from above, has top row-replacement quotient
    (row0 . T^{-1})_t = +- s_N / (det P . s_E),
where row0 = (h_{m-s})_s is the top row, P is the common proper prefix of the blocks above E, N is the
numerator board with rows {m} u rows(P) u (rows(E) \ {t}) and columns cols(P) u cols(E), and s_E is the Schur
function of E translated to start at its least column.  The lower suffix determinants cancel as a whole.

For every connected zero-free board through span SPAN_MAX with at least two strict proper blocks, every
block E after the first (so P is nonempty), and two random rational points: the entry of row0 T^{-1} at row t,
computed by solving the full proper system, equals plus or minus s_N / (det P s_E).  Both signs occur (the
sign is the sorting sign of the numerator board and is not asserted here).  Blocks with a nonempty suffix are
included, so the cancellation of the lower suffix is part of what is compared.
"""
import random
from fractions import Fraction

from verify_fixed_cap_census import boards, det, hval, rand_letters, schur, evaluate
from verify_linearized_and_grades import restore, sigma, vacancies, zero_free, adjugate_form, deg_part

SPAN_MAX = 9
random.seed(20261102)


def proper_blocks(board):
    rows, cols = board
    R, C = rows[1:], cols[:-1]
    cuts = [k for k in range(1, len(R)) if R[k] < C[k - 1]]
    bounds = [0] + cuts + [len(R)]
    return [(R[a:b], C[a:b]) for a, b in zip(bounds, bounds[1:])]


def solve_row(T, row0):
    """Solve y T = row0 for the row vector y (i.e. y = row0 T^{-1})."""
    n = len(T)
    m = [[T[i][j] for i in range(n)] + [row0[j]] for j in range(n)]       # transpose system
    for c in range(n):
        p = next(i for i in range(c, n) if m[i][c] != 0)
        m[c], m[p] = m[p], m[c]
        inv = 1 / m[c][c]
        m[c] = [v * inv for v in m[c]]
        for i in range(n):
            if i != c and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[c])]
    return [m[i][n] for i in range(n)]


def translate(b, t):
    return tuple(x - t for x in b[0]), tuple(y - t for y in b[1])


def main():
    n = 0
    signs = set()
    for span in range(4, SPAN_MAX + 1):
        for B in boards(span):
            if not zero_free(B):
                continue
            blocks = proper_blocks(B)
            if len(blocks) < 2:
                continue
            rows, cols = B
            I, S = rows[1:], cols[:-1]
            for k in range(1, len(blocks)):
                rowsP = tuple(x for blk in blocks[:k] for x in blk[0])
                colsP = tuple(y for blk in blocks[:k] for y in blk[1])
                rowsE, colsE = blocks[k]
                t, a0 = rowsE[0], colsE[-1]
                XN = tuple(sorted((span,) + rowsP + tuple(x for x in rowsE if x != t), reverse=True))
                YN = tuple(sorted(colsP + colsE, reverse=True))
                E = translate((rowsE, colsE), a0)
                for _ in range(2):
                    L = rand_letters(span + 2)
                    T = [[hval(L, x - s) for s in S] for x in I]
                    row0 = [hval(L, span - s) for s in S]
                    y = solve_row(T, row0)
                    q = y[I.index(t)]
                    sN = evaluate(schur((XN, YN)), L)
                    sE = evaluate(schur(E), L)
                    P = [[hval(L, x - s) for s in colsP] for x in rowsP]
                    dP = det(P)
                    assert dP != 0 and sE != 0
                    signs.add(1 if q == sN / (dP * sE) else -1 if q == -sN / (dP * sE) else 0)
                    n += 1
    assert n > 30 and signs <= {1, -1}, signs
    print("%d (board, block) Cramer quotients equal +-s_N/(det P s_E), the suffix cancelling; signs seen %s" % (n, sorted(signs)))
    print("ALL PASS")


if __name__ == "__main__":
    main()
