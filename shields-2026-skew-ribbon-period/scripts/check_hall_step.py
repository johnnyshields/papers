r"""Paper section `app:coincident` (Positive coincident attachment phases).

The terminal Hall operator on the top component of a periodic coincident source.

Section: app:coincident, lem:mark-pair ("the original common terminal Hall operator delta_{N-u}").

The coincident source of L cells with literal marked slots has the top-degree matrix of
check_marked_band.py, with every h_j kept symbolic: rows {L g + tau} u (i g + J), columns
{tau} u (i g + K), entry h_{row - col} zeroed when the row residue is below the column residue.
Its determinant is homogeneous of g-degree L.  With N = L g + u the derivation delta_{N-u} sends
h_j to h_{j-(N-u)}.  The script asserts, on each example and each L, that

    delta_{L g} Top_g(s_S) = eps * s_W * s_B^L,   eps = +1 or -1,

where s_W is the Schur function of the mark (flags J u {tau}, K u {tau}) and s_B the determinant
of the internal marked band (flags J, K).
"""
import sympy as sp

g, u = 5, 3
EXAMPLES = [(1, [3], [0]), (2, [1, 3], [0, 1]), (1, [0, 3], [0, 2])]


def hh(j, H):
    return 0 if j < 0 else (1 if j == 0 else H[j])


def board(X, Y, H):
    return sp.expand(sp.Matrix(len(X), len(Y), lambda a, b: hh(X[a] - Y[b], H)).det())


for tau, J, K in EXAMPLES:
    for L in (1, 2):
        N = L * g + u
        H = {j: sp.Symbol('h%d' % j) for j in range(1, N + 1)}
        rows = [L * g + tau] + [i * g + j for i in range(L + 1) for j in J]
        cols = [tau] + [i * g + k for i in range(L + 1) for k in K]
        M = sp.Matrix(len(rows), len(cols),
                      lambda a, b: 0 if rows[a] % g < cols[b] % g else hh(rows[a] - cols[b], H))
        top = sp.expand(M.det())
        out = sp.expand(sum(sp.diff(top, H[j]) * hh(j - L * g, H) for j in range(L * g, N + 1)))
        sW = board(J + [tau], K + [tau], H)
        sB = board(J, K, H)
        target = sp.expand(sW * sB ** L)
        assert sp.expand(out - target) == 0 or sp.expand(out + target) == 0, (tau, J, K, L)
        print(tau, J, K, 'L', L, 'delta_{Lg} Top = +-', sp.factor(target))
print('ALL PASS')

# Varying band classes.  Each internal marked band carries one of two marked components
# A = (J={1,3}, K={0,1}) or B = (J={3}, K={0}); the end row and column carry the phase tau = 2.
# The product form  delta_{Lg} Top = eps * s_W(c) * prod_{i != c} s_{B_i}  is asserted for the
# band c of some class, where s_W(c) is the Schur function of the mark (J_c u tau, K_c u tau).
import itertools

TAU = 2
CLASSES = {'A': ([1, 3], [0, 1]), 'B': ([3], [0])}
for L in (1, 2):
    N = L * g + u
    H = {j: sp.Symbol('h%d' % j) for j in range(1, N + 1)}
    for pat in itertools.product('AB', repeat=L + 1):
        bands = [CLASSES[c] for c in pat]
        rows = [L * g + TAU] + [i * g + j for i in range(L + 1) for j in bands[i][0]]
        cols = [TAU] + [i * g + k for i in range(L + 1) for k in bands[i][1]]
        M = sp.Matrix(len(rows), len(cols),
                      lambda a, b: 0 if rows[a] % g < cols[b] % g else hh(rows[a] - cols[b], H))
        top = sp.expand(M.det())
        out = sp.expand(sum(sp.diff(top, H[j]) * hh(j - L * g, H) for j in range(L * g, N + 1)))
        sB = [board(J, K, H) for J, K in bands]
        sWc = [board(J + [TAU], K + [TAU], H) for J, K in bands]
        ok = False
        for c in range(L + 1):
            tgt = sWc[c]
            for i in range(L + 1):
                if i != c:
                    tgt = sp.expand(tgt * sB[i])
            if sp.expand(out - tgt) == 0 or sp.expand(out + tgt) == 0:
                ok = True
                break
        assert ok, (L, pat)
print('VARYING CLASSES PASS')
