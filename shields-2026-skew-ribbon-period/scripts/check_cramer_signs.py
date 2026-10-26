r"""Cramer multiplier table (`app:contacts`, `eq:contact-cramer-signs`, `eq:contact-numerator-boards`,
`eq:contact-anchor-forcing`, `lem:contact-leading`).

For zero-free connected skew cores `V` (full lists `X, Y`), contacts `0 <= t < r <= m` (a contact is
a core label or a shared unit absent from both core lists) and every vacancy `z` of the core,
`A_z`, `G_z` are computed from the anchor-only matrix (`check_contact_currents.anchor_forcing`,
the top `nu`-coefficient of the forcing).  The numerator boards of `eq:contact-numerator-boards`
are built literally and their determinants taken at the sampled alphabet:
`F_z = ((X \ r) + z) over (Y + r if eps_r)` and `G_z = (X + t if eps_t) over ((Y \ t) + z)`.
Asserted: `A_z det D = +-det F_z` and `G_z det D = +-det G_z`, with the sign equal to the
displayed multiplier of `eq:contact-cramer-signs` in all four `(eps_t, eps_r)` rows
(`A_I(x)`, `A_C(x)` counted on the anchor lists `I_0`, `C_0`), and the boards' heights are the core
  Sampled: cores up to 8 cells in at most
4 rows and 4 columns, `z` in `(t, r)` (the interior domain of the lemma).
"""
import sympy as sp

import check_contact_currents as cc
from check_contact_currents import anchor_forcing, zero_free_diagrams


def det_board(rows, cols):
    rows, cols = sorted(rows, reverse=True), sorted(cols, reverse=True)
    assert len(rows) == len(cols) and len(set(rows)) == len(rows) and len(set(cols)) == len(cols)
    return sp.Matrix(len(rows), len(rows), lambda i, j: cc.h(rows[i] - cols[j])).det(), rows, cols


def main():
    tally = {}
    for D, X, Y in zero_free_diagrams(8, 4, 4):
        m = X[0]
        vac = [z for z in range(1, m) if z not in X and z not in Y]
        for r in range(1, m + 1):
            for t in range(0, r):
                if (r not in X and r in Y) or (t not in Y and t in X):
                    continue
                eps_r = 0 if r in X else 1
                eps_t = 0 if t in Y else 1
                I0 = sorted((set(X) - {r}) | ({t} if eps_t else set()), reverse=True)
                C0 = sorted((set(Y) - {t}) | ({r} if eps_r else set()), reverse=True)
                Dm = sp.Matrix(len(I0), len(I0), lambda i, j: cc.h(I0[i] - C0[j])).det() if I0 else sp.Integer(1)
                AI = lambda x: sum(1 for i in I0 if i > x)
                AC = lambda x: sum(1 for j in C0 if j > x)
                for z in vac:
                    if not t < z < r:
                        continue
                    A, G, _, _ = anchor_forcing(X, Y, r, t, z)
                    dF, rF, cF = det_board(set(X) - {r} | {z}, set(Y) | ({r} if eps_r else set()))
                    dG, rG, cG = det_board(set(X) | ({t} if eps_t else set()), (set(Y) - {t}) | {z})
                    assert dF != 0 and dG != 0
                    sa, sg = sp.sign(A * Dm / dF), sp.sign(G * Dm / dG)
                    assert abs(A * Dm / dF) == 1 and abs(G * Dm / dG) == 1, (sorted(D), r, t, z)
                    ma = (-1) ** (AI(z) + AC(t)) if eps_t == 0 else -((-1) ** (AI(t) - AI(z)))
                    mg = (-1) ** (AI(r) + AC(z)) if eps_r == 0 else -((-1) ** (AC(z) - 1 - AC(r)))
                    assert sa == ma, ('A', eps_t, eps_r, sorted(D), r, t, z, sa, ma)
                    assert sg == mg, ('G', eps_t, eps_r, sorted(D), r, t, z, sg, mg)
                    tally[(eps_t, eps_r)] = tally.get((eps_t, eps_r), 0) + 1
    print("cases by (eps_t, eps_r):", tally)
    assert set(tally) == {(0, 0), (0, 1), (1, 0), (1, 1)}
    print("PASS")


if __name__ == "__main__":
    main()
