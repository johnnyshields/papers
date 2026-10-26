r"""Paper section `sec:whole-sign` (Whole-determinant noncancellation).

Targets `lem:shift-sign` and `eq:shift-sign` (subsection on feasibility and signs in the
original orders).

For every connected skew diagram `S` in a bounded box, with full beta lists `X, Y` of span `N`,
every row `x` and every shift `q >= 1` with `w_0 = x - q >= 0` not already in `X`, the literal
replacement determinant `R_x` (row `x` replaced in place by label `w_0`, `h_0 = 1`) is built as
a polynomial in `h_1, ..., h_N` and its sign is read independently of the lemma: the
lexicographic leading monomial for `h_N >> ... >> h_1`, with every positive generator negative.
The same is done for every column `y` shifted to `v_0 = y + q <= N` not already in `Y`.  Asserted:
the replacement is nonzero and its sorted lists are weakly feasible; and its sign relative to the
reference `(-1)^{eta(X, Y)}` (the reference itself read off the determinant of `S`) equals both
displayed forms of `eq:shift-sign`, the interval-count form and the height form, with `H_S`
the height word of `S`.  Sampled, not exhaustive: diagrams up to 8 cells in 3 rows and 4 columns.
"""
import sympy as sp

from check_regroup_mixed import skew_shapes, span
from check_contact_currents import beta_lists
from verify_charts import height_word


def lex_sign(M, gens):
    P = sp.Poly(sp.expand(M.det()), *reversed(gens))
    assert not P.is_zero
    mon = P.monoms(order='lex')[0]
    return int(sp.sign(P.coeff_monomial(mon))) * (-1) ** sum(mon)


def main():
    nrow = ncol = 0
    for S in skew_shapes(8, 3, 4):
        if len(S) < 2:
            continue
        X, Y = beta_lists(S)
        N = X[0]
        gens = sp.symbols(f"h1:{N + 1}")

        def h(j):
            return sp.Integer(0) if j < 0 else (sp.Integer(1) if j == 0 else gens[j - 1])
        H = height_word(S)
        ref = lex_sign(sp.Matrix(len(X), len(Y), lambda i, j: h(X[i] - Y[j])), gens)
        for i, x in enumerate(X):
            for q in range(1, x + 1):
                w0 = x - q
                if w0 in X:
                    continue
                Xn = list(X)
                Xn[i] = w0
                M = sp.Matrix(len(Xn), len(Y), lambda a, b: h(Xn[a] - Y[b]))
                srt = sorted(Xn, reverse=True)
                assert all(srt[k] >= Y[k] for k in range(len(Y)))                 # weakly feasible
                sgn = lex_sign(M, gens) * ref
                a = sum(1 for z in X if w0 < z < x) + sum(1 for z in Y if w0 <= z < x)
                b = H[w0] - H[x - 1] + (1 if w0 in Y else 0)
                assert sgn == (-1) ** a == (-1) ** b, (sorted(S), 'row', x, q)
                nrow += 1
        for j, y in enumerate(Y):
            for q in range(1, N - y + 1):
                v0 = y + q
                if v0 in Y:
                    continue
                Yn = list(Y)
                Yn[j] = v0
                M = sp.Matrix(len(X), len(Yn), lambda a, b: h(X[a] - Yn[b]))
                srt = sorted(Yn, reverse=True)
                assert all(X[k] >= srt[k] for k in range(len(X)))
                sgn = lex_sign(M, gens) * ref
                a = sum(1 for z in Y if y < z < v0) + sum(1 for z in X if y < z <= v0)
                b = H[y] - H[v0 - 1] + (1 if v0 in X else 0)
                assert sgn == (-1) ** a == (-1) ** b, (sorted(S), 'col', y, q)
                ncol += 1
    print(f"row shifts {nrow}, column shifts {ncol}")
    assert nrow > 0 and ncol > 0
    print("PASS")


if __name__ == "__main__":
    main()
