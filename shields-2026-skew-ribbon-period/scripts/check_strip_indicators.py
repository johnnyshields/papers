r"""Paper section `app:cell-cut` (Integral cuts with a cell-only proper interior).

`eq:strip-indicators` and the difference formula before it, transcribed literally.

For every cell-only board (as in `verify_cell_cut`) with full lists `X, Y`, row count `s`, span `S`, and every
`L` with `R = S - L >= 1`: `N_t` is the marked-entry cofactor sum with indicator `y_j < t <= x_i - L`
(`verify_cell_cut.marked_cut`), `N_0 = N_{R+1} = 0`; `R_x` is the raw replacement determinant of the row
`x` by the label `x - L` and `C_y` of the column `y` by `y + L` (`h_0 = 1`, negative labels zero, in the
original orders), set to zero when the source label is absent.  Asserted: `N_{e+1} - N_e =
(-1)^{s-1}(C_e - R_{L+e})` for `0 <= e <= R`; and the indicators of `eq:strip-indicators`: the outer-strip replacement
`R_{L+e}` is nonzero as a polynomial only if `1_X(L+e)(1 - 1_X(e)) = 1` and the inner-strip `C_e` only
if `1_Y(e)(1 - 1_Y(L+e)) = 1`; the converse (indicator one implies nonzero) is asserted too.
Ambiguity reported: the text defines `R_x` as nonzero when the label is "present" and the indicator also
requires the shifted label `e` (resp. `L+e`) to be free; here that is read as the duplicate-row/column
vanishing, which is exactly the indicator.  Sampled: boards as in `verify_cell_cut`.
"""
import sympy as sp

from verify_cell_cut import Hs, boards, h, lists, marked_cut


def raw_row(X, Y, x, w):
    i = X.index(x)
    Xn = list(X)
    Xn[i] = w
    return sp.expand(sp.Matrix(len(X), len(Y), lambda a, b: h(Xn[a] - Y[b])).det())


def raw_col(X, Y, y, v):
    j = Y.index(y)
    Yn = list(Y)
    Yn[j] = v
    return sp.expand(sp.Matrix(len(X), len(Y), lambda a, b: h(X[a] - Yn[b])).det())


def main():
    n = nd = ni = 0
    for lens, gaps in boards():
        X, Y = lists(lens, gaps)
        s, S = len(X), X[0]
        for L in range(1, S):
            R = S - L
            N = {0: 0, R + 1: 0}
            for t in range(1, R + 1):
                N[t] = marked_cut(X, Y, L, t)
            for e in range(0, R + 1):
                Rv = raw_row(X, Y, L + e, e) if (L + e) in X else 0
                Cv = raw_col(X, Y, e, L + e) if e in Y else 0
                assert sp.expand(N[e + 1] - N[e] - (-1) ** (s - 1) * (Cv - Rv)) == 0, (lens, gaps, L, e)
                nd += 1
                indR = int((L + e) in X and e not in X)
                indC = int(e in Y and (L + e) not in Y)
                assert (Rv != 0) == bool(indR), ('outer strip indicator', lens, gaps, L, e)
                assert (Cv != 0) == bool(indC), ('inner strip indicator', lens, gaps, L, e)
                ni += 1
        n += 1
    print(f"boards {n}; difference identities {nd}; indicator checks {ni}")
    assert nd > 0
    print("PASS")


if __name__ == "__main__":
    main()
