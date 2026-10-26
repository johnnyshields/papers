r"""Paper section `sec:whole-sign` (Whole-determinant noncancellation).

Consumer step of `thm:scalar-synchronization` and `eq:unit-inclusion`.

The theorem excludes every nonzero weighted private term by a one-sign argument.  Here the sign is
recomputed independently of `eq:shift-sign`: for sampled periodic sources (words `p`-periodic on the open middle,
heights `q`-periodic on `c <= j < a`, singleton pins), every private row shift `k + q -> k` (unit at `k + q`,
vacancy at `k`, `c < k < a`) is formed as the actual sorted list pair and its sign is the sorting sign (number of lists entries jumped over) times `(-1)^{eta(X', Y)}`, with
`eta` the count of `weak-sign`; the same for private column shifts.  Asserted: each such sign equals the
reference `(-1)^{eta(X, Y)}` (relative sign `+1`), so the Hall sums over private row shifts and over private
column shifts each have one sign and are nonzero exactly when a shift survives; hence a vanishing Hall
sum forces `1_{k+q in X} <= 1_{k in X}` (row) and `1_{k in Y} <= 1_{k+q in Y}` (column) on `c < k < a`,
which are the two inclusions of `eq:unit-inclusion` read on the unit sets.  Control: sources violating the
inclusion have a nonzero sum (counted).  The cap shifts, the end-pole filter and the identification of
`Z_{s+}`, `Z_{s-}` with the common-beta sets of the two splices need the comparison and are not covered.
"""
import random

from _source_common import heights, sample


def eta(X, Y):
    m = len(X)
    return sum(1 for i in range(m) for j in range(i + 1) if X[i] > Y[j])


def main():
    rng = random.Random(31)
    n = nrow = ncol = nviol = nincl = 0
    tries = 0
    while n < 300 and tries < 3000000:
        tries += 1
        s = sample(rng, want_pins=False, period='p')
        X, Y, N, c, q, a = (s[k] for k in ('X', 'Y', 'N', 'c', 'q', 'a'))
        H = heights(X, Y, N)
        if not all(H[j] == H[j + q] for j in range(c, a)):
            continue
        n += 1
        ref = (-1) ** eta(X, Y)
        Xs, Ys = set(X), set(Y)
        row_terms, col_terms = [], []
        for k in range(c + 1, a):
            if (k + q) in Xs and k not in Xs:
                X2 = sorted((Xs - {k + q}) | {k}, reverse=True)
                assert all(x >= y for x, y in zip(X2, Y))
                swaps = sum(1 for z in X if k < z < k + q)      # the literal replacement keeps the old row position
                row_terms.append((-1) ** (eta(X2, Y) + swaps) * ref)
            if k in Ys and (k + q) not in Ys:
                Y2 = sorted((Ys - {k}) | {k + q}, reverse=True)
                assert all(x >= y for x, y in zip(X, Y2))
                swaps = sum(1 for z in Y if k < z < k + q)
                col_terms.append((-1) ** (eta(X, Y2) + swaps) * ref)
        assert all(t == 1 for t in row_terms), 'row private shift sign'
        assert all(t == 1 for t in col_terms), 'column private shift sign'
        nrow += len(row_terms)
        ncol += len(col_terms)
        incl_row = all((k + q in Xs) <= (k in Xs) for k in range(c + 1, a))
        incl_col = all((k in Ys) <= (k + q in Ys) for k in range(c + 1, a))
        assert incl_row == (not row_terms) and incl_col == (not col_terms)
        nincl += incl_row + incl_col
        nviol += (not incl_row) + (not incl_col)
    print(f"sources {n}; private row shifts {nrow}; column shifts {ncol}; inclusions holding {nincl}; violating (nonzero sum) {nviol}")
    assert n > 0 and nrow > 0 and nviol > 0
    print("PASS")


if __name__ == "__main__":
    main()
