r"""Paper section `app:cell-cut` (Integral cuts with a cell-only proper interior).

Least-cost monomial of a live cut on the shaved board (`app:cell-cut`, `thm:cell-cut`,
`eq:central-slot-loss`, `eq:all-cut-sign`).

A board `(X, Y)` of `s` rows has strictly decreasing beta lists, `Y_last = 0`, row lengths
`X_i - Y_i >= 1`, adjacent gaps `X_{i+1} - Y_i` in `{0, 1}`, and is upper Hessenberg.  The shaved
board `B_t` deletes the window rows `r` (`X_r = Y_{r-1}` with `t <= Y_{r-1} < L + t`) and their
unit columns `r - 1`.  On `B_t` (of `d` rows) the raw physical cut

    N_t = sum_{i, j : Y_j < t <= X_i - L} h_{X_i - Y_j - L} * cof(i, j)

is read in ordinary degree `d` (every factor `h_k` with `k >= 1`).

Put `p = max{i : X_i >= L + t}`, `q = min{j : Y_j < t}` on `B_t` and `w = X_p - Y_q - L - 1`.  The
script asserts, on every live cut of the census below:

  (1) `p <= q` exist, and the degree-`d` part has a unique least squared-cost monomial: the term of
      the single marked block `[p, q]` with every other row a singleton;
  (2) its raw coefficient is `(-1)^(q - p)` when `w > 0`, and `(-1)^(q - p) * (1 - u - v)` when
      `w = 0`, where `u = [p >= 1 and X_p - Y_{p-1} = 1]`, `v = [q + 1 < d and X_{q+1} - Y_q = 1]`
      are the two one-row extensions of the marked block;
  (3) in the census frame `w = 0` never has exactly one extension (`u = v`), so the coefficient is
      `(-1)^{r_t}` with `r_t = (q - p) + [w = 0 and u = 1]`;
  (4) on the original board, with `G` the lower betas of the gap-one edges, `r_t` is
      `|G cap [t, L + t - 2]| + [t - 1 in G and L + t - 1 in G]`;
  (5) `r_t` is constant over the live cuts of one board, and equals `c - a`, where `c` is the
      number of gap-one edges and `a = |(Y \ X) cap (0, d0)|`.

The census frame is that of `thm_cell_cut`: span `X_0 - Y_last = L + d0 + 1`, `d0 >= 1`, the
unmatched lower betas `Y \ X` are `L`-periodic on `0 < u < d0` and avoid `L - 1` and `d0 + 1`; the
live cuts are `f < t <= g`, `f = [L in Y \ X]`, `g = d0 + 1 - [d0 in Y \ X]`.  The unit transport
(periodicity of the common betas) is not imposed: it is what the signed statement is used to prove.
"""
import itertools
import sys
from collections import defaultdict


def perm_sign(p):
    s, seen = 1, [False] * len(p)
    for i in range(len(p)):
        if not seen[i]:
            j, ln = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                ln += 1
            if ln % 2 == 0:
                s = -s
    return s


def top_part(X, Y, t, L):
    """Degree-`d` part of the raw cut on a `d`-row board, as {sorted index tuple: coefficient}."""
    d = len(X)
    out = defaultdict(int)
    for i in range(d):
        if not X[i] - L >= t:
            continue
        for sig in itertools.permutations(range(d)):
            j = sig[i]
            if not Y[j] < t:
                continue
            idx = [X[k] - Y[sig[k]] - (L if k == i else 0) for k in range(d)]
            if any(v <= 0 for v in idx):
                continue
            out[tuple(sorted(idx))] += perm_sign(sig)
    return {m: c for m, c in out.items() if c != 0}


def cost(m):
    return sum(v * v for v in m)


def window_rows(X, Y, t, L):
    return [r for r in range(1, len(X)) if X[r] == Y[r - 1] and t <= Y[r - 1] < L + t]


def shave(X, Y, W):
    cols = {r - 1 for r in W}
    return ([x for r, x in enumerate(X) if r not in W],
            [y for k, y in enumerate(Y) if k not in cols])


def boards(s, top):
    for Y in itertools.combinations(range(top, -1, -1), s):
        if Y[-1] != 0:
            continue
        for gaps in itertools.product((0, 1), repeat=s - 1):
            X = [None] * s
            for i in range(1, s):
                X[i] = Y[i - 1] + gaps[i - 1]
            for x0 in range(Y[0] + 1, top + 2):
                X[0] = x0
                if any(X[i] <= Y[i] for i in range(s)):
                    continue
                if any(X[i] <= X[i + 1] for i in range(s - 1)):
                    continue
                if any(X[i] >= Y[j] for i in range(s) for j in range(s) if j + 1 < i):
                    continue
                yield tuple(X), tuple(Y)


def main():
    n_cut = n_board = n_w0 = 0
    for s in (1, 2, 3, 4, 5, 6):
        for L in (2, 3, 4):
            for X, Y in boards(s, 9):
                d0 = X[0] - Y[-1] - L - 1
                if d0 < 1:
                    continue
                Yr = set(Y) - set(X)
                if any((u in Yr) != (u + L in Yr) for u in range(1, d0)):
                    continue
                if L - 1 in Yr or d0 + 1 in Yr:
                    continue
                f = 1 if L in Yr else 0
                g = d0 + 1 - (1 if d0 in Yr else 0)
                c = sum(1 for i in range(s - 1) if X[i + 1] - Y[i] == 1)
                a = len([u for u in Yr if 0 < u < d0])
                rs = set()
                for t in range(f + 1, g + 1):
                    Xs, Ys = shave(X, Y, window_rows(X, Y, t, L))
                    d = len(Xs)
                    assert d >= 1, (X, Y, L, t)
                    n_cut += 1
                    P = [i for i in range(d) if Xs[i] >= L + t]
                    Q = [j for j in range(d) if Ys[j] < t]
                    assert P and Q, (X, Y, L, t)
                    p, q = max(P), min(Q)
                    assert p <= q, (X, Y, L, t)
                    w = Xs[p] - Ys[q] - L - 1
                    assert w >= 0
                    u = int(p >= 1 and Xs[p] - Ys[p - 1] == 1)
                    v = int(q + 1 < d and Xs[q + 1] - Ys[q] == 1)
                    top = top_part(Xs, Ys, t, L)
                    assert top, (X, Y, L, t, 'empty top part')
                    mc = min(cost(m) for m in top)
                    least = [m for m in top if cost(m) == mc]
                    assert len(least) == 1, (X, Y, L, t, least)
                    mu = least[0]
                    pred = sorted([Xs[k] - Ys[k] for k in range(d) if not p <= k <= q]
                                  + [Xs[p] - Ys[q] - L] + [1] * (q - p))
                    assert tuple(pred) == mu, (X, Y, L, t, pred, mu)
                    coef = (-1) ** (q - p) * ((1 - u - v) if w == 0 else 1)
                    assert top[mu] == coef, (X, Y, L, t, top[mu], coef)
                    if w == 0:
                        n_w0 += 1
                        assert u == v, (X, Y, L, t, 'blind', u, v)
                    r_t = (q - p) + (1 if w == 0 and u == 1 else 0)
                    assert top[mu] == (-1) ** r_t
                    cnt = sum(1 for k in range(s - 1)
                              if X[k + 1] - Y[k] == 1 and t <= Y[k] <= L + t - 2)
                    G = {Y[k] for k in range(s - 1) if X[k + 1] - Y[k] == 1}
                    w0 = int((t - 1) in G and (L + t - 1) in G)
                    assert r_t == cnt + w0, (X, Y, L, t, r_t, cnt, w0)
                    rs.add(r_t)
                if rs:
                    n_board += 1
                    assert rs == {c - a}, (X, Y, L, sorted(rs), c, a)
    print(f'boards {n_board}, live cuts {n_cut}, cuts with w = 0: {n_w0}')
    assert n_board > 0 and n_w0 > 0
    print('PASS')


if __name__ == '__main__':
    sys.exit(main())
