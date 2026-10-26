r"""Paper section `app:cell-cut` (Integral cuts with a cell-only proper interior).

Probe of the shaved-board top statement (`app:cell-cut`, `thm:cell-cut`, `eq:all-cut-sign`).

For a board `(X, Y)` of `s` rows (strictly decreasing beta lists, `Y_last = 0`, row lengths
`X_i - Y_i >= 1`, adjacent gaps `X_{i+1} - Y_i` in `{0, 1}`, upper Hessenberg: `X_i < Y_j` for
`j + 1 < i`) and a cut `t`, the window rows are the
rows `r` with `X_r = Y_{r-1}` and `t <= Y_{r-1} < L + t`.  The shaved board `B_t` deletes them and
their unit columns `r - 1`.  On `B_t` (of `d` rows) the physical cut

    N_t = sum_{i, j : Y_j < t <= X_i - L} h_{X_i - Y_j - L} * cof(i, j)

is read in ordinary degree `d` (every `h` index positive).  The script checks:

  (1) the degree-`d` part equals the cut computed with `h_0` replaced by zero, which then factors
      over the blocks of `B_t` separated by gap-zero (and negative) subdiagonal entries;
  (1b) it is the sum over the blocks `K` of the cut of block `K` times the determinants of the
      other blocks, all with `h_0 = 0` (the cut is a derivation-type sum over marked entries);
  (2) the degree-`d` part is nonzero and has a unique least squared-cost monomial, of
      coefficient `+1` or `-1`;
  (3) that coefficient is the same for every live cut of one board.

Only boards in the frame of `thm_cell_cut` are used: span `X_0 - Y_last = L + d + 1` with
`d >= 1`; the unmatched lower betas `Y \ X` are `L`-periodic on `0 < u < d` and avoid `L - 1` and
`d + 1`; the live cuts are `f < t <= g` with `f = [L in Y \ X]`, `g = d + 1 - [d in Y \ X]`.

Each check is reported separately; a failure of (1)-(3) is printed with its board.
"""
import itertools
import sys
from functools import lru_cache

import sympy as sp

H = sp.symbols('h1:40')


def h(k, zero_h0=False):
    if k < 0:
        return sp.Integer(0)
    if k == 0:
        return sp.Integer(0) if zero_h0 else sp.Integer(1)
    return H[k - 1]


def det(M):
    n = len(M)
    if n == 0:
        return sp.Integer(1)
    return sp.Matrix(M).det(method='berkowitz')


def phys_cut(X, Y, t, L, zero_h0=False):
    s = len(X)
    tot = sp.Integer(0)
    for i in range(s):
        for j in range(s):
            if Y[j] < t <= X[i] - L:
                minor = [[h(X[a] - Y[b], zero_h0) for b in range(s) if b != j]
                         for a in range(s) if a != i]
                tot += (-1) ** (i + j) * h(X[i] - Y[j] - L, zero_h0) * det(minor)
    return sp.expand(tot)


def window_rows(X, Y, t, L):
    return [r for r in range(1, len(X)) if X[r] == Y[r - 1] and t <= Y[r - 1] < L + t]


def shave(X, Y, W):
    cols = {r - 1 for r in W}
    return ([x for r, x in enumerate(X) if r not in W],
            [y for k, y in enumerate(Y) if k not in cols])


def deg_part(P, d):
    P = sp.Poly(P, *H)
    out = {}
    for mon, c in P.terms():
        if sum(mon) == d and c != 0:
            out[mon] = c
    return out


def cost(mon):
    return sum(k * (i + 1) ** 2 for i, k in enumerate(mon))


def blocks(X, Y):
    """Row index sets of the blocks: split where the subdiagonal entry h_{X_{i+1}-Y_i} has
    index at most zero."""
    out, cur = [], [0]
    for i in range(len(X) - 1):
        if X[i + 1] - Y[i] <= 0:
            out.append(cur)
            cur = []
        cur.append(i + 1)
    out.append(cur)
    return out


def boards(s, top):
    for Y in itertools.combinations(range(top, -1, -1), s):
        if Y[-1] != 0:
            continue
        for gaps in itertools.product((0, 1), repeat=s - 1):
            X = [None] * s
            ok = True
            for i in range(1, s):
                X[i] = Y[i - 1] + gaps[i - 1]
            for x0 in range(Y[0] + 1, top + 2):
                X[0] = x0
                Xs = list(X)
                if any(Xs[i] <= Y[i] for i in range(s)):
                    continue
                if any(Xs[i] <= Xs[i + 1] for i in range(s - 1)):
                    continue
                if any(Xs[i] >= Y[j] for i in range(s) for j in range(s) if j + 1 < i):
                    continue
                yield tuple(Xs), tuple(Y)


def main():
    n_cut = n1 = n1b = n2 = n3 = 0
    fail1b = []
    fail1, fail2, fail3 = [], [], []
    for s in (2, 3, 4, 5):
        for L in (2, 3):
            for X, Y in boards(s, 8):
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
                signs = set()
                for t in range(f + 1, g + 1):
                    W = window_rows(X, Y, t, L)
                    Xs, Ys = shave(X, Y, W)
                    d = len(Xs)
                    if d == 0:
                        continue
                    N = phys_cut(Xs, Ys, t, L)
                    n_cut += 1
                    top = deg_part(N, d)
                    # (1) top part = cut with h0 -> 0
                    N0 = phys_cut(Xs, Ys, t, L, zero_h0=True)
                    top0 = deg_part(N0, d)
                    if top0 != top or sp.expand(N0 - sum(
                            c * sp.Mul(*[H[i] ** k for i, k in enumerate(m)])
                            for m, c in top.items())) != 0:
                        fail1.append((X, Y, L, t))
                    else:
                        n1 += 1
                    bl = blocks(Xs, Ys)
                    sub = lambda K: ([Xs[i] for i in K], [Ys[i] for i in K])
                    dets = [det([[h(Xs[a] - Ys[b], True) for b in K] for a in K]) for K in bl]
                    fact = sum(phys_cut(*sub(K), t, L, zero_h0=True) *
                               sp.Mul(*[dets[l] for l in range(len(bl)) if l != k])
                               for k, K in enumerate(bl))
                    if sp.expand(fact - N0) != 0:
                        fail1b.append((X, Y, L, t))
                    else:
                        n1b += 1
                    # (2) unique least-cost monomial with unit coefficient
                    if not top or N == 0:
                        fail2.append((X, Y, L, t, 'empty'))
                        continue
                    mc = min(cost(m) for m in top)
                    least = [m for m in top if cost(m) == mc]
                    if len(least) != 1 or abs(top[least[0]]) != 1:
                        fail2.append((X, Y, L, t, len(least), [top[m] for m in least]))
                        continue
                    n2 += 1
                    signs.add(int(top[least[0]]))
                if len(signs) > 1:
                    fail3.append((X, Y, L, sorted(signs)))
                elif signs:
                    n3 += 1
    print(f'cuts {n_cut}; (1) ok {n1}, fail {len(fail1)}; (1b) ok {n1b}, fail {len(fail1b)}; (2) ok {n2}, fail {len(fail2)}; '
          f'(3) boards ok {n3}, fail {len(fail3)}')
    for tag, F in (('1', fail1), ('1b', fail1b), ('2', fail2), ('3', fail3)):
        for row in F[:5]:
            print(f'FAIL({tag})', row)
    assert n_cut > 0
    if fail1 or fail1b or fail2 or fail3:
        sys.exit(1)
    print('PASS')


if __name__ == '__main__':
    main()
