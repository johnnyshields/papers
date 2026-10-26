r"""Paper section `sec:boundary` (Boundary comparisons and actual marked factors), ge:terminal-signed.

J is an ordinary finer inner (case (a) mark mu of period r, width 0 < v < r, contacts s, t,
epsilon = v - s - t >= 0, N = r + v).  The data of the statement are constructed from J, never
chosen: for h with r <= h < N and 2r > N, put L = N - h, D = h - v = r - L and require
1 <= L <= s <= v - t; for each column j >= r of J, k = j + epsilon <= h and ell = N - k <= v a row
of J; the child cuts are
    X_S = X_J n (0, h],   Y_S = (Y_J n [0, h]) \ {j},
    X_T = ((X_J n [L, N]) \ {ell}) - L,   Y_T = (Y_J n [L, N)) - L.
They are kept when S and T are connected diagrams and the two comparisons signed-W and signed-G of the
paper hold exactly with (H, R, V, p, q) = (h, r, v, s, t) -- they hold on every constructed instance,
which is checked.  The statement's "actual whole-child equality" is the Schur equality s_S = s_T,
imposed as a hypothesis.  The conclusion is then asserted: J is self-rotational (its mark equals its
half-turn), or J has an actual proper chart of period d | r, d < r, with score
(v mod d, d + v mod d) below (v, r + v).  The chart is looked up in a table of compositions.

Control: the instances without s_S = s_T are counted, and some of them are neither self-rotational
nor improved, so the equality is what carries the conclusion.  The mixed-upper branch and the
untransported orientations of the statement are not run.
"""
from _gluing_common import compose, rotated_mark, schur
from check_two_copy_flags import betas, diagrams, marks, phases
from verify_endpoint_splice import from_flags
from _gluing_common import is_connected_skew

CELLS = 11
TABLE_IN = 6
TABLE_OUT = 7


def build(X, Y):
    if len(X) != len(Y) or not X:
        return None
    cells = from_flags(X, Y)
    if not is_connected_skew(cells) or betas(cells) != (X, Y):
        return None
    return cells


def ind(L, n):
    return [1 if x in L else 0 for x in range(n + 1)]


def main():
    table = {}
    for K in diagrams(TABLE_IN):
        for nu in marks(K):
            for A in diagrams(TABLE_OUT):
                if len(A) >= 2 and len(A) * len(K) <= 14:
                    table.setdefault(compose(A, nu), set()).add((nu.period, nu.width))
    held = unheld_bad = holds_self = holds_chart = 0
    for J in diagrams(CELLS):
        XJ, YJ = betas(J)
        for mu in marks(J):
            if mu.case != 'a' or not mu.lower:
                continue
            r, v = mu.period, mu.width
            s, t = phases(mu)
            N, eps = r + v, v - s - t
            if eps < 0 or 2 * r <= N:
                continue
            for h in range(r, N):
                L, D = N - h, h - v
                if not 1 <= L <= s <= v - t:
                    continue
                for j in YJ:
                    k = j + eps
                    ell = N - k
                    if j < r or k > h or ell > v or ell not in XJ:
                        continue
                    XS = sorted((x for x in XJ if 0 < x <= h), reverse=True)
                    YS = sorted((y for y in YJ if 0 <= y <= h and y != j), reverse=True)
                    XT = sorted((x - L for x in XJ if L <= x <= N and x != ell), reverse=True)
                    YT = sorted((y - L for y in YJ if L <= y < N), reverse=True)
                    S, T = build(XS, YS), build(XT, YT)
                    if S is None or T is None:
                        continue
                    xs, ys, xt, yt = ind(XS, h + 1), ind(YS, h + 1), ind(XT, h + 1), ind(YT, h + 1)
                    assert all(xt[x + D] - xs[x] == (x == s) and yt[x + D] - ys[x] == -(x == t)
                               for x in range(v + 1)), 'signed-W'
                    assert all(xt[x - L] - xs[x] == -(x == ell) and yt[x - L] - ys[x] == (x == j)
                               for x in range(L, h + 1)), 'signed-G'
                    selfrot = rotated_mark(mu) == mu
                    better = any(p < r and r % p == 0 and p >= 2
                                 and (v % p, p + v % p) < (v, r + v)
                                 for p, _ in table.get(J, set()))
                    if schur(S) == schur(T):
                        held += 1
                        assert selfrot or better, (sorted(J), r, v, s, t, h, j)
                        holds_self += selfrot
                        holds_chart += (not selfrot)
                    elif not (selfrot or better):
                        unheld_bad += 1
    assert held > 0 and unheld_bad > 0
    print(f'ge:terminal-signed: {held} instances with s_S = s_T ({holds_self} self-rotational, '
          f'{holds_chart} improving); {unheld_bad} instances without it are neither (control)')
    print('ALL PASS')


if __name__ == '__main__':
    main()
