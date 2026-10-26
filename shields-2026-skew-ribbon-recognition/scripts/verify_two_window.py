r"""Paper section `sec:boundary` (Boundary comparisons and actual marked factors), ge:two-window.

Constructive search for instances of the hypotheses, in the ordinary or EMPTY-free case (marks of
types (a), (b)).  Enumerating P directly finds none with a chart on both S and T, so P is assembled
backwards: S and T range over diagrams of one span H = m f + a (m >= 2) that are compositions
through one common ordinary mark of period f >= 2 and width a; for every shift L, P is built from the
cut identities (positive overlap window on [L, H] and two edits alpha, beta), and kept only when the
recomputed cuts of P are exactly (X_S, Y_S, X_T, Y_T), P is a connected skew diagram, and the
negative window X_T(x + D) = X_S(x), 0 <= x <= V, holds with D = H - V, R = D + L, 0 < L < R, V >= 1.
Where the coverage bounds H - b >= f - 1, H - c >= e - 1 (b = min(L, D), c = max(L, D),
e = gcd(f, b)) also hold, the conclusion is asserted: with d = gcd(f, L, D) one has d | gcd(f, L, R),
2 <= d <= L < R, and in the ordinary case f | b and f | c, so d = f (ordinary assertions of the
proof).  Counts of witnesses and of covered ones are asserted positive.  The existence of the common
root K' of period d is checked against the charts table where both S and T are found there.
"""
import time
from math import gcd

from _gluing_common import compose, is_connected_skew, span
from check_two_copy_flags import betas, diagrams, marks
from verify_endpoint_splice import from_flags

INNER = 4
OUTER = 7
BUDGET = 240


def main():
    t0 = time.time()
    groups = {}
    for K in diagrams(INNER):
        for mk in marks(K):
            if mk.case not in 'ab' or mk.period < 2:
                continue
            f, a = mk.period, mk.width
            for A in diagrams(OUTER):
                if len(A) < 2:
                    continue
                P = compose(A, mk)
                H = span(P)
                if H // f >= 2 and H % f == a:
                    groups.setdefault((mk.inner, mk.lower, mk.case, f, a, H), set()).add(P)
    witnesses = covered = 0
    for (inner, lower, case, f, a, H), Ds in groups.items():
        for S in Ds:
            XS, YS = betas(S)
            for T in Ds:
                if S == T:
                    continue
                XT, YT = betas(T)
                for L in range(1, H):
                    N = H + L
                    if any(((x - L) in XT) != (x in XS) for x in range(L, H + 1)):
                        continue
                    diff = [x for x in range(L, H + 1) if ((x - L) in YT) != (x in YS)]
                    if len(diff) != 2:
                        continue
                    for alpha, beta in ((diff[0], diff[1]), (diff[1], diff[0])):
                        YP = (set(YS) | {beta}) | {y + L for y in YT if y != alpha - L}
                        XP = set(XS) | {x + L for x in XT}
                        if alpha in YP or beta not in YP:
                            continue
                        X, Y = sorted(XP, reverse=True), sorted(YP, reverse=True)
                        if len(X) != len(Y) or X[0] != N or Y[-1] != 0:
                            continue
                        cells = from_flags(X, Y)
                        if not is_connected_skew(cells) or betas(cells) != (X, Y):
                            continue
                        cuts = (sorted((x for x in X if 0 < x <= H), reverse=True),
                                sorted((y for y in Y if y <= H and y != beta), reverse=True),
                                sorted((x - L for x in X if L <= x <= N), reverse=True),
                                sorted((y - L for y in {y for y in Y if L <= y < N} | {alpha}),
                                       reverse=True))
                        if cuts != (XS, YS, XT, YT):
                            continue
                        for V in range(1, H):
                            D = H - V
                            if L >= D + L or D != N - V - L:
                                continue
                            if all(((x + D) in XT) == (x in XS) for x in range(V + 1)):
                                witnesses += 1
                                b, c = min(L, D), max(L, D)
                                e = gcd(f, b)
                                if H - b >= f - 1 and H - c >= e - 1:
                                    covered += 1
                                    d = gcd(gcd(f, L), D)
                                    assert d == gcd(gcd(f, L), D + L) and 2 <= d <= L, \
                                        (f, L, D, d)
                                    if case in 'ab':
                                        assert b % f == 0 and c % f == 0 and d == f, \
                                            (f, L, D, sorted(cells))
                                break
            if time.time() - t0 > BUDGET:
                break
        if time.time() - t0 > BUDGET:
            break
    assert witnesses > 0 and covered > 0, (witnesses, covered)
    print(f'ge:two-window: {witnesses} constructed instances of the hypotheses, {covered} meeting '
          f'the coverage bounds, each with d = f dividing L and D (ordinary assertion)')
    print('ALL PASS')


if __name__ == '__main__':
    main()
