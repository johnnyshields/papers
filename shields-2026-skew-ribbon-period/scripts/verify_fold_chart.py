r"""Paper section `sec:fold` (Finite synchronization and the legal gcd chart).

Targets `thm:fold` (one-chart reconstruction) and `eq:actual-fold`.

Every actual proper positive legal chart `S = L_M o_omega E` with a row or column outer of `M >= 2`
cells on a small inner `E` (all legal marks of every case from `check_regroup_mixed.legal_marks`) is
tested against the theorem's hypotheses read literally: period `p = A g` with `A >= 2`, width
`w = b g + c` with `0 < c < g`, `0 <= b < A`, both full boundary words (read from the beta lists of
`S`) `g`-periodic on `c < k < L g` with `L = M A + b`, and the diagonals `c + j g`, `(j + 1) g - 1`
singletons.  On every chart satisfying them: the window union `G` (the first `g` diagonals with the last
`g` diagonals translated so that the singletons at `N - g` and `c` coincide) is a connected skew
diagram of span `g + c` with singleton ends and area below `|S|`; and, independently of the proof's
construction, a search over all legal width-`c` marks `zeta` on `G` and all `L`-cell row or column
outers (and their antitransposes) finds a composition equal to `S` of score `(c, g + c)`.
Sampled: inners of up to 8 cells.  The hypotheses are met by few
charts; the count is reported, and the script fails if none is found.
`eq:fold-slots`, `eq:fold-cap-budget`, the phase bounds and `eq:old-mark-height` are asserted on
the ordinary case-(a) charts among them (the case-(b) and mixed branches are not covered).
"""
from math import gcd

from check_regroup_mixed import (Mark, add, content, is_cskew, legal_marks, min_content, skew_shapes,
                                 span, sub, translate)
from verify_charts import beta_lists, height_word

def words(S):
    X, Y = beta_lists(S)
    N = span(S)
    return {k: int(k in Y) for k in range(1, N)}, {k: int(k in X) for k in range(1, N)}


def diag_cells(S, k):
    c0 = min_content(S)
    return [x for x in S if content(x) - c0 == k]


def antitranspose(S):
    return frozenset((-j, -i) for i, j in S)


def normalize(S):
    c = min(content(x) for x in S)
    lo = min(x[0] for x in S if content(x) == c)
    return translate((-lo, -(lo + c)), S)


def fold_window_union(S, g, c, N):
    first = [x for x in S if content(x) - min_content(S) < g]
    last = [x for x in S if content(x) - min_content(S) >= N - g]
    s_c = diag_cells(S, c)
    s_n = diag_cells(S, N - g)
    assert len(s_c) == 1 and len(s_n) == 1
    v = sub(s_c[0], s_n[0])
    return frozenset(first) | frozenset(translate(v, last))


nrel = [0]


def check_fold_relations(om, S, g, c, p, w, M, L, N, a_w, b_w, H):
    """`eq:fold-slots`, `eq:fold-cap-budget`, `eq:old-mark-height`, the phase bounds, ordinary source
    in case (a), read literally from the words of `S`."""
    c0 = min_content(om.E)
    cs = sorted(content(x) - c0 for x in om.middle())
    s_, t_ = cs[0], cs[-1] - p + 1
    rho = 0 if S == om.compose(frozenset((0, j) for j in range(M))) else 1
    for j in range(1, M):
        assert a_w[j * p + t_] == rho and b_w[j * p + s_] == rho
    tau, sigma = t_ % g, s_ % g
    A0 = {r: a_w[g + r] for r in range(g)}
    B0 = {r: b_w[g + r] for r in range(g)}
    assert A0[tau] == rho and B0[sigma] == rho                                   # eq:fold-slots
    C = {r: A0[r] - B0[r] for r in range(g)}
    i, j = int(tau > 0), int(sigma < c)
    if rho == 0:
        assert t_ == tau and tau <= c and s_ // g * g + sigma == s_ and sigma <= c
    else:
        assert s_ == sigma and 1 <= sigma <= c and t_ == (t_ // g) * g + tau and tau <= c - 1
    assert C[0] == i * (1 - rho) + rho                                           # eq:fold-cap-budget
    assert -C[c] == rho + j * (1 - rho)
    assert sum(C[r] for r in range(1, c)) + (i - j) * (1 - rho) == 0
    if rho == 0:                                                                 # eq:old-mark-height
        H0 = {r: 1 + sum(C[k] for k in range(1, r + 1)) for r in range(g)}
        Om = [sum(1 for x in om.W if content(x) - c0 == r) for r in range(w)]
        for r in range(w):
            assert Om[r] == H0[r % g] + int(t_ > 0 and r >= t_) - int(r >= s_), (r, Om, H0)


def main():
    found = tested = 0
    for E in skew_shapes(8, 4, 5):
        if len(E) < 2:
            continue
        for om in legal_marks(E):
            w, p = om.width(), om.period()
            if w == 0:
                continue
            for g in range(2, p):
                if p % g or w % g == 0:
                    continue
                A, b, c = p // g, w // g, w % g
                if A < 2 or not 0 <= b < A:
                    continue
                for M in (2, 3):
                    L = M * A + b
                    for outer in (frozenset((0, j) for j in range(M)), frozenset((j, 0) for j in range(M))):
                        S = om.compose(outer)
                        N = span(S)
                        assert N == L * g + c
                        a_w, b_w = words(S)
                        mid = range(c + 1, L * g)
                        if not all(a_w.get(k) == a_w.get(k + g) for k in mid if k + g < L * g) or \
                           not all(b_w.get(k) == b_w.get(k + g) for k in mid if k + g < L * g):
                            continue
                        H = height_word(S)
                        pins = [c + j * g for j in range(L)] + [(j + 1) * g - 1 for j in range(L)]
                        if not all(H[k] == 1 for k in pins if k < N):
                            continue
                        tested += 1
                        G = normalize(fold_window_union(S, g, c, N))
                        assert is_cskew(G) and span(G) == g + c, (sorted(E), sorted(om.W))
                        HG = height_word(G)
                        assert HG[0] == 1 and HG[-1] == 1 and len(G) < len(S)
                        # independent search: legal width-c marks on G, line outers of L cells
                        ok = False
                        for z in legal_marks(G):
                            if z.width() != c:
                                continue
                            for line in (frozenset((0, j) for j in range(L)), frozenset((j, 0) for j in range(L))):
                                for target in (S, antitranspose(S)):
                                    if normalize(z.compose(line)) == normalize(target):
                                        ok = True
                                        assert (c, span(G)) == (z.width(), span(G))
                        assert ok, ("no legal fold chart found", sorted(E), sorted(om.W), om.case, M)
                        found += 1
                        if om.case == 'a':
                            check_fold_relations(om, S, g, c, p, w, M, L, N, a_w, b_w, H)
                            nrel[0] += 1
    print(f"charts meeting the hypotheses {tested}; folded charts found {found}; ordinary relations checked on {nrel[0]}")
    assert tested > 0 and found == tested and nrel[0] > 0
    print("PASS")


if __name__ == "__main__":
    main()
