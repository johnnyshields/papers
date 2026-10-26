r"""Paper section `app:coincident` (Positive coincident attachment phases).

The frame of the coincident marked matrix: the cap windows are B_* bordered by tau.

Section: app:coincident, lem:coincident-reader ("All component slots B_1, ..., B_{L-1} have the
class phi = s_{B_*}, where B_* is the actual mark with its common beta tau deleted from both lists.
Put B_0 = B_L = B_*"), read against eq:marked-floor and the band labels of check_marked_band.py.

For every legal case-(a) mark omega = (E, W, v) on a small connected skew E with coincident phase
0 < tau = s = t < u, u >= 2, every row outer of m cells, and every g with g | p, u < g, for which
S = Row_m o E has the heights P(g, u) (HasPHeights in lean/), put L = m p / g and read the full beta
lists X_S, Y_S of S (normalized at its southwest content) on the windows [i g, i g + u], 0 <= i <= L.
The script asserts, from the cell sets alone:

1. tau lies in both full lists X_W, Y_W of the mark, with u in X_W and 0 in Y_W;
2. every internal window 0 < i < L carries exactly B_* = (X_W - tau, Y_W - tau);
3. the bottom window carries (X_W - tau, Y_W): B_* bordered by the column tau;
   the top window carries (X_W, Y_W - tau): B_* bordered by the row L g + tau;
4. X_S starts at N = L g + u and Y_S ends at 0, so the border row and column are the extreme
   betas L g + tau, tau of the marked matrix of check_marked_band.py;
5. the Jacobi-Trudi determinant of B_* is nonzero and equals the Schur function of the single
   interior component of S in each internal window (phi = s_{B_*});
6. deleting the shared beta tau changes the determinant in general (s_W != s_{B_*} occurs), so
   phi = s_{B_*} rests on item 2 (the internal windows carry B_* literally: at a coincident seam
   the row of W ending at tau and the row of the next copy starting at tau merge), not on any
   invariance of a Jacobi-Trudi determinant under deleting a common beta.

The marks come from three sources: every legal one on a small E, every legal one on an E of span at
least 8 in a thin box, and the regroupings of small ones through Row_A (A = 2, 3, check_regroup_
mixed.py), which give the periods A g with A >= 2.
"""
import sys

import sympy as sp

from check_band_single_component import components, interior, row
from check_line_charge import phases
from check_regroup_mixed import (content, legal_marks, min_content, regroup_mixed, skew_shapes,
                                 span)

H = {k: sp.Symbol('h%d' % k) for k in range(1, 40)}


def h(k):
    if k < 0:
        return 0
    if k == 0:
        return 1
    return H[k]


def betas(D):
    """Full beta lists (X, Y) of a skew diagram, normalized at its least content."""
    c0 = min_content(D)
    rows = {}
    for (i, j) in D:
        rows.setdefault(i, []).append(j - i)
    X = sorted((max(r) + 1 - c0 for r in rows.values()), reverse=True)
    Y = sorted((min(r) - c0 for r in rows.values()), reverse=True)
    return X, Y


def jt(X, Y):
    assert len(X) == len(Y)
    return sp.expand(sp.Matrix(len(X), len(Y), lambda a, b: h(X[a] - Y[b])).det())


def has_p_heights(S, g, u):
    c0 = min_content(S)
    N = span(S)
    if not (u < g and N % g == u):
        return False
    L = N // g
    ht = {}
    lo = {}
    hi = {}
    for (i, j) in S:
        c = j - i - c0
        lo[c] = min(lo.get(c, i), i)
        hi[c] = max(hi.get(c, i), i)
    for c in lo:
        ht[c] = hi[c] - lo[c] + 1
    for k in range(u + 1, L * g - g):
        if ht[k + g] != ht[k]:
            return False
    for j in range(L):
        if ht[u + j * g] != 1 or ht[(j + 1) * g - 1] != 1:
            return False
    return True


def window(Z, w, u):
    return sorted((z - w for z in Z if w <= z <= w + u), reverse=True)


def coincident(om):
    s, t = phases(om)
    return om.case == 'a' and om.width() >= 2 and s == t and 0 < s < om.width()


def sources(nmax, rows, cols, wide):
    """Coincident case-(a) marks: every legal one on a small E, every legal one on an E of span
    at least `wide` in a thin box, and the regroupings of small ones through Row_A, A = 2, 3."""
    for E in skew_shapes(nmax, 4, 6):
        for om in legal_marks(E):
            if coincident(om):
                yield om
                for A in (2, 3):
                    omA = regroup_mixed(om, row(A), A)
                    if omA.legal() and coincident(omA) and omA.width() == om.width():
                        yield omA
    for E in skew_shapes(nmax + 3, rows, cols):
        if span(E) < wide:
            continue
        for om in legal_marks(E):
            if coincident(om):
                yield om


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    rows = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    cols = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    cases = {1: 0, 2: 0}
    internal = changed = 0
    for om in sources(nmax, rows, cols, 8):
        E = om.E
        if om.width() >= 2:
            u = om.width()
            tau, p = phases(om)[0], om.period()
            XW, YW = betas(om.W)
            assert XW[0] == u and YW[-1] == 0, (sorted(E), sorted(om.W))
            assert tau in XW and tau in YW, (sorted(E), sorted(om.W), tau)
            Xs = [x for x in XW if x != tau]
            Ys = [y for y in YW if y != tau]
            phi = jt(Xs, Ys)
            assert phi != 0
            if jt(XW, YW) != phi:
                changed += 1
            for m in (2, 3):
                S = om.compose(row(m))
                XS, YS = betas(S)
                for g in range(u + 1, p + 1):
                    if p % g or not has_p_heights(S, g, u):
                        continue
                    A = p // g
                    L = m * A
                    assert span(S) == L * g + u
                    key = (sorted(E), sorted(om.W), om.v, m, g)
                    assert (window(XS, 0, u), window(YS, 0, u)) == (Xs, YW), key
                    assert (window(XS, L * g, u), window(YS, L * g, u)) == (XW, Ys), key
                    assert XS[0] == L * g + u and YS[-1] == 0, key
                    comps = components(interior(S))
                    c0 = min_content(S)
                    for i in range(1, L):
                        assert (window(XS, i * g, u), window(YS, i * g, u)) == (Xs, Ys), key
                        inside = [C for C in comps
                                  if all(c0 + i * g <= content(x) <= c0 + i * g + u - 1 for x in C)]
                        assert len(inside) == 1, key
                        assert jt(*betas(inside[0])) == phi, key
                        internal += 1
                    cases[min(A, 2)] += 1
    print(f"composites with A = 1: {cases[1]}, with A >= 2: {cases[2]}, internal windows: "
          f"{internal}, marks with s_W != s_B*: {changed}")
    assert cases[1] > 0 and cases[2] > 0 and changed > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
