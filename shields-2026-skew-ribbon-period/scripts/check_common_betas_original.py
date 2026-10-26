r"""Paper section `app:aligned` (`lem:conormal-caps`, `eq:capped-core-quotient`): common betas of the original source.

The end windows of the section (`EndWindowListsT`) ask for a connected U' of span q = span U with
the row map of the empty mark of U, such that the entries of X_E strictly between 0 and q lie in X_U'
and Y_U' is in Y_E.  For literal composites E = J o U this is checked in check_end_window_lists.py and
check_end_window_transport.py.  Here the source E ranges over the whole Schur class of a composite
E0 = J o_eta U (equal Schur function, equal span, by exhaustive enumeration of connected skew shapes
of bounded area), so that E has common betas that no literal composition produces.  For each such E
the script decides whether some U' of the row map of U serves (full windows) and whether the common
betas of E in (0,q) alone lie in X_U' for the U' that serves the non-common entries.
"""
import random
import sys

from check_end_window_lists import compose
from check_end_window_transport import comp, empty_v
from check_row_probe_caps import betas, connected, is_skew, normalize, random_skew

P = (1 << 61) - 1
rng0 = random.Random(5)
H = [[1] + [rng0.randrange(1, P) for _ in range(40)] for _ in range(2)]


def hval(t, k):
    return 0 if k < 0 else H[t][k]


def det_mod(M):
    n = len(M)
    M = [r[:] for r in M]
    d = 1
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] % P), None)
        if p is None:
            return 0
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d = d * M[c][c] % P
        inv = pow(M[c][c], P - 2, P)
        for r in range(c + 1, n):
            f = M[r][c] * inv % P
            if f:
                for k in range(c, n):
                    M[r][k] = (M[r][k] - f * M[c][k]) % P
    return d % P


def lists_xz(cells):
    rows = {}
    for i, j in cells:
        rows.setdefault(i, []).append(j)
    ks = sorted(rows)
    xi = [max(rows[i]) + 1 - r for r, i in enumerate(ks)]
    ze = [min(rows[i]) - r for r, i in enumerate(ks)]
    return xi, ze


def schur(cells):
    xi, ze = lists_xz(cells)
    return tuple(det_mod([[hval(t, x - z) for z in ze] for x in xi]) for t in range(2))


def shapes(area, nrows=None):
    """All connected skew shapes (cells normalized) of the given area (and row count)."""
    out = []

    def rec(rows, left):
        if nrows is not None and len(rows) > nrows:
            return
        if left == 0:
            if nrows is None or len(rows) == nrows:
                out.append(normalize({(-k, j) for k, (a, b) in enumerate(rows) for j in range(a, b + 1)}))
            return
        if nrows is not None and len(rows) == nrows:
            return
        la, ra = rows[-1]
        for lb in range(la, ra + 1):
            for rb in range(ra, ra + left):
                if rb - lb + 1 <= left:
                    rec(rows + [(lb, rb)], left - (rb - lb + 1))

    for l0 in range(1, area + 1):
        rec([(0, l0 - 1)], area - l0)
    return list(set(out))


_cache = {}


def shapes_c(area, nrows=None):
    if (area, nrows) not in _cache:
        _cache[(area, nrows)] = shapes(area, nrows)
    return _cache[(area, nrows)]


def span(cells):
    return betas(cells)[0][0]


def rowmap(U, v):
    return tuple(schur(compose(frozenset((0, c) for c in range(j)), U, v)) for j in (1, 2, 3))


def nrows(cells):
    return len({i for i, _ in cells})


def main():
    amax = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    rng = random.Random(11)
    fail_plainU = withz = tested = noncomp = fail_full = fail_common = 0
    first_fail = None
    seen = set()
    inner_pool = [s for A in range(2, 7) for s in shapes_c(A) if empty_v(s) is not None]
    for _ in range(3000):
        U = rng.choice(inner_pool)
        J = random_skew(rng, rng.randint(1, 3))
        if not (is_skew(J) and connected(J)):
            continue
        R, q = span(J), span(U)
        if R < 2 or q < 2:
            continue
        v = empty_v(U)
        E0 = compose(J, U, v)
        A = len(E0)
        if A > amax or not (is_skew(E0) and connected(E0)) or span(E0) != R * q:
            continue
        if (E0, U) in seen:
            continue
        seen.add((E0, U))
        key = schur(E0)
        rm = rowmap(U, v)
        Us = [W for W in shapes_c(len(U)) if empty_v(W) is not None and span(W) == q
              and rowmap(W, empty_v(W)) == rm]
        for E in shapes_c(A, nrows(E0)):
            if span(E) != R * q or schur(E) != key:
                continue
            xE, yE = betas(E)
            X, Y = set(xE), set(yE)
            tested += 1
            noncomp += not any(compose(J2, U2, empty_v(U2)) == E
                               for U2 in Us for J2 in [J])
            ok = [W for W in Us if all(x in set(betas(W)[0]) for x in X if 0 < x < q)
                  and set(betas(W)[1]) <= Y]
            if not ok:
                fail_full += 1
                if first_fail is None or len(E) < len(first_fail[0]):
                    first_fail = (E, U, J)
            zc = [x for x in X & Y if 0 < x < q]
            plainU = all(x in set(betas(U)[0]) for x in zc) and set(betas(U)[1]) <= Y
            fail_plainU += not plainU
            withz += bool(zc)
            if zc and not any(all(x in set(betas(W)[0]) for x in zc) for W in ok):
                fail_common += 1
    print("source classes", len(seen), "tested", tested, "non-literal", noncomp,
          "full-window failures", fail_full, "common-beta failures", fail_common, "with common betas in (0,q)", withz, "against the original U (not a transport) fail", fail_plainU)
    if first_fail:
        E, U, J = first_fail
        print("smallest failure: E", sorted(E), "U", sorted(U), "J", sorted(J), "q", span(U))
    assert tested > 50 and withz > 0
    assert fail_common == 0, "common betas of the original source escape every transported inner"


if __name__ == "__main__":
    main()
