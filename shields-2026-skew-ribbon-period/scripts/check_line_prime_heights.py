r"""Paper section `app:coincident` (Positive coincident attachment phases).

`LinePrimeHeights` (`lean/SkewRibbonPeriod/Reduction/One/PairHeights.lean`, appendix
`app:coincident`, `lem:one-coincident-entry`).

This script documents that the height-profile form of the statement is FALSE, and checks the form
the descent induction consumes.

Part 1.  Ribbons are enumerated by composition and grouped by ribbon Schur function.  For two
reversal classes `D`, `D'` in one group and a legal line mark `omega`, the parents `omega o D` and
`omega o D'` have the same height multiset but, for the smallest pair (compositions (1,2,1,3,2) and
(1,3,2,1,2), line mark on 3 cells), a profile that is neither equal nor reversed; and `P(g, u)` does
not transfer from one to the other when `g` does not divide the period of `omega`.

Part 2.  The form consumed: `F = omega o D` for a line mark `omega` (possibly empty) and a ribbon
`D`, `g | period(omega)`, `P(g, u)` on `F` implies that `F` is a ribbon or `D` is a line.  Checked
over every ribbon of at most 8 cells and every row or column line mark of at most 7 cells.  A line is
determined by its Schur function among connected skew diagrams, so a Schur-equal second outer is a
translate and the parents are translates of each other.
"""
import itertools
import sys
from collections import defaultdict

from check_regroup_mixed import Mark, content, legal_marks, min_content, vH


def compositions(n):
    for mask in range(1 << (n - 1)):
        out, cur = [], 1
        for i in range(n - 1):
            if mask >> i & 1:
                out.append(cur)
                cur = 1
            else:
                cur += 1
        out.append(cur)
        yield tuple(out)


def schur_key(alpha):
    """Ribbon Schur function in the h-basis: alternating sum over coarsenings."""
    k = len(alpha)
    acc = defaultdict(int)
    for mask in range(1 << (k - 1)):
        parts, cur = [], alpha[0]
        for i in range(k - 1):
            if mask >> i & 1:
                cur += alpha[i + 1]
            else:
                parts.append(cur)
                cur = alpha[i + 1]
        parts.append(cur)
        acc[tuple(sorted(parts, reverse=True))] += (-1) ** (k - len(parts))
    return frozenset((p, c) for p, c in acc.items() if c)


def ribbon(alpha):
    cells, col = set(), 0
    for r, a in enumerate(alpha):
        cells |= {(r, c) for c in range(col - a + 1, col + 1)}
        col = col - a + 1
    return frozenset(cells)


def profile(S):
    c0 = min_content(S)
    n = len({content(x) for x in S})
    return tuple(sum(1 for x in S if content(x) == c0 + k) for k in range(n))


def main(maxn=12, maxline=9):
    from check_top_seam_form import heights_ok
    groups = defaultdict(list)
    for n in range(2, maxn + 1):
        for a in compositions(n):
            groups[(n, schur_key(a))].append(a)
    pairs = []
    for g in groups.values():
        cl = sorted({min(a, a[::-1]) for a in g})
        pairs += list(itertools.combinations(cl, 2))
    assert pairs
    marks = {n: list(legal_marks(frozenset((0, j) for j in range(n)))) for n in range(2, maxline + 1)}
    bad, pfail, pcases, pl3 = [], [], 0, 0
    for a, b in pairs:
        D, D2 = ribbon(a), ribbon(b)
        for n, ms in marks.items():
            for om in ms:
                F, H = om.compose(D), om.compose(D2)
                p, q = profile(F), profile(H)
                assert sorted(p) == sorted(q)
                if not (p == q or p == q[::-1]):
                    bad.append((sum(a), n, a, b, sorted(om.W), om.v))
                for g in range(2, len(p) + 1):
                    for u in range(g):
                        x = heights_ok(F, g, u)
                        if x is None:
                            continue
                        pcases += 1
                        pl3 += x >= 3
                        if heights_ok(H, g, u) != x:
                            pfail.append((a, b, n, g, u, x))
    bad.sort(key=lambda t: (t[0], t[1]))
    print("pairs", len(pairs), "profile failures", len(bad), "P cases", pcases,
          "with L>=3", pl3, "P transfer failures", len(pfail))
    # The height-profile statement fails: smallest counterexample.
    assert bad and bad[0][:3] == (9, 3, (1, 2, 1, 3, 2)) and bad[0][3] == (1, 3, 2, 1, 2)
    # P transfer fails only at L <= 2 among the tested pairs.
    assert pfail and all(t[5] <= 2 for t in pfail)
    part2()
    print("ALL PASS (documents the failure of the profile statement)")


def line_marks(n):
    for E in (frozenset((0, j) for j in range(n)), frozenset((j, 0) for j in range(n))):
        yield from legal_marks(E)
        yield Mark(E, frozenset(), vH(E), 'a')


def is_line_diagram(D):
    return len({x[0] for x in D}) == 1 or len({x[1] for x in D}) == 1


def part2():
    from check_top_seam_form import heights_ok
    marks = [om for n in range(2, 8) for om in line_marks(n)]
    cases = 0
    for m in range(1, 9):
        for a in compositions(m):
            D = ribbon(a)
            for om in marks:
                F = om.compose(D)
                P = om.period()
                if P == 0:
                    continue
                ribbon_F = len(F) == len({content(x) for x in F})
                for g in range(1, len({content(x) for x in F}) + 1):
                    if P % g:
                        continue
                    for u in range(g):
                        if heights_ok(F, g, u) is None:
                            continue
                        cases += 1
                        assert ribbon_F or is_line_diagram(D), (a, sorted(om.E), sorted(om.W), om.v, g, u)
    assert cases > 0
    print("part 2 cases", cases)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 12, int(sys.argv[2]) if len(sys.argv) > 2 else 9)
