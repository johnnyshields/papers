r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Literal core quotient (prop:noncell-realization, eq:capped-core-quotient), empty mark.

Test of the literal statement behind the section argument: for a connected inner U with its empty
mark eta (period q = N_U) and a connected J, every connected H Schur-equal to G = J o_eta U is a
translate of J' o_eta' U' for a connected J' and a mark eta' in {eta, rotated eta}, "transported eta".
The script enumerates all pairs with |G| <= AREA, reports every H of the class that has no such
presentation, and, for each, whether U has a finer proper empty-mark chart (period dividing q).
It asserts that every failure has U decomposable (U itself a composite) or G presented through an
inner of another area, i.e. (J, eta) is not source-minimal; the statement is claimed only for
source-minimal charts.
"""
import itertools
import sys
from fractions import Fraction

from check_row_probe_caps import normalize, is_skew, connected, content, betas
import check_noncell_section as c

AREA = int(sys.argv[1]) if len(sys.argv) > 1 else 12
HV = {m: Fraction((m * 7919) % 31 + 2, (m * 104729) % 17 + 3) for m in range(1, 60)}


def partitions_le(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for p in partitions_le(n - k, k):
            yield (k,) + p


def skews(n):
    """All connected skew diagrams of area n, normalized: rows (a_i, b_i), a and b weakly
    decreasing downward, consecutive rows overlapping in a column."""
    out = set()

    def rec(rows, left):
        if left == 0:
            cells = {(i, j) for i, (a, b) in enumerate(rows) for j in range(a, b)}
            out.add(normalize(cells))
            return
        for ln in range(1, left + 1):
            if not rows:
                rec([(0, ln)], left - ln)
            else:
                pa, pb = rows[-1]
                for b2 in range(pa + 1, pb + 1):
                    a2 = b2 - ln
                    if a2 <= pa:
                        rec(rows + [(a2, b2)], left - ln)
    rec([], n)
    return out


def rot(D):
    mi = max(i for i, _ in D)
    mj = max(j for _, j in D)
    return normalize({(mi - i, mj - j) for i, j in D})


def vH(U):
    cs = [content(x) for x in U]
    lo, hi = min(cs), max(cs)
    sw = min((x for x in U if content(x) == lo))
    ne = min((x for x in U if content(x) == hi))
    sw = (min(i for i, j in U if j - i == lo),) ; swr = sw[0]
    swc = (swr, swr + lo)
    ner = min(i for i, j in U if j - i == hi)
    nec = (ner, ner + hi)
    return (nec[0] - swc[0], nec[1] - swc[1] + 1)


def compose(J, U):
    v = vH(U)
    cells = set()
    for (i, j) in J:
        k = j - i
        o = (k * v[0] + i, k * v[1] + i)
        for (a, b) in U:
            cells.add((a + o[0], b + o[1]))
    return normalize(cells)


HV2 = {m: Fraction((m * 6007) % 37 + 3, (m * 15485863) % 19 + 2) for m in range(1, 60)}
HV3 = {m: Fraction((m * 3571) % 41 + 1, (m * 32452843) % 23 + 5) for m in range(1, 60)}


def schur_key(D):
    return (c.schur(D, HV), c.schur(D, HV2), c.schur(D, HV3))


def composite(U, cache={}):
    """U = D o E' with an empty horizontal mark on a smaller connected E' (or its rotation)."""
    key = U
    if key in cache:
        return cache[key]
    n = len(U)
    res = False
    for m in range(2, n // 2 + 1):
        if n % m:
            continue
        for E in skews(m):
            for e in (E, rot(E)):
                for D in skews(n // m):
                    G = compose(D, e)
                    if len(G) == n and is_skew(G) and G in (U, rot(U)):
                        res = True
                        break
                if res:
                    break
            if res:
                break
        if res:
            break
    cache[key] = res
    return res


def main():
    by_area = {}
    def S(n):
        if n not in by_area:
            by_area[n] = skews(n)
        return by_area[n]
    fails = 0
    total = 0
    bad = []

    def decomposable(U):
        n = len(U)
        for a in range(2, n):
            if n % a:
                continue
            for U2 in S(a):
                for e in (U2, rot(U2)):
                    for J2 in S(n // a):
                        G2 = compose(J2, e)
                        if len(G2) == n and (G2 == U or rot(G2) == U):
                            return True
        return False
    def other_chart(G, nU, Ucur):
        """G has a presentation J2 o e with an inner of another area: then (U, J) need not be
        source-minimal, and the literal statement is only claimed for source-minimal charts."""
        n = len(G)
        for a in range(2, n):
            if n % a:
                continue
            for U2 in S(a):
                for e in (U2, rot(U2)):
                    if a == nU and (e == Ucur or rot(e) == Ucur):
                        continue
                    for J2 in S(n // a):
                        G2 = compose(J2, e)
                        if len(G2) == n and (G2 == G or rot(G2) == G):
                            return True
        return False
    for nU in range(2, AREA // 2 + 1):
        for nJ in range(2, AREA // nU + 1):
            n = nU * nJ
            if n > AREA:
                continue
            allH = S(n)
            cls = {}
            for H in allH:
                cls.setdefault(schur_key(H), []).append(H)
            pres = set()
            for U in S(nU):
                for eta in (U, rot(U)):
                    for J in S(nJ):
                        G = compose(J, eta)
                        if is_skew(G) and connected(G) and len(G) == n:
                            pres.add(G)
                            pres.add(rot(G))
            for U in S(nU):
                if len({i for i, _ in U}) == 1 or len({j for _, j in U}) == 1:
                    continue  # a line inner is a separate branch
                if composite(U):
                    continue  # the inner of a source-minimal chart has no finer chart
                for J in S(nJ):
                    G = compose(J, U)
                    if not (is_skew(G) and connected(G) and len(G) == n):
                        continue
                    total += 1
                    allowed = {normalize(compose(Jp, e)) for Jp in S(nJ) for e in (U, rot(U))
                               if is_skew(compose(Jp, e)) and connected(compose(Jp, e))}
                    allowed |= {rot(x) for x in allowed}
                    for H in cls[schur_key(G)]:
                        if H not in allowed:
                            fails += 1
                            print("NO PRESENTATION", "U", sorted(U), "J", sorted(J), "H", sorted(H))
                            if not decomposable(U) and not other_chart(G, nU, U):
                                bad.append((sorted(U), sorted(J), sorted(H)))
    print("instances", total, "failures", fails, "failures with U indecomposable and G with no other inner", len(bad))
    assert total > 0
    assert not bad, bad[:3]   # a failure with U indecomposable is a counterexample to the literal statement
    print("PASS")


main()
