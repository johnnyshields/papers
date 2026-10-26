"""Support and disjointness of the returned-coordinate charts (ph:source-chart).

Paper section `sec:comparison` (Finite comparisons on actual composition charts), ph:ordinary-flags,
ph:mixed-flags, ph:ordinary-source-chart, ph:mixed-source-chart.

For every small period r, finer width v < r, contact pair, lower lists X_W, Y_W and private
lists B_-, C_- inside (v, r), and coarse span M >= 3, build the finer flags and check:

* the outside exponents (M - a) r + i, 1 <= a <= M - 1, over the available inputs i (missing
  rows for numerator waves, present columns for denominator waves, v < i < N_J) are distinct
  and lie strictly between N_J and S = M r + v;
* no outside exponent equals a returned exponent s + j r, 1 <= j <= M, on the side carrying the
  returned part;
* every returned exponent s + j r either exceeds N_J or is a slot where the seed coefficient
  vanishes: a present finer row (ordinary numerator) or an absent finer column (mixed
  denominator).  In particular r + s < N_J happens, so a degree bound alone does not separate
  the returned part from the seed.
"""

from itertools import combinations


def subsets(lo, hi):
    """All subsets of the integers in [lo, hi)."""
    pts = list(range(lo, hi))
    for k in range(len(pts) + 1):
        for c in combinations(pts, k):
            yield set(c)


def check(r, v, M, ordinary):
    count = 0
    lowered = 0
    NJ = r + v
    S = M * r + v
    for XW in subsets(0, v + 1):
        for YW in subsets(0, v + 1):
            if len(XW) != len(YW) or not XW:
                continue
            for Bm in subsets(v + 1, r):
                for Cm in subsets(v + 1, r):
                    for s in range(0, v + 1):
                        for t in range(0, v + 1):
                            if ordinary:
                                if s not in XW or t not in YW:
                                    continue
                                X = {r + x for x in XW} | Bm | (XW - {s})
                                Y = {r + y for y in YW - {t}} | Cm | YW
                                ret_side_present = X
                            else:
                                if not (t < s) or t not in YW or s in YW:
                                    continue
                                X = set(XW) | Bm | {r + x for x in XW}
                                Y = (YW | {s}) | Cm | {r + y for y in YW - {t}}
                                ret_side_present = Y
                            A = [i for i in range(v + 1, NJ) if i not in X]
                            B = [j for j in range(v + 1, NJ) if j in Y]
                            expA = [(M - a) * r + i for a in range(1, M) for i in A]
                            expB = [(M - a) * r + j for a in range(1, M) for j in B]
                            assert len(set(expA)) == len(expA)
                            assert len(set(expB)) == len(expB)
                            for e in expA + expB:
                                assert NJ < e < S, (r, v, M, e)
                            ret = [s + j * r for j in range(1, M + 1)]
                            side = expA if ordinary else expB
                            assert not set(ret) & set(side), (r, v, M, s, ret, side)
                            for e in ret:
                                if e <= NJ:
                                    lowered += 1
                                    if ordinary:
                                        assert e in ret_side_present, (r, v, s, e)
                                    else:
                                        assert e not in ret_side_present, (r, v, s, e)
                            count += 1
    return count, lowered


def main():
    total = 0
    low = 0
    for r in range(2, 6):
        for v in range(0, r):
            for M in range(3, 5):
                for ordinary in (True, False):
                    c, l = check(r, v, M, ordinary)
                    total += c
                    low += l
    assert total > 0
    assert low > 0, "the case r + s <= N_J must occur"
    print(f"configurations {total}, returned exponents at or below N_J {low}")
    print("ALL PASS")


if __name__ == "__main__":
    main()
