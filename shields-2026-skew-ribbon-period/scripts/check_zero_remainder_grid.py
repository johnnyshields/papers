r"""Paper section `app:empty` (Empty overlaps and zero span remainder).

The selected-grid ribbons of the zero-remainder geometry.

Paper section: "Empty overlaps and zero span remainder" (app:empty), proof of
prop:zero-remainder, the paragraphs from "At every positive grid position the two full flag
bits are both present or both absent" to "All grid bits are now uniformly absent or uniformly
present".

Under whole P(g, 0) the grid bits of a parent at the multiples of g are equal, so the parent's
selected-grid ribbon is the ribbon whose breaks are the grid positions carrying the bit.  A chart
of period A g read in the frame where its line outer is a row pins the grid bits as follows:

* positive mark of width k g (0 < k < A), phases t = 0, s = w: the grid bits are A-periodic,
  with the pair of bits at residues (0, k) equal to (0, 0) for case (a), (1, 1) for case (b),
  (0, 1) for case (d) and (1, 0) for case (c);
* empty mark over a ribbon outer: the grid bits at the multiples of A are the outer's bits
  (arbitrary), and A-periodic at the other residues.

The script enumerates every such break pattern for a period-A parent and a period-B parent of the
same span L, with gcd(A, B) = 1, A > B >= 2, and asserts that equal ribbon Schur functions force
both ribbons to be the row or both the column: the grid is uniformly absent or uniformly
present, and in particular no mixed pattern occurs.  Ribbon Schur functions are compared
exactly in the complete homogeneous basis, r_alpha = sum over coarsenings beta of alpha of
(-1)^(len alpha - len beta) h_{sort beta}.
"""
from itertools import product
from collections import Counter
from math import gcd


def ribbon_h(comp):
    """The ribbon Schur function of a composition, as a Counter over sorted partitions."""
    n = len(comp)
    out = Counter()
    for mask in range(1 << max(n - 1, 0)):
        parts, cur = [], comp[0]
        for i in range(1, n):
            if mask >> (i - 1) & 1:
                cur += comp[i]
            else:
                parts.append(cur)
                cur = comp[i]
        parts.append(cur)
        sign = (-1) ** (n - len(parts))
        out[tuple(sorted(parts, reverse=True))] += sign
    return frozenset((k, v) for k, v in out.items() if v)


def comp_of_breaks(L, breaks):
    cuts = [0] + sorted(breaks) + [L]
    return tuple(cuts[i + 1] - cuts[i] for i in range(len(cuts) - 1))


def patterns(L, A, kind, k):
    """Break sets for a period-A parent of span L; kind 'P' (positive, width k) or 'E'."""
    generic = [r for r in range(1, A) if not (kind == 'P' and r == k)]
    zero_res = [j for j in range(1, L) if j % A == 0]
    for xs in product((0, 1), repeat=len(generic)):
        x = dict(zip(generic, xs))
        base = {j for j in range(1, L) if j % A in x and x[j % A]}
        if kind == 'P':
            for b0, bk in ((0, 0), (1, 1), (0, 1), (1, 0)):
                extra = {j for j in range(1, L) if (j % A == 0 and b0) or (j % A == k and bk)}
                yield frozenset(base | extra)
        else:
            for ds in product((0, 1), repeat=len(zero_res)):
                yield frozenset(base | {j for j, d in zip(zero_res, ds) if d})


def spans(A, kind, Lmax):
    for M in range(2, Lmax // A + 1):
        if kind == 'P':
            for k in range(1, A):
                if M * A + k <= Lmax:
                    yield M * A + k, k
        else:
            yield M * A, 0


def main(Lmax=16):
    checked = 0
    for A in range(3, Lmax):
        for B in range(2, A):
            if gcd(A, B) != 1:
                continue
            for kF in ('P', 'E'):
                for kH in ('P', 'E'):
                    if kF == 'E' and kH == 'E':
                        continue
                    for L, k in spans(A, kF, Lmax):
                        for L2, k2 in spans(B, kH, Lmax):
                            if L2 != L:
                                continue
                            fH = {}
                            for bH in patterns(L, B, kH, k2):
                                fH.setdefault(ribbon_h(comp_of_breaks(L, bH)), []).append(bH)
                            for bF in patterns(L, A, kF, k):
                                for bH in fH.get(ribbon_h(comp_of_breaks(L, bF)), []):
                                    checked += 1
                                    ok = (not bF and not bH) or (len(bF) == len(bH) == L - 1)
                                    assert ok, (A, B, kF, kH, L, sorted(bF), sorted(bH))
    assert checked > 0
    print(f"zero-remainder grid: {checked} Schur-equal pairs, all uniform")


if __name__ == "__main__":
    main()
