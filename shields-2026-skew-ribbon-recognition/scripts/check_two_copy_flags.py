"""Flag lists of the actual two-copy diagram of a horizontal row mark (ph:rectangular-splice).

Paper section `app:physical` (Whole currents and the first complete grade), ph:rectangular-splice.

For every connected skew diagram E with at most CELLS cells and every legal case (a) mark of E
(the empty horizontal mark included), build F = Row_2 o_omega E by the gluing composition and
compare its beta lists with

    X_F = (Q + X) u (X \\ {S}),    Y_F = (Q + (Y \\ {0})) u Y,    Q = S - w,

and the rectangular shape condition xi_{k+1} - zeta_j < Q (k >= 0, j below the last column).
The lemma is stated for a horizontal row mark.  The check asserts that the flag formula holds
exactly when the lower copy W is a single row (or empty), that this is the same as no row or
column flag of E in the end windows 0 < k < w and Q < k < S (the hypothesis of
`twoCopyFlags_of_endRows` in the Lean tree, which `endRows_of_rowMark` derives from the
row-mark hypothesis), and that it then forces the shape condition and the
middle phases (w, 0).  Both kinds of mark occur, so the hypothesis is neither vacuous nor
automatic.
"""

import os
import sys


from _gluing_common import (  # noqa: E402
    compose, content, empty_mark, from_profile, intersection_mark, legal, normalize, shift)

CELLS = 9


def compositions(n):
    if n == 0:
        yield ()
        return
    for k in range(1, n + 1):
        for rest in compositions(n - k):
            yield (k,) + rest


def diagrams(max_cells):
    seen = set()
    for n in range(2, max_cells + 1):
        for lengths in compositions(n):
            def gaps_for(i):
                if i == len(lengths) - 1:
                    yield ()
                    return
                for g in range(min(lengths[i], lengths[i + 1])):
                    for rest in gaps_for(i + 1):
                        yield (g,) + rest
            for gaps in gaps_for(0):
                D = from_profile(list(lengths), list(gaps))
                if D not in seen:
                    seen.add(D)
                    yield D


def betas(D):
    rows = {}
    for i, j in D:
        rows.setdefault(i, []).append(j - i)
    m = min(content(c) for c in D)
    X = sorted((max(v) + 1 - m for v in rows.values()), reverse=True)
    Y = sorted((min(v) - m for v in rows.values()), reverse=True)
    return X, Y


def marks(E):
    yield empty_mark(E)
    for cell in E:
        try:
            mk = intersection_mark(E, cell)
        except AssertionError:
            continue
        yield mk


def phases(mk):
    """The middle phases (s, t) of SkewGluing.MarkedInner.IsPhases, (0, 0) for the empty mark."""
    if not mk.lower:
        return 0, 0
    E, q, w = mk.inner, mk.period, mk.width
    p = mk.displacement[0]
    m = min(content(c) for c in E)

    def lo(a):
        return min(i for i, j in E if j - i == m + a)

    def hi(a):
        return max(i for i, j in E if j - i == m + a)

    dlo = [lo(a + q) - p - lo(a) for a in range(w)]
    dhi = [hi(a + q) - p - hi(a) for a in range(w)]
    lower = [dlo[a] > 0 or dhi[a] < 0 for a in range(w)]
    upper = [dlo[a] < 0 or dhi[a] > 0 for a in range(w)]
    s = next((a for a in range(w) if lower[a]), w)
    t = next((a for a in range(w) if not upper[a]), w)
    assert all(lower[a] == (a >= s) for a in range(w))
    assert all(upper[a] == (a < t) for a in range(w))
    return s, t


def main():
    row2 = frozenset({(0, 0), (0, 1)})
    total = held = 0
    for E in diagrams(CELLS):
        for mk in marks(E):
            if mk.case != 'a' or not legal(mk):
                continue
            total += 1
            S = mk.period + mk.width
            Q = mk.period
            w = mk.width
            X, Y = betas(E)
            assert X[0] == S and Y[-1] == 0
            F = compose(row2, mk)
            XF, YF = betas(F)
            # block order: top block Q + X, then X without S; left block Q + (Y without 0), then Y
            flag_ok = (XF == [Q + x for x in X] + X[1:] and YF == [Q + y for y in Y[:-1]] + Y)
            shape = all(xk - yj < Q for xk in X[1:] for yj in Y[:-1])
            window = all(k not in X and k not in Y
                         for k in list(range(1, w)) + list(range(Q + 1, S)))
            one_row = len({i for i, _ in mk.lower}) <= 1
            assert flag_ok == window == one_row, (sorted(E), sorted(mk.lower))
            if window:
                held += 1
                assert shape and phases(mk) == (w, 0), (sorted(E), sorted(mk.lower))
    print(f'case (a) legal marks: {total}; end windows single rows: {held}')
    assert 0 < held < total
    print('ALL PASS')


if __name__ == '__main__':
    main()
