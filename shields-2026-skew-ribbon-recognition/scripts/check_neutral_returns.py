"""The raised fixed rows of the grade-zero ordinary chart (ph:finite-block, neutral cancellation).

Paper section `sec:comparison` (Finite comparisons on actual composition charts), proof of ph:finite-block:
"The neutral primitive numerator contributes to a raised record only at k = M - 1 and 0 < x < w.
Its index is r + delta + x.  The actual mate implication makes this a proper finer row ... its
numerator coefficient is zero."

For every connected J with at most CELLS cells, every legal case (a) mark mu of J (period r, width
v), every connected coarse factor V in a small box, the source E = V o_mu J, and every legal mark
omega of E of width w < r, w != v (the original upper mark), put delta = v - w.  The check asserts

  (raise)  for every row b of J with 0 <= b < r, and every c >= 1, an index
           c r + delta + b in [0, r + v) is a row of J,

which is the hypothesis `hraise` of `neutral_hneutral` in the Lean tree; and it asserts that the
same statement fails for the chart carrying its returns: with tau = [s < delta], the returned
monomial R_{c + tau} z^{(c + tau) r + s} sits at the raised index c r + delta + beta of the row
beta = s - delta + tau r whenever beta is a row of J other than s, so the ungraded numerator does
not vanish there.  Both kinds of landing
occur, so the grade-zero reading is needed.
"""

import os
import sys


from _gluing_common import (  # noqa: E402
    compose, content, empty_mark, from_profile, intersection_mark, is_connected_skew, legal,
    normalize, span)

CELLS = 6
BOX = 3


def compositions(n):
    if n == 0:
        yield ()
        return
    for k in range(1, n + 1):
        for rest in compositions(n - k):
            yield (k,) + rest


def diagrams(min_cells, max_cells):
    seen = set()
    for n in range(min_cells, max_cells + 1):
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


def main():
    inners = [J for J in diagrams(2, CELLS)]
    coarse = [V for V in diagrams(3, 5) if span(V) >= 3]
    landings = raise_ok = returns_hit = 0
    for J in inners:
        XJ, _ = betas(J)
        for mu in marks(J):
            if mu.case != 'a' or not legal(mu):
                continue
            r, v = mu.period, mu.width
            for V in coarse:
                try:
                    E = compose(V, mu)
                except AssertionError:
                    continue
                if not is_connected_skew(E):
                    continue
                ws = set()
                for om in marks(E):
                    if legal(om) and om.width < r and om.width != v:
                        ws.add(om.width)
                for w in ws:
                    landings += 1
                    delta = v - w
                    ok = True
                    for b in XJ:
                        if not 0 <= b < r:
                            continue
                        for c in range(1, 4):
                            idx = c * r + delta + b
                            if 0 <= idx < r + v and idx not in XJ:
                                ok = False
                    assert ok, (sorted(J), sorted(mu.lower), sorted(V), w)
                    raise_ok += 1
                    # the returned monomial at r + s meets the raised row beta = s - delta
                    for s in XJ:
                        tau = 1 if s < delta else 0
                        beta = s - delta + tau * r
                        if 0 <= s <= v and beta != s and beta in XJ and 0 <= beta < r:
                            returns_hit += 1
                            break
    print(f'landings: {landings}; raise holds: {raise_ok}; returns meet a raised row: '
          f'{returns_hit}')
    assert landings > 0 and raise_ok == landings and returns_hit > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
