r"""Paper section `sec:weighted-action` (Weighted composition covariance).

Checks `lem:covariance`, `rt:mixed-covariance`, `eq:weighted-beta-moves`,
`eq:mixed-strip-remainder`, and `eq:full-normalization` by exact SymPy
arithmetic on actual I--IV cell charts.  The finite family contains empty
and positive marks, both ordinary gauges, both mixed orientations, a
phase difference two, and a nonempty hatted mark.  This is bounded
mechanism evidence, not a proof for arbitrary legal charts.
"""

import sympy as sp

from schur_tools import (antitranspose, compose, delta, dimensions, from_profile,
                         h, hats, legal_marks, rotate, schur, translate)
from _weighted_readout import (beta_weighted, coarse, composition_map, full_betas,
                               involution, mixed_sign, row_image, weighted)


def inner_family():
    seeds = [from_profile(rows, gaps) for rows, gaps in [
        ((3,), ()), ((2, 2), (1,)), ((2, 1), (0,)),
        ((3, 2), (0,)), ((4, 2), (1,)), ((3, 3), (1,)),
    ]]
    return sorted({T for E in seeds for T in
                   (E, rotate(E), antitranspose(E), rotate(antitranspose(E)))},
                  key=lambda E: (len(E), sorted(E)))


def check_strip(E, W, v, case, copies, removed):
    """Compare the literal northwest-cell deletion with all separated pieces."""
    assert case == 'd' and 1 <= removed <= copies
    period = v[1] - v[0]
    O, What, Ohat = hats(E, W, v)
    s = min(j - i for i, j in O)
    row = frozenset((0, j) for j in range(copies))
    parent = compose(row, E, W, v, case)
    deleted = set()
    for content in range((copies - removed) * period + s, copies * period + s):
        diagonal = [x for x in parent if x[1] - x[0] == content]
        deleted.add(min(diagonal))
    assert len(deleted) == removed * period
    rest = copies - removed
    first = (compose(frozenset((0, j) for j in range(rest)), E, W, v, case)
             if rest else W)
    pieces = [first]
    pieces += [translate(Ohat, (j * v[0] + 1, j * v[1] + 1))
               for j in range(rest, copies)]
    pieces += [translate(What, (j * v[0] + 1, j * v[1] + 1))
               for j in range(rest + 1, copies + 1)]
    remainder = set()
    for piece in pieces:
        assert remainder.isdisjoint(piece)
        assert all((i + di, j + dj) not in remainder for i, j in piece
                   for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)))
        remainder.update(piece)
    assert parent - deleted == remainder
    assert schur(frozenset(remainder)) == sp.expand(sp.prod(schur(X) for X in pieces))


def main():
    cases = set()
    offsets = set()
    seen_hat = False
    checks = 0
    outers = [from_profile(rows, gaps) for rows, gaps in [
        ((2,), ()), ((1, 1), (0,)), ((2, 1), (0,)), ((2, 2), (1,)),
    ]]
    for E in inner_family():
        for W, v, case in legal_marks(E):
            cases.add(case)
            period = v[1] - v[0]
            O, What, Ohat = hats(E, W, v)
            A, B, C = (schur(X) for X in (W, What, Ohat))
            seen_hat |= bool(What)
            if W:
                s = min(j - i for i, j in O)
                t = max(j - i for i, j in O) + 1 - period
            else:
                s = t = 0
            inner = schur(E)
            if case in ('a', 'b'):
                local = delta(inner, period)
                offset = sp.cancel(weighted(inner, period) / local)
                assert offset.is_Integer and abs(offset) < period
                assert offset == (s - t if case == 'a' else t - s)
                assert sp.cancel(local / (A * B * C)) in (-1, 1)
                if not W:
                    assert offset == 0 and A == 1
            else:
                offset = s - t
                assert 0 < offset <= dimensions(W)[2] < period
                local = (-1) ** (-v[0]) * A * B * C
                assert delta(inner, period) == 0
                assert weighted(inner, period) == sp.expand(offset * local)
            offsets.add(int(offset))
            assert all(delta(f, period) == weighted(f, period) == 0 for f in (A, B, C))
            assert composition_map(sp.Integer(1), E, W, v, case) == 1

            for copies in range(1, 4):
                raw = schur(compose(frozenset((0, j) for j in range(copies)), E, W, v, case))
                X, Y = full_betas(compose(frozenset((0, j) for j in range(copies)), E, W, v, case))
                image = composition_map(h(copies), E, W, v, case)
                for k in range(1, copies + 2):
                    moves, rows, cols = beta_weighted(X, Y, k * period)
                    assert moves == weighted(raw, k * period)
                    assert sp.expand(sum(rows)) == delta(raw, k * period)
                    assert sp.expand(sum(cols)) == delta(raw, k * period)
                    expected = local ** k * composition_map(
                        coarse(h(copies), k, period, offset), E, W, v, case)
                    assert weighted(image, k * period) == sp.expand(expected)
                    hall_expected = (local ** k * composition_map(delta(h(copies), k), E, W, v, case)
                                     if case in ('a', 'b') else 0)
                    assert delta(image, k * period) == sp.expand(hall_expected)
                    if case in ('a', 'd') and k <= copies:
                        remainder = (schur(compose(frozenset((0, j) for j in range(copies - k)),
                                                   E, W, v, case)) if k < copies else A)
                        sign = sp.cancel(local / (A * B * C))
                        common = sp.expand(sign ** k * (B * C) ** k * remainder)
                        if case == 'a':
                            assert [(x, f) for x, f in zip(X, rows) if f != 0] == [
                                (copies * period + s, common)]
                            assert [(y, f) for y, f in zip(Y, cols) if f != 0] == [(t, common)]
                        else:
                            assert all(f == 0 for f in rows)
                            assert {y: f for y, f in zip(Y, cols) if f != 0} == {
                                t: common, (copies - k) * period + s: -common}
                            check_strip(E, W, v, case, copies, k)
                    checks += 1
            polynomial = h(1) * h(2) + h(3)
            image = composition_map(polynomial, E, W, v, case)
            assert weighted(image, period) == sp.expand(local * composition_map(
                coarse(polynomial, 1, period, offset), E, W, v, case))
            for D in outers:
                rows, columns, diagonals = dimensions(D)
                sign = mixed_sign(D) if case in ('c', 'd') else 1
                normalizer = sign * A ** (len(D) - rows) * B ** (len(D) - columns) * C ** (len(D) - diagonals)
                parent = schur(compose(D, E, W, v, case))
                assert composition_map(schur(D), E, W, v, case, read_outer=False) == sp.expand(normalizer * parent)
                read_outer = involution(schur(D)) if case == 'b' else schur(D)
                assert composition_map(read_outer, E, W, v, case) == sp.expand(normalizer * parent)

    assert cases == {'a', 'b', 'c', 'd'}
    assert 0 in offsets and 2 in offsets and seen_hat
    for polynomial in (h(4), h(1) * h(3), h(2) ** 2 - h(4)):
        for k in range(1, 5):
            assert delta(involution(polynomial), k) == sp.expand((-1) ** (k - 1) * involution(delta(polynomial, k)))
            assert weighted(involution(polynomial), k) == sp.expand((-1) ** k * involution(weighted(polynomial, k)))
    # A real mixed mark detects both a dropped sign and the wrong empty value.
    E = from_profile((2, 1), (0,))
    W, v, case = next(mark for mark in legal_marks(E) if mark[2] == 'd')
    A = schur(W)
    assert A == h(1) and A != 1
    assert composition_map(sp.Integer(1), E, W, v, case) == 1
    assert weighted(schur(E), 2) == -A and weighted(schur(E), 2) != A
    assert row_image(E, W, v, case, 0) != A
    # The terminal corollary also permits the ordinary one-cell inner.
    cell = from_profile((1,), ())
    for D in (from_profile((2,), ()), from_profile((1, 1), (0,))):
        P = schur(compose(D, cell, frozenset(), (0, 1), 'a'))
        T = delta(delta(P, 1), 1)
        assert T != 0 and sp.expand(delta(P, 1) - T * h(1)) == 0
    print('PASS: actual weighted generator and beta-move comparisons:', checks)
    print('PASS: literal mixed strips, full signed modifiers, all physical readings, and unit/sign controls')
    print('ALL PASS')


if __name__ == '__main__':
    main()
