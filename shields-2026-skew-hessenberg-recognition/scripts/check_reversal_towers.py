#!/usr/bin/env python3
"""Exact ribbon-factor towers and free-h determinant controls.

Positive equalities use complete integer polynomials, never evaluation-only
fingerprints.  Geometry uses the separate literal source-rule constructor.
Controls distinguish a non-equivalent rearrangement, the inflation threshold,
and the false class formula obtained by dropping all-power rigidity.
"""
from bisect import insort
from collections import Counter
from itertools import product
import sys

sys.dont_write_bytecode = True

from check_literal_charts import (
    cells_of_profile, composite_profile, compositions, connected_skew,
    literal_hypotheses, norm, profile_of_cells, row_intervals,
    source_ribbon_chart,
)


def clean(poly):
    return {mon: coeff for mon, coeff in poly.items() if coeff}


def jt_poly(rows, gaps):
    """Full Leibniz determinant, bottom row first, pruning negative entries."""
    cells = cells_of_profile(rows, gaps)
    intervals = row_intervals(cells)
    n = len(rows)
    indices = [[intervals[i][1] - intervals[j][0] + 1 - i + j
                for j in range(n)] for i in range(n)]
    states = {0: {(): 1}}
    for i in reversed(range(n)):
        nxt = {}
        for mask, poly in states.items():
            for j, label in enumerate(indices[i]):
                if label < 0 or mask & (1 << j):
                    continue
                sign = -1 if (mask & ((1 << j) - 1)).bit_count() % 2 else 1
                target = nxt.setdefault(mask | (1 << j), Counter())
                for mon, coeff in poly.items():
                    newmon = list(mon)
                    if label:
                        insort(newmon, label)
                    target[tuple(newmon)] += sign * coeff
        states = {mask: clean(poly) for mask, poly in nxt.items() if clean(poly)}
    return states[(1 << n) - 1]


def ribbon_poly(alpha):
    answer = Counter()
    for mask in range(1 << (len(alpha) - 1)):
        blocks = []
        running = alpha[0]
        for i, part in enumerate(alpha[1:]):
            if mask & (1 << i):
                blocks.append(running)
                running = part
            else:
                running += part
        blocks.append(running)
        answer[tuple(sorted(blocks))] += (-1) ** (len(alpha) - len(blocks))
    return clean(answer)


def composition(left, right):
    result = ()
    for part in left:
        power = right
        for _ in range(part - 1):
            power = power[:-1] + (power[-1] + right[0],) + right[1:]
        result += power
    return result


def composition_list(factors):
    answer = factors[0]
    for factor in factors[1:]:
        answer = composition(answer, factor)
    return answer


def rotate(cells):
    return norm(frozenset((-i, -j) for i, j in cells))


def actual_tower(factors, inner, t):
    prefix = cells_of_profile(factors[0], (0,) * (len(factors[0]) - 1))
    for factor in factors[1:]:
        ribbon = cells_of_profile(factor, (0,) * (len(factor) - 1))
        hyps, _ = literal_hypotheses(ribbon, 0)
        assert all(value for name, value in hyps.items() if name != 'V')
        prefix = source_ribbon_chart(profile_of_cells(prefix)[0], ribbon, 0)
        assert all(g == 0 for g in profile_of_cells(prefix)[1])
    return source_ribbon_chart(profile_of_cells(prefix)[0], inner, t)


def multiply(p, q):
    result = Counter()
    for a, ca in p.items():
        for b, cb in q.items():
            result[tuple(sorted(a + b))] += ca * cb
    return clean(result)


def homogenized_transport(alpha, inner_profile, t):
    """Coarsening formula, separately from the full determinant algorithm."""
    result = Counter()
    blocks_cache = {}
    for mask in range(1 << (len(alpha) - 1)):
        blocks = []
        running = alpha[0]
        for i, part in enumerate(alpha[1:]):
            if mask & (1 << i):
                blocks.append(running)
                running = part
            else:
                running += part
        blocks.append(running)
        poly = {(): 1}
        for size in blocks:
            if size not in blocks_cache:
                blocks_cache[size] = jt_poly(*composite_profile((size,), inner_profile, t))
            poly = multiply(poly, blocks_cache[size])
        contracted = len(alpha) - len(blocks)
        mark = (t,) * contracted if t else ()
        for mon, coeff in poly.items():
            result[tuple(sorted(mon + mark))] += (-1) ** contracted * coeff
    return clean(result)


def first_difference(p, q):
    for mon in sorted(set(p) | set(q), key=lambda a: (len(a), a)):
        if p.get(mon, 0) != q.get(mon, 0):
            return mon, p.get(mon, 0), q.get(mon, 0)
    raise AssertionError('expected different polynomials')


def main():
    # The minimum two-nonsymmetric-factor example, with the entire ribbon
    # class recovered independently by coarsening every composition of nine.
    factors = ((1, 2), (1, 2))
    alpha = composition_list(factors)
    assert alpha == (1, 2, 1, 3, 2)
    expected_class = {composition_list(tuple(f[::-1] if flip else f for f, flip in zip(factors, signs)))
                      for signs in product((False, True), repeat=2)}
    exhaustive_class = {beta for beta in compositions(9) if ribbon_poly(beta) == ribbon_poly(alpha)}
    assert exhaustive_class == expected_class and len(exhaustive_class) == 4
    for beta in compositions(9):
        assert jt_poly(beta, (0,) * (len(beta) - 1)) == ribbon_poly(beta)
    print('full nine-cell ribbon class:', sorted(exhaustive_class))
    print('independent ribbon determinant/coarsening comparisons: 256')

    full_checks = 0
    transport_checks = 0
    for profile in (((3, 4), (1,)), ((4, 5), (1,))):
        rows, gaps = profile
        p = min(rows[0] - gaps[0], rows[-1] - gaps[-1])
        for t in range(p):
            inner = cells_of_profile(tuple(r + t for r in rows), tuple(g + t for g in gaps))
            reference = jt_poly(*composite_profile(alpha, profile, t))
            for signs in product((False, True), repeat=2):
                changed = tuple(f[::-1] if flip else f for f, flip in zip(factors, signs))
                beta = composition_list(changed)
                parent = actual_tower(changed, inner, t)
                expected = cells_of_profile(*composite_profile(beta, profile, t))
                assert parent == expected
                rotated_factors = tuple(f[::-1] for f in changed)
                rotated_inner = rotate(inner)
                assert actual_tower(rotated_factors, rotated_inner, t) == rotate(parent)
                actual_poly = jt_poly(*profile_of_cells(parent))
                assert actual_poly == reference
                assert jt_poly(*profile_of_cells(rotate(parent))) == reference
                full_checks += 1
            # An independently assembled homogeneous coarsening expression
            # verifies the polynomial map, including h_0=1 at t=0.
            assert homogenized_transport(alpha, profile, t) == reference
            transport_checks += 1
            fake = (1, 1, 2, 2, 3)
            assert sorted(fake) == sorted(alpha)
            assert ribbon_poly(fake) != ribbon_poly(alpha)
            assert jt_poly(*composite_profile(fake, profile, t)) != reference
        # Keep exactly the same source and the same factor flip at the wall.
        beta = composition(factors[0][::-1], factors[1])
        a_wall = jt_poly(*composite_profile(alpha, profile, p))
        b_wall = jt_poly(*composite_profile(beta, profile, p))
        assert a_wall != b_wall
        print('wall control:', profile, 't=', p, 'coefficient witness=', first_difference(a_wall, b_wall))

    # A taller inner with internal support activation before the terminal
    # threshold.  Here full polynomials check the nontrivial outer reversal.
    profile = ((6, 3, 6), (1, 1))
    for t in (0, 1, 2, 3, 4):
        left = jt_poly(*composite_profile((1, 2), profile, t))
        right = jt_poly(*composite_profile((2, 1), profile, t))
        assert left == right
        assert homogenized_transport((1, 2), profile, t) == left
        transport_checks += 1
    # A nonsymmetric version avoids interpreting every outer reversal as
    # a global rotation of a symmetric inner.
    profile = ((6, 3, 7), (1, 1))
    for t in (0, 1, 2, 3, 4):
        a_cells = cells_of_profile(*composite_profile((1, 2), profile, t))
        b_cells = cells_of_profile(*composite_profile((2, 1), profile, t))
        assert a_cells != b_cells and rotate(a_cells) != b_cells
        left, right = jt_poly(*profile_of_cells(a_cells)), jt_poly(*profile_of_cells(b_cells))
        assert left == right
        assert homogenized_transport((1, 2), profile, t) == left
        transport_checks += 1

    # Three factors: every flip is performed in one fixed left-associated
    # tower, with the final marks never reassociated through the prefix.
    factors3 = ((1, 2), (1, 2), (1, 2))
    baseline_ribbon = ribbon_poly(composition_list(factors3))
    taller_profile = ((4, 3, 5), (1, 1))
    tower_checks = 0
    for signs in product((False, True), repeat=3):
        changed = tuple(f[::-1] if flip else f for f, flip in zip(factors3, signs))
        beta = composition_list(changed)
        assert ribbon_poly(beta) == baseline_ribbon
        for t in (0, 1, 2):
            inner = cells_of_profile(tuple(r + t for r in taller_profile[0]),
                                     tuple(g + t for g in taller_profile[1]))
            hyps, _ = literal_hypotheses(inner, t)
            assert all(value for name, value in hyps.items() if name != 'V' or t > 0)
            assert actual_tower(changed, inner, t) == cells_of_profile(*composite_profile(beta, taller_profile, t))
            tower_checks += 1

    # The same marks work for the exact mixed-zero recoding domain; no
    # claim is made here for arbitrary mixed-zero inner class recovery.
    recoded = composite_profile((1, 1), ((3, 4), (1,)))
    assert recoded == ((3, 4, 3, 4), (1, 0, 1))
    mixed_checks = 0
    for t in (0, 1):
        inner = cells_of_profile(tuple(r + t for r in recoded[0]),
                                 tuple(g + t for g in recoded[1]))
        hyps, _ = literal_hypotheses(inner, t)
        assert all(value for name, value in hyps.items() if name != 'V' or t > 0)
        for signs in product((False, True), repeat=2):
            changed = tuple(f[::-1] if flip else f for f, flip in zip(factors, signs))
            beta = composition_list(changed)
            assert actual_tower(changed, inner, t) == cells_of_profile(*composite_profile(beta, recoded, t))
            mixed_checks += 1

    # Dropping all-power rigidity invalidates the displayed upper class
    # formula already for alpha=(1).  It does NOT refute necessity itself.
    bad_inner = ((3, 4, 3, 6, 4), (1, 1, 1, 1))
    mate = ((3, 6, 4, 3, 4), (1, 1, 1, 1))
    bad_cells, mate_cells = cells_of_profile(*bad_inner), cells_of_profile(*mate)
    assert connected_skew(bad_cells) and connected_skew(mate_cells)
    assert jt_poly(*bad_inner) == jt_poly(*mate)
    assert mate_cells not in (bad_cells, rotate(bad_cells))
    assert list(compositions(1)) == [(1,)]
    print('all-power omission control: equal nonrotation mate at alpha=(1), so the claimed upper class would fail')
    print('complete free-h parent equalities with two-factor towers:', full_checks, '(plus each rotation)')
    print('full determinant versus homogeneous transport:', transport_checks)
    print('three-factor retained-context cell checks:', tower_checks)
    print('mixed-zero recoded-inner cell checks:', mixed_checks)
    print('controls: non-equivalent rearrangement rejected at every tested pre-wall time; wall and all-power controls fired')
    print('ALL PASS')


if __name__ == '__main__':
    main()
