#!/usr/bin/env python3
"""Check area-cut recovery and retained-end rigidity for zero-free blocks.

The main route cuts one literal total-merger word at prescribed cell counts.
Independent checks enumerate parent row/gap arrangements, and determinant
polynomials are calibrated against SymPy Jacobi--Trudi matrices.  Finite
checks do not replace the proofs of the arbitrary-height statements.
"""
from collections import Counter, defaultdict
from functools import lru_cache, reduce
from itertools import permutations, product, combinations
import argparse
import sympy as sp


def valid(p):
    r, g = p
    return bool(r) and len(g) == len(r) - 1 and all(a > 0 for a in r) and all(
        0 <= x < min(r[i], r[i + 1]) for i, x in enumerate(g))


def rotate(p):
    return p[0][::-1], p[1][::-1]


def near(a, b):
    return a[0][:-1] + (a[0][-1] + b[0][0],) + b[0][1:], a[1] + b[1]


def join(a, b):
    return a[0] + b[0], a[1] + (0,) + b[1]


def merger(bs):
    return reduce(near, bs)


def parent(bs):
    return reduce(join, bs)


def blocks(p):
    r, g = p
    cuts = [-1] + [i for i, a in enumerate(g) if a == 0] + [len(r) - 1]
    return tuple((r[a + 1:b + 1], g[a + 1:b]) for a, b in zip(cuts, cuts[1:]))


def betas(p):
    assert valid(p), p
    r, g = p
    x, y = [r[-1]], [0]
    for row, gap in zip(reversed(r[:-1]), reversed(g)):
        y.append(x[-1] - gap)
        x.append(y[-1] + row)
    return tuple(reversed(x)), tuple(reversed(y))


def zero_free(p):
    x, y = betas(p)
    return not set(x) & set(y)


def hessenberg(p):
    return all(p[0][i] > p[1][i - 1] + p[1][i] for i in range(1, len(p[0]) - 1))


@lru_cache(maxsize=50000)
def schur(p):
    x, y = betas(p)
    n = len(x)
    state = {0: {(): 1}}
    for i, row in enumerate(x):
        nxt = {}
        for mask, poly in state.items():
            for j, col in enumerate(y):
                label = row - col
                if label < 0 or mask >> j & 1:
                    continue
                sign = (-1) ** (mask >> (j + 1)).bit_count()
                target = nxt.setdefault(mask | (1 << j), Counter())
                for mon, coeff in poly.items():
                    out = tuple(sorted(mon + (label,))) if label else mon
                    target[out] += sign * coeff
        state = {m: {mon: c for mon, c in pol.items() if c} for m, pol in nxt.items()}
    return tuple(sorted(state[(1 << n) - 1].items()))


def add(*polys):
    out = Counter()
    for p in polys:
        out.update(dict(p))
    return tuple(sorted((m, c) for m, c in out.items() if c))


def scale(p, k):
    return tuple((m, k * c) for m, c in p if k * c)


def multiply(a, b):
    out = Counter()
    for m, c in a:
        for n, d in b:
            out[tuple(sorted(m + n))] += c * d
    return tuple(sorted((m, c) for m, c in out.items() if c))


def middle(bs):
    a, b, c = bs
    return add(multiply(schur(near(a, b)), schur(c)), multiply(schur(a), schur(near(b, c))))


def coefficient(poly, label):
    result = []
    for mon, c in poly:
        if label in mon:
            assert mon.count(label) == 1
            remainder = list(mon)
            remainder.remove(label)
            result.append((tuple(remainder), c))
    return tuple(sorted(result))


def leading(p):
    result = coefficient(schur(p), betas(p)[0][0])
    assert result
    return result


def inventory(bs):
    return tuple(sorted(schur(b) for b in bs))


def sympy_schur(p):
    # Rebuild partitions geometrically rather than use the beta constructor.
    r, g = p
    starts = [0]
    for i, gap in enumerate(g):
        starts.append(starts[-1] + gap + 1 - r[i + 1])
    shift = min(starts)
    mu = [a - shift for a in starts]
    lam = [a + b for a, b in zip(mu, r)]
    labels = [[lam[i] - mu[j] - i + j for j in range(len(r))] for i in range(len(r))]
    h = sp.symbols('h1:' + str(max(map(max, labels)) + 1))
    matrix = sp.Matrix([[0 if q < 0 else (1 if q == 0 else h[q - 1]) for q in row] for row in labels])
    expression = matrix.det(method='domain-ge')
    output = []
    for exponents, coefficient in sp.Poly(expression, *h).terms():
        mon = tuple(i + 1 for i, e in enumerate(exponents) for _ in range(e))
        output.append((mon, int(coefficient)))
    return tuple(sorted(output))


def split_by_areas(m, areas, multirow=True):
    """Return the unique split, or None if a proposed word cut is illegal."""
    if sum(areas) != sum(m[0]) or min(areas) <= 0:
        return None
    marks, pos = {}, 0
    for row, gap in zip(m[0][:-1], m[1]):
        pos += row
        marks[pos] = gap
    result, start = [], 0
    for area in areas:
        end = start + area
        if end in marks:
            return None
        interior = sorted(p for p in marks if start < p < end)
        points = [start] + interior + [end]
        b = tuple(v - u for u, v in zip(points, points[1:])), tuple(marks[p] for p in interior)
        if not valid(b) or not zero_free(b) or (multirow and len(b[0]) < 2):
            return None
        result.append(b)
        start = end
    assert merger(result) == m
    return tuple(result)


def candidates(bs, multirow=True, test_middle=True):
    m = merger(bs)
    inv = inventory(bs)
    target = middle(bs) if test_middle else None
    out = set()
    raw = set()
    for oriented in {m, rotate(m)}:
        for areas in set(permutations(sum(b[0]) for b in bs)):
            cut = split_by_areas(oriented, areas, multirow)
            if cut is None:
                continue
            raw.add(parent(cut))
            if inventory(cut) != inv:
                continue
            if test_middle and middle(cut) != target:
                continue
            out.add(parent(cut))
    return out, raw


def endpoint_area_test(bs):
    first, last = bs[0][1][0], bs[-1][1][-1]
    left = {sum(b[0]) for b in bs if first in b[1]}
    right = {sum(b[0]) for b in bs if last in b[1]}
    return left == {sum(bs[0][0])} or right == {sum(bs[-1][0])}


def profiles(max_rows=4, max_row=4):
    for n in range(1, max_rows + 1):
        for r in product(range(1, max_row + 1), repeat=n):
            for g in product(*(range(1, min(r[i], r[i + 1])) for i in range(n - 1))):
                p = r, g
                if zero_free(p):
                    yield p


def fixed_merger_sweep():
    count = fibers = relations = symmetric = equal_ends = endpoints = rejected = 0
    # These are all positive-gap zero-free mergers in the explicit box.
    for m in profiles(4, 4):
        area = sum(m[0])
        groups = defaultdict(list)
        for a, end in combinations(range(1, area), 2):
            bs = split_by_areas(m, (a, end - a, area - end), multirow=False)
            if bs is None:
                continue
            groups[(inventory(bs), middle(bs))].append(bs)
            count += 1
        for members in groups.values():
            fibers += 1
            assert len(members) <= 2
            for bs in members:
                spans = [betas(b)[0][0] for b in bs]
                if spans.count(min(spans)) == 1:
                    assert len(members) <= 2
                reconstructed, _ = candidates(bs, multirow=False)
                assert all(schur(h) == schur(parent(bs)) for h in reconstructed)
                assert len(reconstructed) <= 4
                if m == rotate(m):
                    assert reconstructed <= {parent(bs), rotate(parent(bs))}
                    symmetric += 1
                if sum(bs[0][0]) == sum(bs[2][0]):
                    assert reconstructed <= {parent(bs), rotate(parent(bs))}
                    equal_ends += 1
                if all(len(b[0]) >= 2 for b in bs) and endpoint_area_test(bs):
                    assert reconstructed <= {parent(bs), rotate(parent(bs))}
                    endpoints += 1
                for cs in members:
                    relations += 1
                    if sum(bs[0][0]) == sum(cs[0][0]) or sum(bs[2][0]) == sum(cs[2][0]):
                        assert bs == cs
            # First/last areas label distinct members injectively.
            assert len({sum(bs[0][0]) for bs in members}) == len(members)
            assert len({sum(bs[-1][0]) for bs in members}) == len(members)
        # Compare words with matching inventory but different sums: a firing control.
        by_inv = defaultdict(set)
        for inv, mid in groups:
            by_inv[inv].add(mid)
        rejected += sum(len(values) > 1 for values in by_inv.values())
    assert count and symmetric and equal_ends and rejected
    print(f'PASS: {count} literal cuts in {fibers} inventory/sum fibers; {relations} retained-end comparisons.')
    print(f'PASS: {symmetric} symmetric-merger and {equal_ends} equal-exterior-area instances; {endpoints} endpoint-support instances.')
    print(f'CONTROL: {rejected} inventory fibers have different middle sums; the two extreme readings alone do not classify them.')


def arrangement_check(p):
    """Exact independent mate check over all invariant row/gap arrangements."""
    target, matches, count = schur(p), set(), 0
    for r in set(permutations(p[0])):
        for g in set(permutations(p[1])):
            q = r, g
            if not valid(q):
                continue
            count += 1
            if schur(q) == target:
                matches.add(q)
    return count, matches


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--skip-sweep', action='store_true')
    args = parser.parse_args()
    calibrations = [((2, 3), (1,)), ((9, 6, 6), (4, 4)),
                    ((1, 2, 2, 3), (0, 0, 1)), ((1, 2, 3, 2), (0, 1, 0))]
    for p in calibrations:
        assert schur(p) == sympy_schur(p)
    print('PASS: four independent SymPy polynomial calibrations.')
    # The non-Hessenberg seven-row source, including its precise domain tests.
    bs = (((11, 4), (2,)), ((4, 5), (2,)), ((9, 6, 6), (4, 4)))
    m = merger(bs)
    assert m == ((11, 8, 14, 6, 6), (2, 2, 4, 4))
    assert all(zero_free(b) and len(b[0]) >= 2 for b in bs)
    assert not hessenberg(bs[2]) and not hessenberg(parent(bs))
    assert set(bs[0][1]) & set(bs[1][1]) and endpoint_area_test(bs)
    assert m[0].count(11) == 1 and 11 > 2 * max(m[1])
    assert all(a % 2 == 0 for a in m[0][1:] + m[1])
    answer, raw = candidates(bs)
    assert answer == {parent(bs), rotate(parent(bs))}
    print('PASS: seven-row zero-free non-Hessenberg overlapping-support source; area-cut candidates:', len(raw), 'survivors:', len(answer))
    # Merger-fixed class recovery without assuming individual block rigidity.
    e = ((2, 3), (1,))
    power2 = near(e, e)
    repeated = e, e, power2
    answer, raw = candidates(repeated)
    assert len(answer) == 4 and len(raw) == 6
    assert parent((e, power2, e)) not in answer
    assert parent((power2, e, e)) in answer
    assert middle(repeated) != middle((e, power2, e))
    print('CONTROL: repeated-inner cuts give six oriented candidates, four equal; the middle placement is rejected.')
    for p in (parent(repeated), parent((e, power2, e))):
        count, direct = arrangement_check(p)
        recovered, _ = candidates(blocks(p))
        assert direct == recovered
        print('PASS: complete row/gap arrangements:', count, 'exact mates:', len(direct))
    # Pairwise disjoint supports and an overlapping private-end support.
    disjoint = (((13, 10, 5), (4, 4)), ((5, 7), (2,)), ((13, 14, 14), (6, 6)))
    assert endpoint_area_test(disjoint)
    assert candidates(disjoint)[0] == {parent(disjoint), rotate(parent(disjoint))}
    # Equal outer areas, but distinct and nonrotation blocks, with overlapping gaps.
    equal = (((9, 4), (2,)), ((3, 6), (2,)), ((7, 6), (2,)))
    assert sum(equal[0][0]) == sum(equal[2][0])
    assert equal[2] not in {equal[0], rotate(equal[0])}
    assert not endpoint_area_test(equal)
    assert candidates(equal)[0] == {parent(equal), rotate(parent(equal))}
    print('PASS: disjoint-support and genuinely distinct equal-exterior-area controls.')
    e3 = near(power2, e)
    distinct = e, power2, e3
    moved = power2, e, e3
    largest_pair_span = betas(power2)[0][0] + betas(e3)[0][0]
    assert any(largest_pair_span in mon for mon, _ in middle(distinct))
    assert all(largest_pair_span not in mon for mon, _ in middle(moved))
    assert len(candidates(distinct)[0]) == 4
    print('CONTROL: moving the unique smallest-span block to the middle removes the highest pair generator.')
    pool = tuple(profiles(3, 3))
    cofactor_tests = 0
    for a, b in product(pool, repeat=2):
        assert leading(near(a, b)) == multiply(leading(a), leading(b))
        cofactor_tests += 1
    same_span = (((2, 4), (1,)), ((3, 4), (2,)), ((4, 4), (3,)))
    assert {betas(p)[0][0] for p in same_span} == {5}
    rotations = tuple(same_span[i:] + same_span[:i] for i in range(3))
    assert len({coefficient(middle(bs), 10) for bs in rotations}) == 3
    tied_minimum = (((2, 3), (1,)), ((3, 3), (2,)), ((4, 4), (1,)))
    a, b, c = tied_minimum
    assert coefficient(middle((a, c, b)), 11) != coefficient(middle((b, a, c)), 11)
    print('PASS: maximal-generator cofactor multiplicativity:', cofactor_tests, 'near-concatenations.')
    print('CONTROL: tied-minimum and three-equal-span cyclic middle readings are separated by their highest pair coefficient.')
    if not args.skip_sweep:
        fixed_merger_sweep()
    print('ALL PASS')


if __name__ == '__main__':
    main()
