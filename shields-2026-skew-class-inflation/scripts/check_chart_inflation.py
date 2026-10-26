#!/usr/bin/env python3
r"""Paper section `sec:profile-transport` (Profile transport).

Checks `lem:inflate-chart` on actual cells, all four attachment types and all
three alternatives.  The deterministic box has inners with 1..3 rows, row
lengths 1..5 and area at most 10, every legal overlap, and every connected
nonrow outer of area 2..4.  Named witnesses additionally pin each alternative,
nonhorizontal marks and mixed supplements; a fixed 5-by-5 square supplies
negative I/III/IV predicate controls.  No class census is inferred.

The existing composition engine supplies the cell convention and composition.
Candidate marks come from full intersections; I is checked independently by
all possible larger end subdiagrams, III by the actual complements, and IV by
exact membership in the bi-infinite chain.  Its finite translate bounds are
derived from content support and the positive period, never from a fixed K.
Input legality, properness, nonrow outer and zero-free inflated parent are
asserted independently of the output comparison.  Arithmetic is integer-only.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product

from _composition_engine import (
    attachment_case, beta_from_cells, cells_from_rho_a, compose,
    connected_skew_subdiagrams, enum_rho_a, is_connected_skew, ne_cell,
    normalize, rotate, row_intervals, shift, sw_cell, v_of_W,
)

EMPTY = frozenset()
EAST = (0, 1)
DIAGONAL = (1, 1)


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def sub(a, b):
    return a[0]-b[0], a[1]-b[1]


def content(cell):
    return cell[1]-cell[0]


def span(cells):
    return len({content(cell) for cell in cells})


def inflate(cells):
    """Extend each actual row east by one; preserve its row and left endpoint."""
    return frozenset((i, j) for i, (lo, hi) in row_intervals(cells).items()
                     for j in range(lo, hi+2))


def antitranspose(cells):
    return normalize(frozenset((-j, -i) for i, j in cells))


def zero_free(cells):
    x, y = beta_from_cells(cells)
    return set(x).isdisjoint(y)


def no_minus_one(cells):
    x, y = beta_from_cells(cells)
    return all(a-b != -1 for a in x for b in y)


def diagonal_intervals(cells):
    rows = defaultdict(list)
    for cell in cells:
        rows[content(cell)].append(cell[0])
    return {c: (min(values), max(values)) for c, values in rows.items()}


def in_periodic_union(cell, cells, displacement):
    """Decide membership in union_{k in Z}(cells+k*v), with an exact bound.

    If the support is [lo,hi] and c(v)=q>0, only
    ceil((c(cell)-hi)/q) <= k <= floor((c(cell)-lo)/q) can contribute.
    """
    if not cells:
        return False
    q = content(displacement)
    assert q > 0
    lo = min(map(content, cells))
    hi = max(map(content, cells))
    first = -((hi-content(cell))//q)
    last = (content(cell)-lo)//q
    return any((cell[0]-k*displacement[0], cell[1]-k*displacement[1]) in cells
               for k in range(first, last+1))


def hats(inner, lower, upper, displacement):
    middle = inner-lower-upper
    middle_hat = frozenset(cell for cell in middle if add(cell, DIAGONAL) in middle)
    mark_hat = {sub(cell, DIAGONAL) for cell in lower
                if in_periodic_union(sub(cell, DIAGONAL), inner, displacement)}
    mark_hat.update(cell for cell in lower
                    if in_periodic_union(add(cell, DIAGONAL), inner, displacement))
    return middle_hat, frozenset(mark_hat)


def all_integer_iv(inner, lower, upper, displacement):
    """Periodicity reduces every middle copy to the zeroth one, not a window."""
    middle_hat, mark_hat = hats(inner, lower, upper, displacement)
    for i, j in middle_hat:
        for neighbor in ((i-1, j), (i+1, j), (i, j-1), (i, j+1)):
            if in_periodic_union(neighbor, mark_hat, displacement):
                return False
    return True


@lru_cache(None)
def possible_lower_end_marks(inner):
    """All congruent end pairs, before separation, attachment or IV tests.

    Larger competitors for I may overlap, so no disjointness filter belongs
    here.  Enumerating row-interval subdiagrams is independent of the full-
    intersection construction used to propose the tested marks.
    """
    pieces = connected_skew_subdiagrams(inner)
    upper_shapes = {normalize(piece) for piece in pieces if ne_cell(inner) in piece}
    return tuple(piece for piece in pieces
                 if sw_cell(inner) in piece and normalize(piece) in upper_shapes)


def mark_failures(inner, lower, upper, case, displacement):
    failures = set()
    if not is_connected_skew(inner):
        return {'inner'}
    if not lower:
        if upper or case != 'a' or displacement != v_of_W(inner, EMPTY, EMPTY, 'a'):
            failures.add('EMPTY')
        if content(displacement) != span(inner):
            failures.add('II')
        return failures
    q, w = content(displacement), span(lower)
    if (not is_connected_skew(lower) or not is_connected_skew(upper)
            or not lower <= inner or not upper <= inner
            or shift(lower, displacement) != upper
            or sw_cell(inner) not in lower or ne_cell(inner) not in upper):
        failures.add('mark')
    if not (0 < w < q and q+w == span(inner) and lower.isdisjoint(upper)):
        failures.add('II')
    contents = {content(cell) for cell in lower}
    if any(lower < larger and {content(cell) for cell in larger} == contents
           for larger in possible_lower_end_marks(inner)):
        failures.add('I')
    if (not is_connected_skew(inner-lower) or not is_connected_skew(inner-upper)):
        failures.add('III')
    middle = inner-lower-upper
    if (not is_connected_skew(middle)
            or attachment_case(inner, lower, upper, middle) != case):
        failures.add('attachment')
    if q <= 0 or not all_integer_iv(inner, lower, upper, displacement):
        failures.add('IV')
    return failures


def candidate_marks(inner):
    """Generate genuine horizontal EMPTY, then positive full end intersections."""
    yield EMPTY, EMPTY, 'a', v_of_W(inner, EMPTY, EMPTY, 'a')
    sw = sw_cell(inner)
    for w in range(1, (span(inner)-1)//2+1):
        q = span(inner)-w
        for endpoint in sorted(inner):
            if content(endpoint)-content(sw) != q:
                continue
            displacement = sub(endpoint, sw)
            lower = inner & shift(inner, (-displacement[0], -displacement[1]))
            upper = shift(lower, displacement)
            if (not lower or span(lower) != w or sw not in lower
                    or ne_cell(inner) not in upper):
                continue
            middle = inner-lower-upper
            if not is_connected_skew(middle):
                continue
            case = attachment_case(inner, lower, upper, middle)
            if case is not None:
                yield lower, upper, case, displacement


def literal_union(outer, inner, upper, case, displacement, supplements=True):
    """Cell union using diagonal endpoints, independently of engine offsets."""
    intervals = diagonal_intervals(outer)
    origins, ranks = {}, {}
    for cell in outer:
        i, c = cell[0], content(cell)
        lo, hi = intervals[c]
        rank = i-lo if case == 'c' else hi-i
        ranks[cell] = rank
        offset = {'a': i, 'b': -i, 'c': rank, 'd': -rank}[case]
        origins[cell] = (c*displacement[0]+offset, c*displacement[1]+offset)
    result = set()
    for origin in origins.values():
        result.update(shift(inner, origin))
    if supplements and case in ('c', 'd'):
        extra = DIAGONAL if case == 'c' else (-1, -1)
        for cell, origin in origins.items():
            north = cell[0]-1, cell[1]
            if north in outer and ranks[north] == ranks[cell]:
                result.update(shift(upper, add(origin, extra)))
    return normalize(result)


def phases(inner, lower, upper, displacement):
    middle = inner-lower-upper
    base = content(sw_cell(inner))
    return (max(map(content, middle))-base-content(displacement)+1,
            min(map(content, middle))-base)


def check_chart(outer, inner, lower, upper, case, displacement, counts):
    """All premises are independently asserted before the branch is constructed."""
    assert is_connected_skew(outer) and len(outer) >= 2
    assert len(row_intervals(outer)) > 1, 'the supplied outer must not be a row'
    assert len(inner) >= 2
    assert not mark_failures(inner, lower, upper, case, displacement)
    parent = literal_union(outer, inner, upper, case, displacement)
    assert parent == compose(outer, inner, lower, upper, case, displacement)
    assert is_connected_skew(parent)
    target = normalize(inflate(parent))
    assert zero_free(target), 'zero-free inflated parent is an input, not an output filter'
    assert no_minus_one(parent)
    q, w = content(displacement), span(lower)
    assert span(parent) == span(outer)*q+w

    if w == q-1:
        branch = 'atom'
        assert case == 'a'
        middle = inner-lower-upper
        assert middle == frozenset({add(ne_cell(lower), EAST)})
        assert phases(inner, lower, upper, displacement) == (0, w)
        assert displacement == add(sub(ne_cell(lower), sw_cell(lower)), (0, 2))
        new_outer, new_inner = normalize(inflate(outer)), normalize(inflate(lower))
        new_lower, new_upper, new_case = EMPTY, EMPTY, 'a'
        new_displacement = v_of_W(new_inner, EMPTY, EMPTY, 'a')
        assert new_displacement == displacement
        assert zero_free(new_outer) and no_minus_one(outer)
        # Naively retaining the enlarged positive mark violates separation.
        naive_lower, naive_upper = inflate(lower), inflate(upper)
        assert span(naive_lower) == q
        assert 'II' in mark_failures(inflate(inner), naive_lower, naive_upper,
                                     case, displacement)
    else:
        new_outer, new_inner = outer, inflate(inner)
        new_displacement, new_case = displacement, case
        if w == 0:
            branch = 'empty'
            assert case == 'a' and lower == upper == EMPTY
            new_lower = frozenset({sw_cell(inner)})
            new_upper = frozenset({add(ne_cell(inner), EAST)})
            assert phases(new_inner, new_lower, new_upper, displacement) == (0, 1)
        else:
            branch = 'interior'
            assert 0 < w < q-1
            new_lower, new_upper = inflate(lower), inflate(upper)
            tau, sigma = phases(inner, lower, upper, displacement)
            assert 0 <= tau < w and 1 <= sigma <= w
            if case in ('c', 'd'):
                assert tau < sigma
            expected = {'a': (tau, sigma+1), 'b': (tau+1, sigma),
                        'c': (tau+1, sigma+1), 'd': (tau, sigma)}[case]
            assert phases(new_inner, new_lower, new_upper, displacement) == expected
            counts['interior_'+case] += 1
        assert span(new_lower) == w+1
        assert shift(new_lower, displacement) == new_upper
        assert new_lower == new_inner & shift(new_inner, (-displacement[0], -displacement[1]))
        intervals = diagonal_intervals(new_inner)
        base = content(sw_cell(new_inner))
        assert intervals[base+w+1][0] == intervals[base+w+1][1]
        assert intervals[base+q-1][0] == intervals[base+q-1][1]

    assert not mark_failures(new_inner, new_lower, new_upper, new_case, new_displacement)
    actual = compose(new_outer, new_inner, new_lower, new_upper, new_case, new_displacement)
    independent = literal_union(new_outer, new_inner, new_upper, new_case, new_displacement)
    assert actual == independent == target, (branch, case, outer, inner, lower)
    assert content(new_displacement) == q
    if case in ('c', 'd'):
        bare = literal_union(outer, inner, upper, case, displacement, supplements=False)
        if bare != parent:
            assert bare < parent
            counts['supplement_'+case] += 1
        bare_new = literal_union(new_outer, new_inner, new_upper, new_case,
                                 new_displacement, supplements=False)
        if bare_new != target:
            assert bare_new < target
            counts['inflated_supplement_'+case] += 1
    if lower and len(row_intervals(lower)) > 1:
        counts['nonhorizontal_mark'] += 1
    assert normalize(inflate(rotate(parent))) == rotate(target)
    counts[branch] += 1
    return branch


def witnesses(counts):
    outer = cells_from_rho_a((1, 1), (1,))
    # The singleton-mark ordinary VV and maximal-width HH atom use the same
    # inner but different full marks.  Width alone cannot identify the chart.
    examples = (
        ((2,), (), 0, 'a', 'empty'),
        ((4,), (), 1, 'a', 'interior'),
        ((1, 3, 1), (1, 1), 1, 'b', 'interior'),
        ((4, 1), (1,), 1, 'd', 'interior'),
        ((1, 4), (1,), 1, 'c', 'interior'),
        ((1, 4, 2), (1, 2), 2, 'a', 'interior'),
        ((3,), (), 1, 'a', 'atom'),
        ((1, 3, 1), (1, 1), 2, 'a', 'atom'),
    )
    for rows, overlaps, width, expected_case, branch in examples:
        inner = cells_from_rho_a(rows, overlaps)
        matches = [(lower, upper, case, v) for lower, upper, case, v in candidate_marks(inner)
                   if span(lower) == width and case == expected_case
                   and not mark_failures(inner, lower, upper, case, v)]
        assert len(matches) == 1, (rows, width, expected_case)
        assert check_chart(outer, inner, *matches[0], counts) == branch

    # Genuine EMPTY has an edge displacement; its vertical reading changes the
    # outer by antitransposition.  A cell is not an empty mark.
    inner = cells_from_rho_a((2, 3), (2,))
    v_h = v_of_W(inner, EMPTY, EMPTY, 'a')
    v_v = v_of_W(inner, EMPTY, EMPTY, 'b')
    assert v_v == sub(v_h, DIAGONAL)
    horizontal = compose(antitranspose(outer), inner, EMPTY, EMPTY, 'a', v_h)
    assert compose(outer, inner, EMPTY, EMPTY, 'b', v_v) == horizontal
    assert compose(outer, inner, EMPTY, EMPTY, 'a', v_h) != horizontal
    assert mark_failures(inner, EMPTY, EMPTY, 'a', v_v) == {'EMPTY'}
    # Exercise a nonzero, negative translate rather than a fixed finite chain.
    for k in (-101, -2, 0, 3, 137):
        cell = add(sw_cell(inner), (k*v_h[0], k*v_h[1]))
        assert in_periodic_union(cell, inner, v_h)
    assert not in_periodic_union((10**6, 10**6), frozenset({(0, 0)}), (0, 2))

    # The full hat includes marked cells with a southeastern neighbor in the
    # infinite chain, not merely the northwest interior of W itself.
    square = cells_from_rho_a((5,)*5, (5,)*4)
    lower = frozenset((i, j) for i in (3, 4) for j in (0, 1))
    displacement = (-3, 3)
    upper = shift(lower, displacement)
    middle_hat, mark_hat = hats(square, lower, upper, displacement)
    assert (2, 1) in middle_hat and (3, 1) in mark_hat
    assert (4, 2) not in lower and (4, 2) in square
    assert not all_integer_iv(square, lower, upper, displacement)
    assert 'III' in mark_failures(square, lower, upper, 'a', displacement)
    # A proper subset on the same content band is not a maximal mark, even
    # when its two congruent copies retain the actual extreme cells.
    incomplete = lower-frozenset({(4, 1)})
    assert is_connected_skew(incomplete) and span(incomplete) == span(lower)
    assert 'I' in mark_failures(square, incomplete, shift(incomplete, displacement),
                               'a', displacement)


def main():
    counts = Counter()
    witnesses(counts)
    outers = sorted({cells_from_rho_a(rows, overlaps)
                     for rows, overlaps in enum_rho_a(4, minsize=2) if len(rows) > 1},
                    key=lambda cells: (len(cells), sorted(cells)))
    for n in range(1, 4):
        for rows in product(range(1, 6), repeat=n):
            if not 2 <= sum(rows) <= 10:
                continue
            for overlaps in product(*(range(1, min(a, b)+1)
                                      for a, b in zip(rows, rows[1:]))):
                inner = cells_from_rho_a(rows, overlaps)
                for lower, upper, case, displacement in candidate_marks(inner):
                    if mark_failures(inner, lower, upper, case, displacement):
                        continue
                    for outer in outers:
                        parent = compose(outer, inner, lower, upper, case, displacement)
                        assert is_connected_skew(parent)
                        if not zero_free(inflate(parent)):
                            counts['excluded_nonzero_free_parent'] += 1
                            continue
                        check_chart(outer, inner, lower, upper, case, displacement, counts)
    for key in ('empty', 'interior', 'atom', 'nonhorizontal_mark',
                'interior_a', 'interior_b', 'interior_c', 'interior_d',
                'supplement_c', 'supplement_d', 'inflated_supplement_c',
                'inflated_supplement_d', 'excluded_nonzero_free_parent'):
        assert counts[key] > 0, ('missing coverage', key)
    print('PASS: actual chart inflation, all three branches, I–IV, full marks and EMPTY gauge')
    print('PASS: mixed supplemental cells, phase shifts and maximal-width nonrow atom controls')
    print('SCOPE: inners 1..3 rows, lengths 1..5, area <=10; nonrow outers area 2..4')
    print('COUNTS:', dict(sorted(counts.items())))
    print('ALL PASS')


if __name__ == '__main__':
    main()
