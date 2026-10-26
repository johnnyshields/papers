"""Paper section `sec:profile-transport` (Profile transport), with cut
coefficients used in `sec:inflation-proof` (The exact inflation threshold).
Targets `lem:erosion`, `lem:inflation-lowering`, `cor:inflation-no-escape`
and `lem:zero-free-bijection`.

Exact integer polynomials retain h_0=1 and kill negative indices.  Erosion
is compared with determinants of actual cell components, including vanished
rows.  The transport box has 1..4 rows of length 1..4, total area at most 9,
and every legal adjacent overlap.  Raising is checked only on its no-minus-one
domain, with explicit off-domain and non-inverse controls.  Cut sets are
enumerated independently of determinants.  None of these finite checks proves
the uniform transport results.
"""
from collections import Counter, defaultdict
from itertools import product
from time import monotonic
from check_two_residue_decoder import betas, poly, cell_permutation
from _composition_engine import (
    cells_from_rho_a, is_connected_skew, normalize, rotate, row_intervals,
)

START = monotonic()

def say(text):
    print(f'{monotonic()-START:.2f}s {text}', flush=True)

def cuts(alpha):
    out, total = [], 0
    for a in alpha[:-1]:
        total += a
        out.append(total)
    return tuple(out)

def composition(M, positions):
    bounds = (0,)+tuple(sorted(positions))+(M,)
    return tuple(b-a for a, b in zip(bounds, bounds[1:]))

def coarsening(alpha):
    S = cuts(alpha)
    M, n = sum(alpha), len(alpha)
    out = Counter()
    for mask in range(1 << len(S)):
        gamma = composition(M, [z for i, z in enumerate(S) if mask >> i & 1])
        out[tuple(sorted(gamma))] += (-1)**(n-len(gamma))
    return {m: c for m, c in out.items() if c}

def two_piece(alpha):
    M, n = sum(alpha), len(alpha)
    if n == 1:
        return {}
    out = Counter(tuple(sorted((z, M-z))) for z in cuts(alpha))
    return {m: (-1)**(n-2)*c for m, c in out.items()}

def lower(pol, t, n, degree_filter=True, strict=False):
    if t == 0:
        return pol.copy()
    out = Counter()
    for mon, c in pol.items():
        if degree_filter and len(mon) != n:
            continue
        if not all(j > t if strict else j >= t for j in mon):
            continue
        out[tuple(j-t for j in mon if j != t)] += c
    return {m: c for m, c in out.items() if c}

def cut_fibers():
    count = Counter()
    for M in range(1, 15):
        fibers = defaultdict(list)
        for mask in range(1 << (M-1)):
            S = tuple(z for z in range(1, M) if mask >> (z-1) & 1)
            signature = tuple(sorted(Counter(min(z, M-z) for z in S).items()))
            fibers[signature].append(S)
            count['cut_sets'] += 1
        for signature, fiber in fibers.items():
            for S in fiber:
                if S != tuple(sorted(M-z for z in S)):
                    continue
                assert len(fiber) == 1
                recovered = set()
                for z, multiplicity in signature:
                    if 2*z == M:
                        assert multiplicity == 1
                        recovered.add(z)
                        count['central_cuts'] += 1
                    else:
                        assert multiplicity == 2
                        recovered.update((z, M-z))
                assert recovered == set(S)
                alpha = composition(M, S)
                assert alpha == alpha[::-1]
                count['palindromic_singleton_fibers'] += 1
        say(f'cut totals through weight {M}: {dict(count)}')
    # Same support, not same coefficient data: this rejects support alone,
    # not the stronger combination of support and the known row count.
    a, b = (1, 2, 1), (1, 3)
    assert set(two_piece(a)) == set(two_piece(b)) and two_piece(a) != two_piece(b)
    assert two_piece((1, 1, 1)) == {(1, 2): -2}
    assert two_piece((2, 2)) == {(2, 2): 1}
    say(f'cut counts={dict(count)}; support-only, sign, and central-position controls fire')

def determinant_and_lowering():
    fixtures = set()
    for length in range(3):
        for half in product((1, 2, 4), repeat=length):
            for middle in ((), (1,), (4,)):
                alpha = half+middle+half[::-1]
                if alpha:
                    fixtures.add(alpha)
    fixtures.update(((1, 3, 2, 2, 3, 1), (4, 1, 5, 1, 4),
                     (6, 7, 6), (9, 2, 4, 2, 9)))
    count = Counter()
    for alpha in sorted(fixtures):
        n = len(alpha)
        p = (alpha, (0,)*(n-1))
        A, B = betas(p)
        det = poly(A, B)
        assert det == coarsening(alpha)
        assert {m: c for m, c in det.items() if len(m) == 2} == two_piece(alpha)
        count['ribbon_determinants'] += 1
        for t in (0, 1, 4, 9):
            AA = tuple(a+t for a in A)
            inflated = poly(AA, B)
            assert lower(inflated, t, n) == det
            assert all(g+t < min(a+t, b+t) for g, a, b in zip(p[1], alpha, alpha[1:]))
            if n <= 5:
                shifted_profile = (tuple(a+t for a in alpha), (t,)*(n-1))
                assert cell_permutation(shifted_profile) == inflated
                count['independent_cell_determinants'] += 1
            count['lowering_identities'] += 1
            count['nonhessenberg_inflations'] += any(AA[i]-B[j] >= 0
                                                       for i in range(n) for j in range(i-1))
            if t:
                count['missing_degree_filter_controls'] += lower(inflated, t, n, degree_filter=False) != det
                count['discarded_h0_controls'] += lower(inflated, t, n, strict=True) != det
                count['inflated_common_beta_cases'] += bool(set(AA)&set(B))
        if count['ribbon_determinants'] % 12 == 0:
            say(f'lowering progress={dict(count)}')
    assert all(count[key] for key in ('missing_degree_filter_controls', 'discarded_h0_controls',
                                      'nonhessenberg_inflations', 'inflated_common_beta_cases'))
    # The live corollary is one-sided: an equality can split under inflation.
    a = ((1, 2, 1, 3, 2), (0,)*4)
    b = ((1, 3, 2, 1, 2), (0,)*4)
    A, B = betas(a)
    C, D = betas(b)
    assert poly(A, B) == poly(C, D) and a != b and a[0] != b[0][::-1]
    split = []
    for t in (1, 2, 4, 8):
        p = poly(tuple(x+t for x in A), B)
        q = poly(tuple(x+t for x in C), D)
        assert lower(p, t, 5) == lower(q, t, 5)
        if p != q:
            split.append(t)
    assert split
    say(f'determinant/lowering counts={dict(count)}; equal ribbons split at t={split}')


def multiply(left, right):
    out = Counter()
    for a, ca in left.items():
        for b, cb in right.items():
            out[tuple(sorted(a+b))] += ca*cb
    return {m: c for m, c in out.items() if c}


def erode_cells(cells):
    return frozenset((i, j) for i, j in cells if (i, j+1) in cells)


def inflate_cells(cells):
    """Extend actual nonempty row intervals east, without moving their starts."""
    return frozenset((i, j) for i, (lo, hi) in row_intervals(cells).items()
                     for j in range(lo, hi+2))


def cell_components_polynomial(cells):
    """Independent erosion route: multiply JT functions of actual components.

    Do not compress all surviving rows together: an empty row may separate
    components, and erosion need not leave a connected diagram.
    """
    remaining = set(cells)
    result = {(): 1}
    while remaining:
        seed = min(remaining)
        component, frontier = {seed}, [seed]
        remaining.remove(seed)
        while frontier:
            i, j = frontier.pop()
            for neighbor in ((i-1, j), (i+1, j), (i, j-1), (i, j+1)):
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    component.add(neighbor)
                    frontier.append(neighbor)
        assert is_connected_skew(component)
        intervals = row_intervals(component)
        rows = sorted(intervals)
        x = tuple(intervals[i][1]+1-i for i in rows)
        y = tuple(intervals[i][0]-i for i in rows)
        result = multiply(result, poly(x, y))
    return result


def raise_no_minus_one(polynomial, rows):
    """The whole homogeneous substitution, not unconditional inflation."""
    out = Counter()
    for monomial, coefficient in polynomial.items():
        assert len(monomial) <= rows
        raised = tuple(sorted(tuple(j+1 for j in monomial)
                              + (1,)*(rows-len(monomial))))
        out[raised] += coefficient
    return {m: c for m, c in out.items() if c}


def erosion_and_raising():
    count = Counter()
    classes = defaultdict(list)
    for n in range(1, 5):
        for rows in product(range(1, 5), repeat=n):
            if sum(rows) > 9:
                continue
            for gaps in product(*(range(min(a, b))
                                  for a, b in zip(rows, rows[1:]))):
                x, y = betas((rows, gaps))
                polynomial = poly(x, y)
                cells = cells_from_rho_a(rows, tuple(g+1 for g in gaps))
                assert is_connected_skew(cells)
                assert cell_components_polynomial(cells) == polynomial
                assert max(map(len, polynomial)) == n
                eroded = erode_cells(cells)
                assert len(eroded) == len(cells)-n
                assert lower(polynomial, 1, n) == poly(tuple(a-1 for a in x), y)
                assert lower(polynomial, 1, n) == cell_components_polynomial(eroded)
                assert normalize(erode_cells(rotate(cells))) == rotate(eroded)
                assert normalize(inflate_cells(rotate(cells))) == rotate(inflate_cells(cells))
                count['erosion_profiles'] += 1
                count['empty_rows'] += len(row_intervals(eroded)) < n
                count['disconnected_erosions'] += bool(eroded) and not is_connected_skew(eroded)

                # Positive k-row overlaps come from actual interval intersections.
                intervals = row_intervals(cells)
                overlaps = 0
                for k in range(3, n+1):
                    for first in range(n-k+1):
                        common = (min(intervals[i][1] for i in range(first, first+k))
                                  - max(intervals[i][0] for i in range(first, first+k))+1)
                        overlaps += common == k-2
                minus_one = sum(a-b == -1 for a in x for b in y)
                assert minus_one == overlaps
                inflated_polynomial = poly(tuple(a+1 for a in x), y)
                assert cell_components_polynomial(inflate_cells(cells)) == inflated_polynomial
                raised = raise_no_minus_one(polynomial, n)
                if minus_one == 0:
                    assert raised == inflated_polynomial
                    count['no_minus_one_raising'] += 1
                else:
                    count['off_domain_raising_failures'] += raised != inflated_polynomial
                signature = tuple(sorted(polynomial.items()))
                classes[signature].append((cells, x, y, minus_one))

    for signature, members in classes.items():
        assert len({len(x) for _, x, _, _ in members}) == 1
        assert len({minus_one for _, _, _, minus_one in members}) == 1
        if members[0][3] == 0:
            assert len({tuple(sorted(poly(tuple(a+1 for a in x), y).items()))
                        for _, x, y, _ in members}) == 1
        source, x, y, _ = members[0]
        nonline = len(row_intervals(source)) > 1 and len({j for _, j in source}) > 1
        if set(x).isdisjoint(y) and nonline:
            assert all(set(xx).isdisjoint(yy) for _, xx, yy, _ in members)
            for cells, _, _, _ in members:
                eroded = erode_cells(cells)
                assert is_connected_skew(eroded)
                assert len(row_intervals(eroded)) == len(row_intervals(cells))
                assert inflate_cells(eroded) == cells
            eroded_key = tuple(sorted(cell_components_polynomial(erode_cells(source)).items()))
            eroded_class = classes[eroded_key]
            assert all(minus_one == 0 for _, _, _, minus_one in eroded_class)
            assert {cells for cells, _, _, _ in members} == {
                normalize(inflate_cells(cells)) for cells, _, _, _ in eroded_class
            }
            count['exact_zero_free_class_bijections'] += 1
        if len(members) > 1:
            count['nontrivial_equality_classes'] += 1

    # Erosion may be connected even though a singleton row was lost.
    unit_bearing = cells_from_rho_a((1, 2), (1,))
    survivor = erode_cells(unit_bearing)
    assert is_connected_skew(survivor)
    assert len(row_intervals(survivor)) == 1
    assert normalize(inflate_cells(survivor)) != unit_bearing
    # An empty middle row must not be removed before deriving the erosion.
    empty_middle = cells_from_rho_a((2, 1, 2), (1, 1))
    eroded = erode_cells(empty_middle)
    assert set(row_intervals(eroded)) == {0, 2}
    assert cell_components_polynomial(eroded) == {(1, 1): 1}
    x, y = betas(((2, 1, 2), (0, 0)))
    assert lower(poly(x, y), 1, 3) == {(1, 1): 1}
    # Removing the top-degree filter, or taking the minimum degree, is wrong.
    x, y = betas(((1, 2), (0,)))
    polynomial = poly(x, y)
    correct = lower(polynomial, 1, 2)
    assert correct == {(1,): 1}
    assert lower(polynomial, 1, 2, degree_filter=False) != correct
    minimum = min(map(len, polynomial))
    assert lower(polynomial, 1, minimum) != correct
    # The three-cell column has an index -1, which opens to h_0 under inflation.
    x, y = betas(((1, 1, 1), (0, 0)))
    assert any(a-b == -1 for a in x for b in y)
    assert raise_no_minus_one(poly(x, y), 3) != poly(tuple(a+1 for a in x), y)
    assert all(count[key] for key in (
        'erosion_profiles', 'empty_rows', 'disconnected_erosions',
        'no_minus_one_raising', 'off_domain_raising_failures',
        'exact_zero_free_class_bijections', 'nontrivial_equality_classes',
    ))
    say(f'erosion/raising counts={dict(count)}; empty-row and off-domain controls fire')

if __name__ == '__main__':
    cut_fibers()
    determinant_and_lowering()
    erosion_and_raising()
    say('ALL PASS')
