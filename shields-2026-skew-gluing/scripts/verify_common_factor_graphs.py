#!/usr/bin/env python3
"""Exact cell and Schur-polynomial checks of explicit common-factor graphs.

The fixtures are reversal fibers, a three-vertex fork with two different
supplied roots, and a width-zero reassociation through both edge readings of a
row.  They are not a census of all mates or all roots.  Composition is checked
both by adjacency propagation and by diagonal-rank offsets.  Mark legality uses
cell sets, all possible marked displacements, and actual hats.  No private data
files or external composition engine are used.
"""
from collections import defaultdict, deque
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, permutations
from math import gcd


def shift(shape, vector):
    return frozenset((i + vector[0], j + vector[1]) for i, j in shape)


def content(cell):
    return cell[1] - cell[0]


def southwest(shape):
    return min(shape, key=content)


def northeast(shape):
    return max(shape, key=content)


def normalize(shape):
    cell = southwest(shape)
    return shift(shape, (-cell[0], -cell[1]))


def rotate(shape):
    return normalize(frozenset((-i, -j) for i, j in shape))


def transpose(shape):
    return normalize(frozenset((j, i) for i, j in shape))


def antitranspose(shape):
    return normalize(frozenset((-j, -i) for i, j in shape))


def span(shape):
    return max(map(content, shape)) - min(map(content, shape)) + 1


def from_profile(lengths, gaps):
    """Adjacent gaps are overlaps minus one, not actual overlaps."""
    assert len(gaps) + 1 == len(lengths)
    left = 0
    cells = set()
    for i, length in enumerate(lengths):
        assert length > 0
        if i:
            gap = gaps[i - 1]
            assert 0 <= gap < min(lengths[i - 1], length)
            left += gap + 1 - length
        cells.update((i, left + j) for j in range(length))
    result = normalize(cells)
    assert is_connected_skew(result)
    return result


def is_connected_skew(shape):
    if not shape:
        return False
    rows = defaultdict(set)
    for i, j in shape:
        rows[i].add(j)
    order = sorted(rows)
    if order != list(range(order[0], order[-1] + 1)):
        return False
    bounds = [(min(rows[i]), max(rows[i])) for i in order]
    if any(len(rows[i]) != high - low + 1 for i, (low, high) in zip(order, bounds)):
        return False
    if any(a < c or b < d for (a, b), (c, d) in zip(bounds, bounds[1:])):
        return False
    reached = {next(iter(shape))}
    queue = deque(reached)
    while queue:
        i, j = queue.popleft()
        for cell in ((i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1)):
            if cell in shape and cell not in reached:
                reached.add(cell)
                queue.append(cell)
    return reached == set(shape)


@dataclass(frozen=True)
class Mark:
    inner: frozenset
    lower: frozenset
    upper: frozenset
    case: str
    displacement: tuple

    @property
    def period(self):
        return content(self.displacement)

    @property
    def width(self):
        return span(self.lower) if self.lower else 0


def empty_mark(inner):
    inner = normalize(inner)
    i, j = northeast(inner)
    return Mark(inner, frozenset(), frozenset(), 'a', (i, j + 1))


def singleton_mark(inner):
    inner = normalize(inner)
    return intersection_mark(inner, northeast(inner))


def intersection_mark(inner, displacement):
    inner = normalize(inner)
    lower = inner & shift(inner, (-displacement[0], -displacement[1]))
    upper = shift(lower, displacement)
    middle = inner - lower - upper
    assert lower and is_connected_skew(middle)
    i, j = southwest(middle)
    k, l = northeast(middle)
    lower_h = (i, j - 1) in lower
    lower_v = (i + 1, j) in lower
    upper_h = (k, l + 1) in upper
    upper_v = (k - 1, l) in upper
    assert lower_h != lower_v and upper_h != upper_v
    case = {(True, True): 'a', (False, False): 'b',
            (True, False): 'c', (False, True): 'd'}[lower_h, upper_h]
    mark = Mark(inner, lower, upper, case, displacement)
    assert legal(mark)
    return mark


def legal(mark):
    E, W, T, case, v = (mark.inner, mark.lower, mark.upper,
                         mark.case, mark.displacement)
    if not is_connected_skew(E) or len(E) < 2:
        return False
    if not W:
        return mark == empty_mark(E)
    if not (is_connected_skew(W) and is_connected_skew(T)):
        return False
    if T != shift(W, v) or not (W <= E and T <= E):
        return False
    if southwest(E) not in W or northeast(E) not in T:
        return False
    w, q = mark.width, mark.period
    if not (0 < w < q and span(E) == q + w and not W & T):
        return False
    O = E - W - T
    if not all(is_connected_skew(S) for S in (O, E - W, E - T)):
        return False
    i, j = southwest(O)
    k, l = northeast(O)
    attachments = ((i, j - 1) in W, (i + 1, j) in W,
                   (k, l + 1) in T, (k - 1, l) in T)
    expected = {'a': (True, False, True, False),
                'b': (False, True, False, True),
                'c': (True, False, False, True),
                'd': (False, True, True, False)}
    if attachments != expected[case]:
        return False
    # Every alternative displacement sends the lower extreme cell to E_q.
    # Do not prefilter alternatives by III or IV when checking maximality.
    for cell in E:
        if content(cell) != q:
            continue
        candidate = E & shift(E, (-cell[0], -cell[1]))
        if W < candidate and is_connected_skew(candidate):
            if northeast(E) in shift(candidate, cell):
                return False
    if W != E & shift(E, (-v[0], -v[1])):
        return False
    hat_o = frozenset((i, j) for i, j in O if (i + 1, j + 1) in O)
    # At contents 0,...,w-1 only E and E-v meet the infinite amalgamation.
    local = E | shift(E, (-v[0], -v[1]))
    hat_w = (frozenset((i, j) for i, j in local if (i + 1, j + 1) in W)
             | frozenset((i, j) for i, j in W if (i + 1, j + 1) in local))
    if hat_o and hat_w:
        low = (min(map(content, hat_o)) - w + q - 1) // q
        high = (max(map(content, hat_o)) + 1) // q
        for multiple in range(low, high + 1):
            translated = shift(hat_w, (multiple * v[0], multiple * v[1]))
            for i, j in hat_o:
                if any(cell in translated for cell in
                       ((i, j), (i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1))):
                    return False
    return True


def rotated_mark(mark):
    raw = frozenset((-i, -j) for i, j in mark.inner)
    x = southwest(raw)
    turn = lambda S: shift(frozenset((-i, -j) for i, j in S), (-x[0], -x[1]))
    if not mark.lower:
        return empty_mark(turn(mark.inner))
    result = Mark(turn(mark.inner), turn(mark.upper), turn(mark.lower),
                  {'a': 'a', 'b': 'b', 'c': 'd', 'd': 'c'}[mark.case],
                  mark.displacement)
    assert legal(result)
    return result


def ribbon_ranks(shape, case):
    remaining = set(shape)
    ranks = {}
    direction = -1 if case == 'c' else 1
    rank = 0
    while remaining:
        rank += 1
        layer = {p for p in remaining
                 if (p[0] + direction, p[1] + direction) not in remaining}
        assert layer
        ranks.update({p: rank for p in layer})
        remaining -= layer
    return ranks


def compose(outer, mark, supplemental=True):
    assert is_connected_skew(outer) and legal(mark)
    outer = normalize(outer)
    v, case = mark.displacement, mark.case
    ranks = ribbon_ranks(outer, case) if case in 'cd' else {}
    links = defaultdict(list)

    def link(p, q, delta):
        links[p].append((q, delta))
        links[q].append((p, (-delta[0], -delta[1])))

    for i, j in outer:
        p = (i, j)
        for q, north in (((i, j + 1), False), ((i - 1, j), True)):
            if q not in outer:
                continue
            if case in 'ab':
                extra = (-1 if case == 'a' else 1) if north else 0
                link(p, q, (v[0] + extra, v[1] + extra))
            elif ranks[p] == ranks[q]:
                link(p, q, v)
        if case in 'cd' and (i + 1, j + 1) in outer:
            link(p, (i + 1, j + 1), (1, 1))
    origins = {(0, 0): (0, 0)}
    queue = deque(origins)
    while queue:
        p = queue.popleft()
        for q, delta in links[p]:
            candidate = (origins[p][0] + delta[0], origins[p][1] + delta[1])
            if q in origins:
                assert origins[q] == candidate
            else:
                origins[q] = candidate
                queue.append(q)
    assert set(origins) == set(outer)
    result = set()
    for origin in origins.values():
        result.update(shift(mark.inner, origin))
    if supplemental and case in 'cd':
        sign = 1 if case == 'c' else -1
        for p, origin in origins.items():
            north = (p[0] - 1, p[1])
            if north in outer and ranks[north] == ranks[p]:
                result.update(shift(mark.upper, (origin[0] + sign, origin[1] + sign)))
    result = normalize(result)
    if supplemental:
        assert is_connected_skew(result)
    return result


def compose_by_offsets(outer, mark):
    outer = normalize(outer)
    diagonals = defaultdict(list)
    for i, j in outer:
        diagonals[j - i].append(i)
    result = set()
    origins, ranks = {}, {}
    for i, j in outer:
        t = j - i
        if mark.case == 'a':
            axial = i
        elif mark.case == 'b':
            axial = -i
        elif mark.case == 'c':
            axial = i - min(diagonals[t])
        else:
            axial = i - max(diagonals[t])
        origins[i, j] = (t * mark.displacement[0] + axial,
                         t * mark.displacement[1] + axial)
        ranks[i, j] = (i - min(diagonals[t]) if mark.case == 'c'
                       else max(diagonals[t]) - i)
        result.update(shift(mark.inner, origins[i, j]))
    if mark.case in 'cd':
        sign = 1 if mark.case == 'c' else -1
        for (i, j), origin in origins.items():
            if (i - 1, j) in outer and ranks[i, j] == ranks[i - 1, j]:
                result.update(shift(mark.upper, (origin[0] + sign, origin[1] + sign)))
    return normalize(result)


def matrix_indices(shape):
    rows = sorted({i for i, _ in shape})
    ends = [(min(j for k, j in shape if k == i),
             max(j for k, j in shape if k == i)) for i in rows]
    X = [hi + 1 - i for i, (_, hi) in zip(rows, ends)]
    Y = [lo - i for i, (lo, _) in zip(rows, ends)]
    return [[x - y for y in Y] for x in X]


@lru_cache(None)
def schur(shape):
    board = matrix_indices(shape)
    # Reverse both row and column orders, preserving the determinant sign.
    board = [row[::-1] for row in board[::-1]]
    states = {0: {(): 1}}
    for row in board:
        following = {}
        for mask, polynomial in states.items():
            for j, entry in enumerate(row):
                if entry < 0 or mask & (1 << j):
                    continue
                sign = -1 if (mask >> (j + 1)).bit_count() % 2 else 1
                target = following.setdefault(mask | (1 << j), defaultdict(int))
                for monomial, coefficient in polynomial.items():
                    term = tuple(sorted(monomial + ((entry,) if entry else ())))
                    target[term] += sign * coefficient
        states = {mask: {m: c for m, c in terms.items() if c}
                  for mask, terms in following.items()}
    return tuple(sorted(states[(1 << len(board)) - 1].items()))


def bareiss(matrix):
    a = [row[:] for row in matrix]
    n, previous, sign = len(a), 1, 1
    for k in range(n - 1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        value = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * value - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = value
    return sign * a[-1][-1]


def check_polynomial(shape):
    polynomial = schur(shape)
    assert polynomial
    board = matrix_indices(shape)
    for seed in (7, 23):
        def value(index):
            if index < 0:
                return 0
            if index == 0:
                return 1
            return (seed * index ** 3 + 17 * index ** 2 + 31 * index + seed ** 2) % 1009 + 1
        evaluation = 0
        for monomial, coefficient in polynomial:
            term = coefficient
            for index in monomial:
                term *= value(index)
            evaluation += term
        assert evaluation == bareiss([[value(x) for x in row] for row in board])
    if len(board) <= 7:
        direct = defaultdict(int)
        for permutation in permutations(range(len(board))):
            indices = [board[i][j] for i, j in enumerate(permutation)]
            if min(indices) < 0:
                continue
            inversions = sum(permutation[i] > permutation[j]
                             for i in range(len(board)) for j in range(i + 1, len(board)))
            direct[tuple(sorted(i for i in indices if i))] += (-1) ** inversions
        assert tuple(sorted((m, c) for m, c in direct.items() if c)) == polynomial
    return polynomial


def mark_key(mark):
    def raw(m):
        return (tuple(sorted(m.inner)), tuple(sorted(m.lower)),
                tuple(sorted(m.upper)), m.case, m.displacement)
    return min(raw(mark), raw(rotated_mark(mark)))


def witness_graph(records):
    """Each record is an actual parent and a supplied proper chart."""
    fibers = defaultdict(set)
    polynomials = {}
    for parent, outer, mark in records:
        assert len(outer) >= 2 and len(mark.inner) >= 2 and legal(mark)
        assert compose(outer, mark) == compose_by_offsets(outer, mark) == parent
        polynomials[parent] = check_polynomial(parent)
        fibers[(mark_key(mark), check_polynomial(outer))].add(parent)
    vertices = set(polynomials)
    assert len(set(polynomials.values())) == 1
    edges = {frozenset(pair) for fiber in fibers.values() for pair in combinations(fiber, 2)}
    assert len(edges) == len(vertices) * (len(vertices) - 1) // 2
    return len(vertices), len(edges)


def reversal_fiber(outer, mark):
    records = [(compose(D, M), D, M) for D in (outer, rotate(outer))
               for M in (mark, rotated_mark(mark))]
    assert len({S for S, _, _ in records}) == 4
    return witness_graph(records)


def explicit_fork():
    H = from_profile((2, 1), (0,))
    V = from_profile((4, 1), (0,))
    fine, middle = singleton_mark(H), singleton_mark(V)
    assert fine.case == middle.case == 'd'
    D = compose(H, middle)
    B = compose(V, fine)
    coarse = intersection_mark(B, tuple(middle.period * x for x in fine.displacement))
    DX = compose(H, rotated_mark(middle))
    DZ = compose(rotate(H), middle)
    X, Y, Z = (compose(DX, fine), compose(D, fine), compose(DZ, fine))
    assert len(X) == len(Y) == len(Z) == 32
    assert compose(H, coarse) == Y and compose(rotate(H), coarse) == Z
    assert len({min(tuple(sorted(S)), tuple(sorted(rotate(S)))) for S in (X, Y, Z)}) == 3
    assert DX not in (D, rotate(D)) and schur(DX) == schur(D) == schur(DZ)
    records = [(X, DX, fine), (Y, D, fine), (Z, DZ, fine),
               (Y, H, coarse), (Z, rotate(H), coarse)]
    assert (fine.period, coarse.period) == (2, 8)
    vertices, edges = witness_graph(records)
    assert compose(D, fine, supplemental=False) != Y
    return vertices, edges, len(schur(Y))


def nondividing_roots():
    H = from_profile((2, 1), (0,))
    square = from_profile((2, 2), (1,))
    base_outer = from_profile((12, 6), (0,))
    sizes = []
    for fine in (singleton_mark(H), empty_mark(square)):
        parent = compose(base_outer, fine)
        periods = []
        for a in (2, 3):
            V = from_profile((a,), ())
            inner = compose(V, fine)
            coarse = (intersection_mark(inner, tuple(a * x for x in fine.displacement))
                      if fine.width else empty_mark(inner))
            outer = from_profile((12 // a, 6 // a), (0,))
            assert compose(outer, coarse) == compose_by_offsets(outer, coarse) == parent
            assert legal(coarse)
            periods.append(coarse.period)
        assert all(p % q and q % p for p, q in [periods])
        assert gcd(*periods) == fine.period
        # Recover the gcd inner from the two extreme windows, not its input name.
        g, width, n = fine.period, fine.width, span(parent)
        lower = frozenset(x for x in parent if content(x) < g)
        last = frozenset(x for x in parent if content(x) >= n - g)
        target = next(x for x in parent if content(x) == width)
        origin = next(x for x in parent if content(x) == n - g)
        recovered = lower | shift(last, (target[0] - origin[0], target[1] - origin[1]))
        assert recovered == fine.inner
        assert compose(base_outer, fine) == compose_by_offsets(base_outer, fine)
        sizes.append((len(parent), tuple(periods), g))
    return sizes


def width_zero_reassociation():
    """Width-zero reassociation through both legal coarse marks of U = V o E."""
    E = from_profile((2, 3, 2), (1, 1))
    omega = intersection_mark(E, (-1, 2))
    domino = from_profile((1, 1), (0,))
    assert omega.case == 'a' and normalize(omega.lower) == normalize(omega.upper) == domino
    V = from_profile((2,), ())
    U = compose(V, omega)
    assert U == compose_by_offsets(V, omega) == from_profile((2, 4, 4, 2), (1, 2, 1))
    # Every candidate displacement carries the southwest cell (0, 0) of U into U.
    candidates = []
    for x in U:
        lower = U & shift(U, (-x[0], -x[1]))
        if lower:
            candidates += [Mark(U, lower, shift(lower, x), case, x) for case in 'abcd']
    marks = sorted((mark for mark in candidates if legal(mark)), key=lambda mark: mark.case)
    assert [(mark.case, mark.displacement) for mark in marks] == [('a', (-2, 4)), ('b', (-3, 3))]
    eta_h, eta_v = marks
    assert eta_v == intersection_mark(U, (-3, 3)) and eta_v.lower == frozenset({(0, 0), (0, 1)})
    horizontal = empty_mark(V)
    i, j = horizontal.displacement
    # The vertical edge reading is a change of coordinates, not a legal mark,
    # so only the offset formula composes through it.
    vertical = Mark(V, frozenset(), frozenset(), 'b', (i - 1, j - 1))
    assert not legal(vertical)
    # The case-(a) copy origin tv + ie carries the two edge displacements of V
    # to the two coarse displacements.
    origin = lambda d: (content(d) * omega.displacement[0] + d[0],
                        content(d) * omega.displacement[1] + d[0])
    assert origin(horizontal.displacement) == eta_h.displacement
    assert origin(vertical.displacement) == eta_v.displacement
    outers = [from_profile(*p) for p in (((1,), ()), ((2,), ()), ((1, 1), (0,)),
                                         ((2, 1), (0,)), ((1, 2), (0,)), ((3,), ()))]
    fired = 0
    for C in outers:
        A = antitranspose(C)
        left = compose(C, eta_v)
        middle = compose(A, horizontal)
        assert left == compose_by_offsets(C, eta_v)
        assert middle == compose_by_offsets(A, horizontal) == compose_by_offsets(C, vertical)
        assert left == compose(middle, omega) == compose_by_offsets(middle, omega)
        unchanged = compose(compose(C, horizontal), omega)
        assert compose(C, eta_h) == compose_by_offsets(C, eta_h) == unchanged
        # The unchanged outer fails at the vertical displacement whenever AT
        # moves C; a single cell is fixed by AT.
        assert (unchanged != left) == (A != C)
        fired += unchanged != left
    assert fired, "Unchanged-outer control"
    C = from_profile((2,), ())
    left, unchanged = compose(C, eta_v), compose(compose(C, horizontal), omega)
    assert left == from_profile((2, 4, 4, 2, 4, 4, 2), (1, 2, 1, 1, 2, 1))
    assert unchanged == from_profile((2, 4, 5, 5, 4, 2), (1, 2, 2, 2, 1))
    assert check_polynomial(left) != check_polynomial(unchanged), "Polynomial control"
    return omega, vertical, eta_h, eta_v, outers


def controls():
    H = from_profile((2, 1), (0,))
    good = singleton_mark(H)
    bad = Mark(good.inner, good.lower, good.upper, 'a', good.displacement)
    assert not legal(bad), "Attachment mutation must be rejected"
    assert schur(from_profile((3,), ())) != schur(H), "Polynomial inequality control"
    unit = from_profile((1,), ())
    try:
        witness_graph([(compose(unit, good), unit, good)])
    except AssertionError:
        pass
    else:
        raise AssertionError("A one-cell outer was admitted as a proper chart")
    # A disjoint union of cliques has local gluing but need not be connected.
    edges = {frozenset((0, 1)), frozenset((2, 3))}
    assert not any(frozenset((a, b)) in edges and frozenset((b, c)) in edges
                   and frozenset((a, c)) not in edges
                   for a, b, c in permutations(range(4), 3))
    assert frozenset((0, 2)) not in edges
    print("CONTROLS PASS: attachment, properness, polynomial inequality, missing supplement, "
          "unchanged vertical-edge outer, disconnected cliques")


def main():
    H = from_profile((2, 1), (0,))
    ordinary = from_profile((2, 3), (0,))
    families = (("singleton mixed", singleton_mark(H)),
                ("empty ordinary", empty_mark(H)),
                ("singleton ordinary", singleton_mark(ordinary)),
                ("singleton vertical", singleton_mark(transpose(ordinary))))
    assert {mark.case for _, mark in families} == {'a', 'b', 'd'}
    assert rotated_mark(families[0][1]).case == 'c'
    for name, mark in families:
        vertices, edges = reversal_fiber(H, mark)
        print(f"{name}: {vertices} vertices, {edges} certified edges")
    vertices, edges, terms = explicit_fork()
    print(f"32-cell fork: {vertices} vertices, {edges} certified edges, {terms} exact parent monomials")
    for size, periods, g in nondividing_roots():
        print(f"nondividing roots: {size} cells, periods {periods}, reconstructed gcd period {g}")
    omega, vertical, eta_h, eta_v, outers = width_zero_reassociation()
    print(f"width-zero reassociation: {len(outers)} outers, coarse displacement "
          f"{eta_h.displacement} keeps the outer and {eta_v.displacement} antitransposes it")
    controls()
    print("ALL PASS")


if __name__ == '__main__':
    main()
