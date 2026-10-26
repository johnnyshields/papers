"""Skew-diagram and marked-composition machinery shared by the sweeps in this directory.

Cell sets, normalization, content and span, connectivity of skew shapes, the mark record, the
legality test for a mark (by cell sets, all marked displacements, and actual hats), and the
composition of an outer shape with a mark by adjacency propagation.  Import-only; asserts nothing
about the paper.  Copied verbatim from the companion supplement of the gluing paper so that this
directory runs on its own.
"""
from collections import defaultdict, deque
from dataclasses import dataclass
from functools import lru_cache



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


