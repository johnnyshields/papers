#!/usr/bin/env python3
"""Exact cell-set controls for source-minimal components and their keys.

No research engine or other verifier is imported.  Mark legality is checked by
end intersections, skew complements, and exact membership in the infinite
amalgamation.  Composition uses the displayed cell-placement definition, with
boundary ribbons obtained by deletion.  Sparse complete-homogeneous determinants
are cross-checked by SymPy integer determinants; the tiny hook class is also
checked by direct semistandard tableaux.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, product
from math import prod

from sympy import Matrix

Cell = tuple[int, int]
Shape = frozenset[Cell]
Polynomial = dict[tuple[int, ...], int]


def add(x: Cell, y: Cell) -> Cell:
    return x[0] + y[0], x[1] + y[1]


def shifted(shape: Shape, vector: Cell) -> Shape:
    return frozenset(add(x, vector) for x in shape)


def normalize(shape: Shape) -> Shape:
    assert shape
    return shifted(shape, (-min(i for i, _ in shape), -min(j for _, j in shape)))


def partition_shape(lam, mu=()) -> Shape:
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return normalize(frozenset((i, j) for i, end in enumerate(lam)
                               for j in range(mu[i], end)))


def profile(shape: Shape):
    shape = normalize(shape)
    rows = sorted({i for i, _ in shape})
    left = [min(j for r, j in shape if r == i) for i in rows]
    right = [max(j for r, j in shape if r == i) for i in rows]
    return (tuple(b - a + 1 for a, b in zip(left, right)),
            tuple(right[i + 1] - left[i] for i in range(len(rows) - 1)))


def from_profile(lengths, gaps) -> Shape:
    starts = [0] * len(lengths)
    for i in range(len(lengths) - 2, -1, -1):
        starts[i] = starts[i + 1] + lengths[i + 1] - gaps[i] - 1
    return normalize(frozenset((i, j) for i, length in enumerate(lengths)
                               for j in range(starts[i], starts[i] + length)))


def skew(shape: Shape) -> bool:
    if not shape:
        return False
    rows = sorted({i for i, _ in shape})
    if rows != list(range(rows[0], rows[-1] + 1)):
        return False
    bounds = []
    for i in rows:
        js = {j for r, j in shape if r == i}
        lo, hi = min(js), max(js)
        if js != set(range(lo, hi + 1)):
            return False
        bounds.append((lo, hi))
    return all(a[0] >= b[0] and a[1] >= b[1] for a, b in zip(bounds, bounds[1:]))


def connected(shape: Shape) -> bool:
    if not shape:
        return False
    seen, todo = set(), [next(iter(shape))]
    while todo:
        x = todo.pop()
        if x in seen:
            continue
        seen.add(x)
        todo.extend(add(x, step) for step in ((1, 0), (-1, 0), (0, 1), (0, -1))
                    if add(x, step) in shape and add(x, step) not in seen)
    return seen == shape


def content(x: Cell) -> int:
    return x[1] - x[0]


def span(shape: Shape) -> int:
    return len({content(x) for x in shape})


def southwest(shape: Shape) -> Cell:
    return min(shape, key=content)


def northeast(shape: Shape) -> Cell:
    return max(shape, key=content)


def rotated(shape: Shape) -> Shape:
    return normalize(frozenset((-i, -j) for i, j in shape))


def antitransposed(shape: Shape) -> Shape:
    return normalize(frozenset((-j, -i) for i, j in shape))


@dataclass(frozen=True)
class Mark:
    inner: Shape
    lower: Shape
    vector: Cell
    case: str

    @property
    def period(self):
        return content(self.vector)

    @property
    def width(self):
        return span(self.lower)

    @property
    def score(self):
        return self.width, span(self.inner)


def periodic_contains(x: Cell, finite: Shape, vector: Cell) -> bool:
    if not finite:
        return False
    p = content(vector)
    lo = min(map(content, finite))
    hi = max(map(content, finite))
    first = -((hi - content(x)) // p)
    last = (content(x) - lo) // p
    return any((x[0] - k * vector[0], x[1] - k * vector[1]) in finite
               for k in range(first, last + 1))


def legal(mark: Mark) -> bool:
    E, W, v, case = mark.inner, mark.lower, mark.vector, mark.case
    p, w = mark.period, mark.width
    if not (skew(E) and connected(E) and p >= 2 and 0 <= w < p):
        return False
    sw, ne = southwest(E), northeast(E)
    if not W:
        expected = (ne[0] - sw[0], ne[1] - sw[1] + 1)
        return case == 'a' and v == expected
    upper = shifted(W, v)
    if not (W <= E and upper <= E and sw in W and ne in upper):
        return False
    O = E - W - upper
    if W & upper or not all(skew(x) and connected(x) for x in (W, O, E - W, E - upper)):
        return False
    if span(E) != p + w or E & shifted(E, (-v[0], -v[1])) != W:
        return False
    osw, one = southwest(O), northeast(O)
    lower_case = 'H' if add(osw, (0, -1)) in W else 'V' if add(osw, (1, 0)) in W else '?'
    upper_case = 'H' if add(one, (0, 1)) in upper else 'V' if add(one, (-1, 0)) in upper else '?'
    if {'a': 'HH', 'b': 'VV', 'c': 'HV', 'd': 'VH'}[case] != lower_case + upper_case:
        return False
    # A larger mark must occur as an end intersection at some displacement.
    for target in E:
        dv = (target[0] - sw[0], target[1] - sw[1])
        if content(dv) != p:
            continue
        intersection = E & shifted(E, (-dv[0], -dv[1]))
        if not W <= intersection:
            continue
        extras = sorted(intersection - W)
        for size in range(1, len(extras) + 1):
            for chosen in combinations(extras, size):
                enlarged = W | frozenset(chosen)
                if span(enlarged) == w and skew(enlarged) and ne in shifted(enlarged, dv):
                    return False
    hatO = frozenset(x for x in O if add(x, (1, 1)) in O)
    hatW = frozenset({add(x, (-1, -1)) for x in W
                      if periodic_contains(add(x, (-1, -1)), E, v)} |
                     {x for x in W if periodic_contains(add(x, (1, 1)), E, v)})
    return not any(periodic_contains(add(y, step), hatO, v)
                   for y in hatW for step in ((1, 0), (-1, 0), (0, 1), (0, -1)))


def rotated_mark(mark: Mark) -> Mark:
    E, upper = mark.inner, shifted(mark.lower, mark.vector)
    reflected = frozenset((-i, -j) for i, j in E)
    shift = (-min(i for i, _ in reflected), -min(j for _, j in reflected))
    W = shifted(frozenset((-i, -j) for i, j in upper), shift)
    return Mark(shifted(reflected, shift), W, mark.vector,
                {'a': 'a', 'b': 'b', 'c': 'd', 'd': 'c'}[mark.case])


def ribbon_ranks(shape: Shape, northwest: bool):
    """Peel actual boundary ribbons, rather than using diagonal-rank formulas."""
    remaining, ranks, rank = set(shape), {}, 0
    step = (-1, -1) if northwest else (1, 1)
    while remaining:
        rim = {x for x in remaining if add(x, step) not in remaining}
        assert rim
        for x in rim:
            ranks[x] = rank
        remaining -= rim
        rank += 1
    return ranks


def compose(outer: Shape, mark: Mark, supplemental=True) -> Shape:
    assert outer and skew(outer) and connected(outer)
    assert legal(mark), mark
    E, W, v, case = mark.inner, mark.lower, mark.vector, mark.case
    if case == 'c':
        ranks = ribbon_ranks(outer, True)
    elif case == 'd':
        ranks = ribbon_ranks(outer, False)
    else:
        ranks = {}
    result = set()
    for x in outer:
        i, j = x
        t = j - i
        k = i if case == 'a' else -i if case == 'b' else ranks[x] if case == 'c' else -ranks[x]
        origin = (t * v[0] + k, t * v[1] + k)
        result.update(shifted(E, origin))
        north = add(x, (-1, 0))
        if supplemental and case in 'cd' and north in outer and ranks[north] == ranks[x]:
            sign = 1 if case == 'c' else -1
            result.update(shifted(W, add(origin, add(v, (sign, sign)))))
    answer = normalize(frozenset(result))
    assert skew(answer) and connected(answer), profile(answer)
    assert span(answer) == span(outer) * mark.period + mark.width
    return answer


def board(shape: Shape):
    shape = normalize(shape)
    n = max(i for i, _ in shape) + 1
    lam = [1 + max(j for i, j in shape if i == r) for r in range(n)]
    mu = [min(j for i, j in shape if i == r) for r in range(n)]
    return tuple(tuple(lam[i] - mu[j] - i + j for j in range(n)) for i in range(n))


@lru_cache(None)
def schur(shape: Shape) -> Polynomial:
    """Exact last-row Laplace recursion, retaining every nonzero monomial."""
    matrix = board(shape)
    n = len(matrix)

    @lru_cache(None)
    def minor(columns):
        if not columns:
            return {(): 1}
        i = len(columns) - 1
        answer = defaultdict(int)
        for position, j in enumerate(columns):
            degree = matrix[i][j]
            if degree < 0:
                continue
            sign = -1 if (i + position) % 2 else 1
            for monomial, coefficient in minor(columns[:position] + columns[position + 1:]).items():
                term = tuple(sorted(monomial + ((degree,) if degree else ())))
                answer[term] += sign * coefficient
        return {m: c for m, c in answer.items() if c}

    return minor(tuple(range(n)))


def evaluate(polynomial, values):
    return sum(c * prod(values[k] for k in m) for m, c in polynomial.items())


def determinant_crosscheck(shape):
    P, matrix = schur(shape), board(shape)
    bound = max(max(row) for row in matrix)
    for seed in (2, 5):
        values = {0: 1, **{k: (k * k + seed * k + 1) % 17 - 8 for k in range(1, bound + 1)}}
        M = Matrix([[values[d] if d >= 0 else 0 for d in row] for row in matrix])
        assert evaluate(P, values) == M.det(method='bareiss')


def small_shapes(area):
    """Enumerate all connected diagrams via positive row lengths and overlaps."""
    def compositions(n):
        if n == 0:
            yield ()
        else:
            for first in range(1, n + 1):
                for rest in compositions(n - first):
                    yield (first,) + rest
    for rows in compositions(area):
        for gaps in product(*(range(min(a, b)) for a, b in zip(rows, rows[1:]))):
            yield from_profile(rows, gaps)


def tableau_polynomial(shape, variables=3):
    cells = sorted(shape)
    counts = defaultdict(int)
    for entries in product(range(variables), repeat=len(cells)):
        filling = dict(zip(cells, entries))
        if any(add(x, (0, 1)) in filling and filling[x] > filling[add(x, (0, 1))]
               or add(x, (1, 0)) in filling and filling[x] >= filling[add(x, (1, 0))]
               for x in cells):
            continue
        counts[tuple(entries.count(i) for i in range(variables))] += 1
    return dict(counts)


def check_hook():
    H = partition_shape((2, 1))
    target = {(1, 2): 1, (3,): -1}
    candidates = set(small_shapes(3))
    assert len(candidates) == 4
    assert {G for G in candidates if schur(G) == target} == {H, rotated(H)}
    assert {G for G in candidates if tableau_polynomial(G) == tableau_polynomial(H)} == {H, rotated(H)}
    assert H != rotated(H) and span(H) == 3
    assert not [(p, r, w) for p in range(2, 4) for r in range(2, 4)
                for w in range(p) if p * r + w == span(H)]
    for G in candidates:
        determinant_crosscheck(G)
    # All disconnected size-three products have zero coefficient at h_3.
    disconnected = ({(1, 2): 1}, {(1, 1, 1): 1, (1, 2): -1}, {(1, 1, 1): 1})
    assert all(P != target and P.get((3,), 0) == 0 for P in disconnected)
    print('hook: complete connected class has two chartless rotations; four shapes checked')


def check_line_periods():
    row = partition_shape((7,))
    W = partition_shape((1,))
    m2 = Mark(partition_shape((3,)), W, (0, 2), 'a')
    m3 = Mark(partition_shape((4,)), W, (0, 3), 'a')
    assert legal(m2) and legal(m3)
    assert compose(partition_shape((3,)), m2) == compose(partition_shape((2,)), m3) == row
    assert 3 % 2 != 0 and 2 % 3 != 0
    print('line qualifier: row (7) has legal proper periods 2 and 3')


def check_gauge():
    E = partition_shape((4, 4, 2), (2,))
    # End intersections at the two possible content-four displacements.
    va, vb = (-1, 3), (-2, 2)
    wa = E & shifted(E, (1, -3))
    wb = E & shifted(E, (2, -2))
    a, b = Mark(E, wa, va, 'a'), Mark(E, wb, vb, 'b')
    assert legal(a) and legal(b) and a.width == b.width == 2
    assert add(b.vector, (1, 1)) == a.vector
    contacts = {}
    for mark in (a, b):
        upper = shifted(mark.lower, mark.vector)
        middle = E - mark.lower - upper
        contacts[mark.case] = tuple(sum(any(add(x, step) in middle
                                           for step in ((1, 0), (-1, 0), (0, 1), (0, -1)))
                                       for x in W) for W in (mark.lower, upper))
    assert contacts == {'a': (2, 2), 'b': (2, 2)}, 'both marks must fail Hypothesis V'
    assert not legal(Mark(E, wa, va, 'd')), 'incorrect attachment control did not fire'
    row = partition_shape((2,))
    column = antitransposed(row)
    F = compose(row, a)
    assert F == compose(column, b)
    assert schur(row) == {(2,): 1}
    assert schur(column) == {(1, 1): 1, (2,): -1}
    assert schur(row) != schur(column), 'omitting the outer involution must be detected'
    determinant_crosscheck(F)
    print(f'gauge: E=(4,4,2)/(2), p=4, w=2, parent profile={profile(F)}; h_2 != e_2')
    print(f'  Hypothesis V contacts (lower, upper): {contacts}; displacements differ by (1,1)')


def check_coarse_fiber():
    H, V = partition_shape((2, 1)), partition_shape((4, 1))
    omega = Mark(H, frozenset({(1, 0)}), (-1, 1), 'd')
    mu = Mark(V, frozenset({(1, 0)}), (-1, 3), 'd')
    assert legal(omega) and legal(mu)
    D = compose(H, mu)
    otherD = compose(H, rotated_mark(mu))
    B = compose(V, omega)
    Y, X = compose(D, omega), compose(otherD, omega)
    assert len(X) == len(Y) == 32 and X not in {Y, rotated(Y)}
    assert schur(D) == schur(otherD) and schur(X) == schur(Y)
    # The extreme singleton images determine the displacement of the coarse mark.
    v = (-4, 4)
    eta = Mark(B, B & shifted(B, (4, -4)), v, 'd')
    assert legal(eta) and eta.period == 8 and eta.width == 3
    assert compose(H, eta) == Y
    coarse = {compose(A, mark) for A in (H, rotated(H))
              for mark in (eta, rotated_mark(eta))}
    assert len(coarse) == 4 and Y in coarse and X not in coarse
    Z = compose(rotated(H), eta)
    assert coarse == {Y, rotated(Y), Z, rotated(Z)}
    assert profile(Y)[0] == (2, 2, 2, 3, 2, 2, 2, 4, 3, 2, 2, 3, 2, 1)
    assert profile(Z)[0] == (2, 2, 2, 4, 3, 2, 2, 3, 2, 2, 2, 3, 2, 1)
    assert profile(X)[0] == (3, 2, 2, 2, 3, 2, 2, 4, 3, 2, 2, 2, 2, 1)
    assert omega.score == (1, 3) and eta.score == (3, 11)
    assert span(Y) == 27
    empty_periods = [p for p in range(2, span(Y) // 2 + 1) if span(Y) % p == 0]
    assert empty_periods == [3, 9]
    # Empty composition repeats each boundary word away from the joining steps.
    first_content = min(map(content, Y))
    intervals = [[i for i, j in Y if j - i == first_content + k] for k in range(span(Y))]
    for p in empty_periods:
        words = [[edge(intervals[k - 1]) - edge(intervals[k])
                  for k in range(1, span(Y))] for edge in (min, max)]
        compatible = all(len({word[k - 1] for k in range(a, span(Y), p)}) <= 1
                         for word in words for a in range(1, p))
        assert not compatible, 'an empty period survived the direct boundary test'
    for G in {X, Y, D, otherD, B} | coarse:
        determinant_crosscheck(G)
    # Omitting a supplemental mark changes the parent of a mixed chart.
    assert compose(D, omega, supplemental=False) != Y
    print(f'coarse fiber: {len(coarse)} distinct members, excludes X; '
          f'X,Y area=32, span=27, Schur terms={len(schur(Y))}')
    for name, G in [('D', D), ('B', B), ('Y', Y), ('Z', Z), ('X', X)]:
        print(f'  {name}: profile={profile(G)}')
    print(f'  eta: lower={sorted(eta.lower)}, vector={eta.vector}')
    print('  complete coarse fiber profiles:', sorted(profile(G) for G in coarse))


def main():
    check_hook()
    check_line_periods()
    check_gauge()
    check_coarse_fiber()
    print('ALL PASS')


if __name__ == '__main__':
    main()
