#!/usr/bin/env python3
"""Paper sections `sec:preliminaries`, `sec:profile-transport`,
`sec:saturation-proof`, `sec:thin-and-lowering`, `sec:inflation-proof`
and `sec:examples`; results
`thm:repeated-block-saturation`, `thm:sharp-inflation`,
`thm:two-row-thin-class`, `cor:unbounded-class-splitting`.

Exact checks for repeated-block recovery and asymmetric profile inflation.

All arithmetic is integral.  Polynomials are collected full Jacobi--Trudi
permutation sums, computed by a subset dynamic program, not by the paper's
interval expansion.  Small determinants are independently expanded over all
permutations.  Complete-class searches enumerate every ordering of the fixed
row and gap multisets.  Integer evaluations only reject unequal polynomials;
every accepted candidate is compared symbolically.  Completeness uses the
standard row-count, row-multiset, and adjacent-overlap invariants.

The nonrigid-inner search uses A=(4,7,4,10,7;1,1,1,1) and A dot_2 A:
all 28,350 profiles with the necessary multisets are tested, not merely
assemblies of already classified components.  The size-nine ribbon example
checks its eight constructed images, not all arbitrary fourteen-row mates.
There are no third-party dependencies, floating-point evaluations, or imports
from another paper's verification engine.
"""

from collections import Counter, defaultdict
from functools import lru_cache
from itertools import permutations
from math import factorial


def valid(profile):
    rows, gaps = profile
    return bool(rows) and len(gaps) == len(rows) - 1 and all(
        r > 0 for r in rows
    ) and all(0 <= g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps))


def betas(profile):
    assert valid(profile)
    rows, gaps = profile
    n = len(rows)
    x, y = [0] * n, [0] * n
    x[-1] = rows[-1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    assert all(x[i] > x[i + 1] and y[i] > y[i + 1] for i in range(n - 1))
    return tuple(x), tuple(y)


def add_term(poly, monomial, coefficient):
    if coefficient:
        value = poly.get(monomial, 0) + coefficient
        if value:
            poly[monomial] = value
        else:
            poly.pop(monomial, None)


def determinant_polynomial(x, y):
    n = len(x)
    assert len(y) == n
    board = tuple(tuple(u - v for v in y) for u in x)
    full = (1 << n) - 1

    @lru_cache(None)
    def feasible(mask):
        row = mask.bit_count()
        cols = [j for j in range(n) if not mask & (1 << j)]
        return all(board[row + k][j] >= 0 for k, j in enumerate(cols))

    states = {0: {(): 1}}
    for i in range(n):
        following = {}
        for mask, poly in states.items():
            for j, index in enumerate(board[i]):
                bit = 1 << j
                if mask & bit or index < 0:
                    continue
                new_mask = mask | bit
                if not feasible(new_mask):
                    continue
                sign = -1 if (mask >> (j + 1)).bit_count() % 2 else 1
                target = following.setdefault(new_mask, {})
                for monomial, coefficient in poly.items():
                    new_monomial = tuple(sorted(monomial + (index,))) if index else monomial
                    add_term(target, new_monomial, sign * coefficient)
        states = following
    return states.get(full, {})


@lru_cache(None)
def schur(profile):
    return determinant_polynomial(*betas(profile))


def leibniz(x, y):
    result = {}
    n = len(x)
    for perm in permutations(range(n)):
        indices = tuple(x[i] - y[perm[i]] for i in range(n))
        if min(indices, default=0) < 0:
            continue
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        add_term(result, tuple(sorted(j for j in indices if j)), (-1) ** inversions)
    return result


def bareiss(matrix):
    a = [list(row) for row in matrix]
    n = len(a)
    if not n:
        return 1
    previous, sign = 1, 1
    for k in range(n - 1):
        if not a[k][k]:
            pivot_row = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot_row is None:
                return 0
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def alphabet(n):
    values, state = [1], 8675309
    for _ in range(n):
        state = (1664525 * state + 1013904223) % (1 << 32)
        values.append(1 + state % 1009)
    return values


def evaluate(poly, values):
    total = 0
    for monomial, coefficient in poly.items():
        term = coefficient
        for j in monomial:
            term *= values[j]
        total += term
    return total


def determinant_value(profile, values):
    x, y = betas(profile)
    return bareiss([[values[u - v] if u >= v else 0 for v in y] for u in x])


def multiset_permutations(word):
    counts = Counter(word)
    keys = sorted(counts)
    partial = []

    def visit():
        if len(partial) == len(word):
            yield tuple(partial)
            return
        for key in keys:
            if counts[key]:
                counts[key] -= 1
                partial.append(key)
                yield from visit()
                partial.pop()
                counts[key] += 1

    yield from visit()


def permutation_count(word):
    answer = factorial(len(word))
    for count in Counter(word).values():
        answer //= factorial(count)
    return answer


def rotation(profile):
    return profile[0][::-1], profile[1][::-1]


def inflate(profile, t):
    return tuple(r + t for r in profile[0]), tuple(g + t for g in profile[1])


def block(inner, c, d, m):
    a, b = inner[0], inner[-1]
    middle = inner[1:-1]
    rows = (a,) + middle + ((a + b - d,) + middle) * (m - 1) + (b,)
    return rows, (c,) * (m * (len(inner) - 1))


def parent(inner, c, d, alpha):
    rows, gaps = (), ()
    for i, m in enumerate(alpha):
        br, bg = block(inner, c, d, m)
        rows += br
        gaps += ((d,) if i else ()) + bg
    result = rows, gaps
    assert valid(result)
    return result


def complete_class(profile, expected, description):
    rows, gaps = profile
    polynomial = schur(profile)
    values = alphabet(betas(profile)[0][0])
    target = evaluate(polynomial, values)
    assert determinant_value(profile, values) == target
    gap_orders = tuple(multiset_permutations(gaps))
    raw = feasible = survivors = 0
    actual = set()
    for r in multiset_permutations(rows):
        for g in gap_orders:
            raw += 1
            candidate = r, g
            if not valid(candidate):
                continue
            feasible += 1
            if determinant_value(candidate, values) != target:
                continue
            survivors += 1
            if schur(candidate) == polynomial:
                actual.add(candidate)
    assert raw == permutation_count(rows) * permutation_count(gaps)
    assert actual == set(expected), (description, actual, expected)
    print(f"PASS {description}: {raw} multiset orders, {feasible} valid, "
          f"{survivors} evaluation survivors, {len(actual)} exact mates")
    return raw


def compositions(m):
    if m == 0:
        yield ()
    else:
        for first in range(1, m + 1):
            for tail in compositions(m - first):
                yield (first,) + tail


def suffixes(alpha):
    answer, total = set(), 0
    for part in reversed(alpha[1:]):
        total += part
        answer.add(total)
    return answer


def lowering(poly, t, n):
    result = {}
    for monomial, coefficient in poly.items():
        if len(monomial) == n and all(j >= t for j in monomial):
            add_term(result, tuple(j - t for j in monomial if j > t), coefficient)
    return result


def subthreshold_shift(poly, t, n):
    result = {}
    for monomial, coefficient in poly.items():
        shifted = tuple(sorted((t,) * (n - len(monomial)) + tuple(j + t for j in monomial)))
        add_term(result, shifted, coefficient)
    return result


def fingerprint(poly):
    return tuple(sorted(poly.items()))


def check_engines():
    assert bareiss([[0, 1], [1, 0]]) == -1
    assert bareiss([[1, 2], [2, 4]]) == 0
    for m in range(1, 6):
        for alpha in compositions(m):
            profile = alpha, (0,) * (len(alpha) - 1)
            x, y = betas(profile)
            assert schur(profile) == leibniz(x, y)
            values = alphabet(x[0])
            assert determinant_value(profile, values) == evaluate(schur(profile), values)
    for t in range(4):
        profile = inflate(parent((2, 3), 1, 0, (1, 2)), t)
        assert schur(profile) == leibniz(*betas(profile))
    print("PASS determinant engines: subset sum, direct permutations, and integer Bareiss agree")


def check_saturation():
    for inner, c, d, alpha in [((4, 5), 1, 2, (1, 2)),
                               ((4, 4), 1, 2, (1, 2)),
                               ((2, 3), 0, 1, (1, 2)),
                               ((4, 7, 5), 1, 2, (1, 1)),
                               ((4, 5, 6, 4), 1, 2, (1, 1))]:
        outer = {alpha, alpha[::-1]}
        expected = {parent(inner, c, d, beta) for beta in outer}
        expected |= {rotation(x) for x in expected}
        complete_class(parent(inner, c, d, alpha), expected, f"saturation {inner}, c={c}, d={d}")

    a0, a1 = (4, 7, 4, 10, 7), (4, 10, 7, 4, 7)
    p0, p1 = (a0, (1,) * 4), (a1, (1,) * 4)
    assert p1 not in {p0, rotation(p0)}
    complete_class(p0, {p0, p1, rotation(p0), rotation(p1)}, "nonrigid five-row inner")
    equal0, equal1 = parent(a0, 1, 1, (1, 1)), parent(a1, 1, 1, (1, 1))
    assert schur(equal0) == schur(equal1)
    separated0, separated1 = parent(a0, 1, 2, (1, 1)), parent(a1, 1, 2, (1, 1))
    assert schur(separated0) != schur(separated1)
    raw = complete_class(separated0, {separated0, rotation(separated0)},
                         "two copies of a nonrigid inner")
    assert raw == 28350

    literal = parent(a0, 1, 2, (1, 2))
    swapped = parent(a0, 1, 2, (2, 1))
    assert schur(literal) == schur(swapped)
    for wrong in (a1, a0[::-1], a1[::-1]):
        br, bg = block(a0, 1, 2, 2)
        candidate = wrong + br, (1,) * 4 + (2,) + bg
        assert schur(candidate) != schur(literal)
    print("PASS ambiguous one-copy components: literal order survives; all other inner mates fail")


def check_inflation():
    cases = 0
    for a, b, c in ((2, 3, 1), (3, 4, 1), (3, 5, 2), (4, 6, 1)):
        p, q = a - c, a + b - c
        for m in range(1, 6):
            boundary_seen = set()
            groups = defaultdict(list)
            for alpha in compositions(m):
                profile = parent((a, b), c, 0, alpha)
                ribbon = schur((alpha, (0,) * (len(alpha) - 1)))
                groups[fingerprint(ribbon)].append(profile)
                boundary = inflate(profile, p)
                x, y = betas(boundary)
                suffix = suffixes(alpha)
                assert set(x) & set(y) == {q * s for s in suffix}
                u = tuple(sorted(({q * k for k in range(1, m + 1) if k not in suffix}
                                  | {q * k + p for k in suffix | {m}}), reverse=True))
                v = tuple(sorted(({q * j - a for j in range(1, m + 1)} | {0}), reverse=True))
                assert tuple(z for z in x if z not in set(y)) == u
                assert tuple(z for z in y if z not in set(x)) == v
                polynomial = schur(boundary)
                degree = min(map(len, polynomial))
                assert degree == m + 1
                lowest = {mon: coef for mon, coef in polynomial.items() if len(mon) == degree}
                assert lowest == determinant_polynomial(u, v)
                support = {j for mon in lowest for j in mon}
                assert {k for k in range(1, m) if q * k + p in support} == suffix
                key = fingerprint(lowest)
                assert key not in boundary_seen
                boundary_seen.add(key)
                for t in range(1, p + 2):
                    inflated = schur(inflate(profile, t))
                    assert lowering(inflated, t, len(profile[0])) == schur(profile)
                    if t < p:
                        assert inflated == subthreshold_shift(schur(profile), t, len(profile[0]))
                cases += 1
            for members in groups.values():
                for t in range(p):
                    assert len({fingerprint(schur(inflate(member, t))) for member in members}) == 1
    print(f"PASS boundary beta deletion, positive sign, private support, lowering: {cases} instances")

    for a, b, c in ((2, 3, 1), (3, 4, 1)):
        base = parent((a, b), c, 0, (1, 2))
        other = parent((a, b), c, 0, (2, 1))
        p = a - c
        for t in range(p + 3):
            image = inflate(base, t)
            expected = {image, rotation(image)}
            if t < p:
                expected |= {inflate(other, t), rotation(inflate(other, t))}
            complete_class(image, expected, f"inflation {(a, b, c)}, t={t}")

    cp = determinant_polynomial((13, 12, 9, 4), (10, 6, 2, 0))
    cq = determinant_polynomial((13, 12, 8, 5), (10, 6, 2, 0))
    coefficient = {}
    for mon, value in cp.items():
        if 9 in mon:
            assert mon.count(9) == 1
            add_term(coefficient, tuple(j for j in mon if j != 9), value)
    assert coefficient == {(2, 3, 6): -1, (2, 2, 7): 1}
    assert all(9 not in mon for mon in cq)

    outer = ((1, 2, 1, 3, 2), (1, 3, 2, 1, 2),
             (2, 1, 2, 3, 1), (2, 3, 1, 2, 1))
    oriented = {parent((2, 3), 1, 0, alpha) for alpha in outer}
    images = oriented | {rotation(profile) for profile in oriented}
    assert len(images) == 8
    assert len({fingerprint(schur(profile)) for profile in images}) == 1
    classes = defaultdict(set)
    for profile in images:
        image = inflate(profile, 1)
        classes[fingerprint(schur(image))].add(image)
    assert len(classes) == 4
    assert all(len(group) == 2 and group == {next(iter(group)), rotation(next(iter(group)))}
               for group in classes.values())
    print("PASS eight constructed class members split into four distinct rotation pairs")


def main():
    check_engines()
    check_saturation()
    check_inflation()
    print("ALL PASS")


if __name__ == "__main__":
    main()
