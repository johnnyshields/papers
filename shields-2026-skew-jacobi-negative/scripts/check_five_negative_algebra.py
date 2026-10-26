#!/usr/bin/env python3
"""Independent finite checks of the algebraic five-negative interface.

All polynomials retain the independent variable H_0.  Determinants are computed
by full permutation expansion, not by the interval formula under test.  The
window covers both opening types, repeated generator indices, unit openings,
and all three strict/tied second-corner regimes.  It checks the sixteen-plus-
eight expansion, its cofactor marker, finite same-/mixed-opening comparisons,
and the prime obstruction including d <= b.  These checks corroborate the
range-free arguments; no finite box is asserted to prove classification.
"""

from collections import defaultdict
from itertools import permutations, product


def clean(poly):
    return {m: c for m, c in poly.items() if c}


def h(index):
    return {(index,): 1} if index >= 0 else {}


def add(*terms):
    result = defaultdict(int)
    for term in terms:
        for monomial, coefficient in term.items():
            result[monomial] += coefficient
    return clean(result)


def scale(poly, value):
    return {m: c * value for m, c in poly.items() if c * value}


def mul(*terms):
    result = {(): 1}
    for term in terms:
        following = defaultdict(int)
        for a, ca in result.items():
            for b, cb in term.items():
                following[tuple(sorted(a + b))] += ca * cb
        result = clean(following)
    return result


PERMS = {n: tuple((p, (-1) ** sum(p[i] > p[j]
                                for i in range(n) for j in range(i + 1, n)))
                  for p in permutations(range(n))) for n in (4, 5)}


def determinant(mat, forbidden=None):
    answer = defaultdict(int)
    count = 0
    signs = defaultdict(int)
    for perm, sign in PERMS[len(mat)]:
        if forbidden is not None and perm[forbidden[0]] == forbidden[1]:
            continue
        indices = [mat[i][j] for i, j in enumerate(perm)]
        if min(indices) < 0:
            continue
        count += 1
        signs[sign] += 1
        answer[tuple(sorted(indices))] += sign
    return clean(answer), count, dict(signs)


def board(profile):
    rows, gaps = profile
    y = [0] * len(rows)
    for i in range(len(rows) - 2, -1, -1):
        y[i] = y[i + 1] + rows[i + 1] - gaps[i]
    x = [y[i] + rows[i] for i in range(len(rows))]
    return tuple(tuple(a - b for b in y) for a in x)


def interval(profile):
    rows, gaps = profile
    n = len(rows)
    answer = defaultdict(int)
    for mask in range(1 << (n - 1)):
        indices = [gaps[i] for i in range(n - 1) if mask & (1 << i)]
        current = rows[0]
        for i in range(n - 1):
            if mask & (1 << i):
                current += rows[i + 1] - gaps[i]
            else:
                indices.append(current)
                current = rows[i + 1]
        indices.append(current)
        answer[tuple(sorted(indices))] += (-1) ** mask.bit_count()
    return clean(answer)


def coefficient(poly, index, exponent=1):
    result = {}
    for monomial, value in poly.items():
        if monomial.count(index) == exponent:
            result[tuple(j for j in monomial if j != index)] = value
    return result


def without(poly, index):
    return {m: c for m, c in poly.items() if index not in m}


def top(poly):
    return max(j for m in poly for j in m)


def tpoly(z, b, p):
    return add(mul(h(b), h(z)), scale(mul(h(p), h(z + b - p)), -1))


def fpoly(s, z, tau):
    return add(mul(h(s), h(z)), scale(mul(h(tau), h(z + s - tau)), -1))


def rotate(profile):
    return profile[0][::-1], profile[1][::-1]


def from_lists(x, y):
    return tuple(a - b for a, b in zip(x, y)), tuple(x[i + 1] - y[i] for i in range(4))


def family_members(b, g, q):
    x = tuple(b + k * g for k in range(4, -1, -1))
    result = []
    for y, yp in (((3*g, g+q, g, q, 0), (2*g+q, 2*g, g, q, 0)),
                  ((3*g+q, g+q, g, q, 0), (2*g+q, 2*g, g+q, q, 0))):
        first, second = from_lists(x, y), from_lists(x, yp)
        result.append({first, rotate(first), second, rotate(second)})
    return result


def main():
    fibers = defaultdict(list)
    regimes = defaultdict(int)
    count = 0
    for tau in range(3):
        for u, v in product(range(tau + 1, tau + 4), repeat=2):
            core = fpoly(u, v, tau)
            L = u + v - tau
            for a, p in product(range(3), repeat=2):
                for dx, dy, dc, db in product(range(1, 3), repeat=4):
                    b = p + db
                    for kind in ('M', 'E'):
                        if kind == 'M':
                            x, y, c = a + dx, a + u + dy, v + p + dc
                            profile = (x, y, L, c, b), (a, u, v, p)
                            opened = (3, 1)
                            c25 = scale(mul(h(x), h(p), core), -1)
                            delta = x - a
                        else:
                            x, y, c = u + dx, a + v + dy, a + p + dc
                            profile = (x, L, y, c, b), (u, v, a, p)
                            opened = (2, 0)
                            c25 = scale(mul(h(a), h(p), fpoly(v, x, tau)), -1)
                            delta = x - u
                        mat = board(profile)
                        assert sum(j < 0 for row in mat for j in row) == 5
                        assert mat[opened[0]][opened[1]] == tau
                        full, total, signs = determinant(mat)
                        assert total == 24 and signs == {1: 12, -1: 12}, (profile, signs)
                        closed, count_closed, _ = determinant(mat, opened)
                        assert count_closed == 16 and closed == interval(profile)
                        minor = tuple(tuple(index for j, index in enumerate(row) if j != opened[1])
                                      for i, row in enumerate(mat) if i != opened[0])
                        extra, count_extra, _ = determinant(minor)
                        assert count_extra == 8
                        assert full == add(closed, mul(h(tau), extra)), profile
                        m = mat[0][-1]
                        c15 = mul(h(a), h(p), core)
                        c14 = scale(mul(h(a), h(b), core), -1)
                        assert coefficient(full, m) == c15
                        remainder = without(full, m)
                        q = b - p
                        N = m - min(q, delta)
                        assert top(remainder) == N
                        expected = c14 if q < delta else c25 if delta < q else add(c14, c25)
                        assert coefficient(remainder, N) == expected, (kind, profile)
                        assert all(mon.count(N) <= 1 for mon in remainder)
                        regime = 'bottom' if q < delta else 'top' if delta < q else 'tie'
                        regimes[kind, regime] += 1
                        fibers[tuple(sorted(full.items()))].append((kind, profile, tau, u, v))
                        count += 1

    mixed = 0
    for entries in fibers.values():
        middle = {min(p, rotate(p)) for kind, p, *_ in entries if kind == 'M'}
        end = {p for kind, p, *_ in entries if kind == 'E'}
        assert len(middle) <= 1, ('nonrotation M/M equality', entries)
        assert len(end) <= 1, ('nonidentity E/E equality', entries)
        if middle and end:
            mixed += 1
            _, _, tau, u, v = entries[0]
            b, g, q = min(u, v), max(u, v) - tau, min(u, v) - tau
            assert 1 <= q <= b < g, entries
            members = {p for _, p, *_ in entries}
            assert any(members <= family for family in family_members(b, g, q)), entries
    assert mixed > 0
    assert len(regimes) == 6

    prime_count = 0
    low_d = 0
    for tau in range(3):
        for v in range(tau + 1, tau + 4):
            for u in range(v + 1, v + 4):
                L = u + v - tau
                for p in range(7):
                    for b in range(p + 1, p + 9):
                        for c in range(v + p + 1, v + p + 5):
                            d = c + u - v
                            defect = add(mul(h(u), tpoly(c, b, p)),
                                         scale(mul(h(v), tpoly(d, b, p)), -1))
                            # Substitute H_L=H_u H_v/H_tau and clear denominators.
                            # Since the primitive divisor is linear in H_L, a zero
                            # remainder is equivalent to divisibility by B.
                            power = max((m.count(L) for m in defect), default=0)
                            remainder = defaultdict(int)
                            for monomial, value in defect.items():
                                exponent = monomial.count(L)
                                new = tuple(j for j in monomial if j != L)
                                new += (u, v) * exponent + (tau,) * (power - exponent)
                                remainder[tuple(sorted(new))] += value
                            assert clean(remainder), (u, v, tau, b, p, c, d)
                            prime_count += 1
                            low_d += d <= b
    assert low_d > 0
    print('five-negative boards:', count, 'mixed fibers:', mixed, 'marker regimes:', dict(regimes))
    print('prime-obstruction instances:', prime_count, 'including d <= b:', low_d)
    print('ALL PASS')


if __name__ == '__main__':
    main()
