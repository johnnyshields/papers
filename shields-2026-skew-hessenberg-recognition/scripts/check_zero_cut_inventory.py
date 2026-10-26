"""Verify zero-cut expansion, internal-unit counts, and full block readings.

Complete integer polynomials are computed by a subset determinant and checked
against permutation expansion using independently reconstructed partitions.
The internal-unit example rejects an unqualified full-block reading from the
highest ordinary component.  No bounded search supplies a universal proof.
"""
from bisect import insort
from collections import Counter
from functools import lru_cache
from itertools import permutations, product


def valid(profile):
    rows, gaps = profile
    return bool(rows) and len(gaps) == len(rows) - 1 and all(r > 0 for r in rows) and all(
        0 <= g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps))


def betas(profile):
    rows, gaps = profile
    assert valid(profile), profile
    x, y = [0] * len(rows), [0] * len(rows)
    x[-1] = rows[-1]
    for i in reversed(range(len(gaps))):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return tuple(x), tuple(y)


def rotate(profile):
    return profile[0][::-1], profile[1][::-1]


def near(left, right):
    rows, gaps = left
    other_rows, other_gaps = right
    return (rows[:-1] + (rows[-1] + other_rows[0],) + other_rows[1:],
            gaps + other_gaps)


def join(left, right):
    return left[0] + right[0], left[1] + (0,) + right[1]


def blocks(profile):
    rows, gaps = profile
    answer, start = [], 0
    for i, gap in enumerate(gaps):
        if gap == 0:
            answer.append((rows[start:i + 1], gaps[start:i]))
            start = i + 1
    answer.append((rows[start:], gaps[start:]))
    return tuple(answer)


def total_merge(profile):
    pieces = blocks(profile)
    answer = pieces[0]
    for piece in pieces[1:]:
        answer = near(answer, piece)
    return answer


def zero_free(profile):
    x, y = betas(profile)
    return not set(x) & set(y)


@lru_cache(maxsize=20000)
def polynomial(profile):
    x, y = betas(profile)
    n = len(x)
    states = {0: {(): 1}}
    for i in reversed(range(n)):
        next_states = {}
        for mask, poly in states.items():
            for j, column in enumerate(y):
                label = x[i] - column
                if label < 0 or mask & (1 << j):
                    continue
                sign = -1 if (mask & ((1 << j) - 1)).bit_count() % 2 else 1
                target = next_states.setdefault(mask | (1 << j), Counter())
                for monomial, coefficient in poly.items():
                    new = list(monomial)
                    if label:
                        insort(new, label)
                    target[tuple(new)] += sign * coefficient
        states = {mask: {mon: c for mon, c in poly.items() if c}
                  for mask, poly in next_states.items()}
    return tuple(sorted(states[(1 << n) - 1].items()))


def permutation_polynomial(profile):
    rows, gaps = profile
    left = [0]
    for i, gap in enumerate(gaps):
        left.append(left[-1] + gap + 1 - rows[i + 1])
    offset = min(left)
    mu = tuple(a - offset for a in left)
    lam = tuple(a + b for a, b in zip(mu, rows))
    n = len(rows)
    answer = Counter()
    for perm in permutations(range(n)):
        labels = tuple(lam[i] - mu[j] - i + j for i, j in enumerate(perm))
        if min(labels) < 0:
            continue
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        answer[tuple(sorted(a for a in labels if a))] += sign
    return tuple(sorted((mon, c) for mon, c in answer.items() if c))


def homogeneous(poly, degree):
    return tuple((mon, c) for mon, c in poly if len(mon) == degree)


def multiply(left, right):
    answer = Counter()
    for a, ca in left:
        for b, cb in right:
            answer[tuple(sorted(a + b))] += ca * cb
    return tuple(sorted((mon, c) for mon, c in answer.items() if c))


def block_expansion(pieces):
    answer = Counter()
    for mask in range(1 << (len(pieces) - 1)):
        merged, groups = pieces[0], []
        for i, piece in enumerate(pieces[1:]):
            if mask & (1 << i):
                merged = near(merged, piece)
            else:
                groups.append(merged)
                merged = piece
        groups.append(merged)
        term = (((), 1),)
        for group in groups:
            term = multiply(term, polynomial(group))
        sign = (-1) ** mask.bit_count()
        for mon, coefficient in term:
            answer[mon] += sign * coefficient
    return tuple(sorted((mon, c) for mon, c in answer.items() if c))


def evaluate(profile, values, modulus):
    x, y = betas(profile)
    n = len(x)
    matrix = [[0 if a < b else (1 if a == b else values[a - b]) for b in y] for a in x]
    answer = 1
    for i in range(n):
        pivot = next((j for j in range(i, n) if matrix[j][i] % modulus), None)
        if pivot is None:
            return 0
        if pivot != i:
            matrix[pivot], matrix[i] = matrix[i], matrix[pivot]
            answer = -answer
        value = matrix[i][i] % modulus
        answer = answer * value % modulus
        inverse = pow(value, modulus - 2, modulus)
        for j in range(i + 1, n):
            scale = matrix[j][i] * inverse % modulus
            if scale:
                for k in range(i + 1, n):
                    matrix[j][k] = (matrix[j][k] - scale * matrix[i][k]) % modulus
            matrix[j][i] = 0
    return answer % modulus


def main():
    count = free = internal = 0
    for n in range(1, 5):
        for rows in product(range(1, 5), repeat=n):
            for gaps in product(*(range(min(rows[i], rows[i + 1])) for i in range(n - 1))):
                profile = rows, gaps
                x, y = betas(profile)
                poly = polynomial(profile)
                assert permutation_polynomial(profile) == poly
                assert block_expansion(blocks(profile)) == poly
                common = len(set(x) & set(y))
                assert n - min(len(mon) for mon, _ in poly) == common
                iota = common - gaps.count(0)
                assert iota == sum(len(set(betas(b)[0]) & set(betas(b)[1])) for b in blocks(profile))
                if iota == 0:
                    top = (((), 1),)
                    for b in blocks(profile):
                        assert zero_free(b)
                        top = multiply(top, polynomial(b))
                    assert homogeneous(poly, n) == top
                    k = len(blocks(profile))
                    assert homogeneous(poly, n - k + 1) == tuple(
                        (mon, (-1) ** (k - 1) * c) for mon, c in polynomial(total_merge(profile)))
                    free += 1
                else:
                    internal += 1
                count += 1
    f = ((4, 5, 4, 3, 2, 1), (2, 3, 2, 1, 0))
    h = ((1, 2, 3, 4, 4, 5), (0, 1, 2, 2, 3))
    assert polynomial(f) == polynomial(h) == permutation_polynomial(f) == permutation_polynomial(h)
    assert h not in (f, rotate(f))
    q, r = blocks(f)[0], blocks(h)[1]
    assert not zero_free(q) and not zero_free(r)
    assert dict(polynomial(q)).get((4, 7, 7), 0) == 1
    assert dict(polynomial(r)).get((4, 7, 7), 0) == 0
    assert homogeneous(polynomial(f), len(f[0])) != multiply(polynomial(q), polynomial(blocks(f)[1]))
    for p in (f, h):
        x, y = betas(p)
        assert len(set(x) & set(y)) - p[1].count(0) == 2
    changed = ((5,) + f[0][1:], f[1])
    assert polynomial(changed) != polynomial(h)
    print(f'PASS: {count} full determinant and block-expansion identities; '
          f'{free} zero-free-block extreme readings; {internal} internal-unit cases.')
    print('PASS: the 19-cell equality has different full block functions, with coefficients 1 and 0 at h4*h7^2.')
    print('CONTROL: internal units reject the unqualified top-degree product; a row perturbation rejects equality.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
