#!/usr/bin/env python3
"""Exact zero-join inventory checks and a bounded search without one-row blocks.

Inventories mean multisets of full block Schur polynomials, not just row words.
The connected profile enumeration is complete at each printed area.  A found
witness is checked again by a separate SymPy determinant.  Negative controls
reject recovering full block functions from top degree when blocks have units.
"""
import argparse
from bisect import insort
from collections import Counter
from functools import lru_cache
from itertools import product
import sys
from random import Random

sys.dont_write_bytecode = True


def valid(p):
    r, g = p
    return bool(r) and len(g) == len(r) - 1 and all(v > 0 for v in r) and all(
        0 <= s < min(r[i], r[i + 1]) for i, s in enumerate(g))


def betas(p):
    r, g = p
    assert valid(p), p
    x, y = [0] * len(r), [0] * len(r)
    x[-1] = r[-1]
    for i in reversed(range(len(r) - 1)):
        y[i] = x[i + 1] - g[i]
        x[i] = y[i] + r[i]
    return tuple(x), tuple(y)


def rotate(p):
    return p[0][::-1], p[1][::-1]


def near(p, q):
    r, g = p
    s, h = q
    return r[:-1] + (r[-1] + s[0],) + s[1:], g + h


def join(p, q):
    return p[0] + q[0], p[1] + (0,) + q[1]


def blocks(p):
    r, g = p
    start = 0
    out = []
    for i, seam in enumerate(g):
        if seam == 0:
            out.append((r[start:i + 1], g[start:i]))
            start = i + 1
    out.append((r[start:], g[start:]))
    return tuple(out)


def total_merge(p):
    parts = blocks(p)
    answer = parts[0]
    for b in parts[1:]:
        answer = near(answer, b)
    return answer


@lru_cache(maxsize=100000)
def polynomial(p):
    x, y = betas(p)
    n = len(x)
    states = {0: {(): 1}}
    for i in reversed(range(n)):
        nxt = {}
        for mask, poly in states.items():
            for j in range(n):
                label = x[i] - y[j]
                if label < 0 or mask & (1 << j):
                    continue
                sign = -1 if (mask & ((1 << j) - 1)).bit_count() % 2 else 1
                target = nxt.setdefault(mask | (1 << j), Counter())
                for mon, coeff in poly.items():
                    new = list(mon)
                    if label:
                        insort(new, label)
                    target[tuple(new)] += sign * coeff
        states = {m: {v: c for v, c in poly.items() if c} for m, poly in nxt.items()}
    return tuple(sorted(states[(1 << n) - 1].items()))


def sympy_polynomial(p):
    import sympy as sp
    # Independent partition reconstruction from literal adjacent-row overlaps.
    r, g = p
    left = [0]
    for i in range(len(g)):
        left.append(left[-1] + g[i] + 1 - r[i + 1])
    low = min(left)
    mu = [a - low for a in left]
    lam = [a + b for a, b in zip(mu, r)]
    largest = lam[0] - mu[-1] + len(r) - 1
    hs = sp.symbols('h1:' + str(largest + 1))
    def h(a):
        return 0 if a < 0 else (1 if a == 0 else hs[a - 1])
    matrix = sp.Matrix(len(r), len(r), lambda i, j: h(lam[i] - mu[j] - i + j))
    expanded = sp.Poly(matrix.det(method='berkowitz'), *hs)
    answer = {}
    for powers, coeff in expanded.terms():
        mon = tuple(j + 1 for j, mult in enumerate(powers) for _ in range(mult))
        answer[mon] = int(coeff)
    return tuple(sorted(answer.items()))


def inventory(p):
    return tuple(sorted(polynomial(b) for b in blocks(p)))


def zero_free(p):
    x, y = betas(p)
    return not set(x) & set(y)


def positive_compositions(total, minimum=1):
    if total == 0:
        yield ()
    else:
        for a in range(minimum, total + 1):
            for rest in positive_compositions(total - a, minimum):
                yield (a,) + rest


def no_singleton_profiles(area):
    # Every row of a block with at least two rows has length at least two.
    for r in positive_compositions(area, 2):
        n = len(r)
        if n < 4:
            continue
        for g in product(*(range(min(r[i], r[i + 1])) for i in range(n - 1))):
            if g[0] == 0 or g[-1] == 0 or 0 not in g:
                continue
            if any(g[i] == g[i + 1] == 0 for i in range(n - 2)):
                continue
            p = (r, g)
            assert all(len(b[0]) >= 2 for b in blocks(p))
            yield p


def multiply(p, q):
    answer = Counter()
    for a, ca in p:
        for b, cb in q:
            answer[tuple(sorted(a + b))] += ca * cb
    return tuple(sorted((m, c) for m, c in answer.items() if c))


def homogeneous(poly, degree):
    return tuple((m, c) for m, c in poly if len(m) == degree)


def controls():
    f = ((4, 5, 4, 3, 2, 1), (2, 3, 2, 1, 0))
    h = ((1, 2, 3, 4, 4, 5), (0, 1, 2, 2, 3))
    assert polynomial(f) == polynomial(h)
    assert polynomial(f) == sympy_polynomial(f) == sympy_polynomial(h)
    assert h not in (f, rotate(f)) and inventory(f) != inventory(h)
    bf, bh = blocks(f)[0], blocks(h)[1]
    assert not zero_free(bf)
    for b in (bf, bh):
        x, y = betas(b)
        assert len(b[0]) == 5 and sum(a < c for a in x for c in y) == 3
    sharp = lambda b: (tuple(2 * r - 1 for r in b[0]), tuple(2 * g - 1 for g in b[1]))
    sf, sh = sharp(bf), sharp(bh)
    assert polynomial(sf) == polynomial(sh)
    assert sh not in (sf, rotate(sf))
    block_product = multiply(polynomial(blocks(f)[0]), polynomial(blocks(f)[1]))
    assert homogeneous(polynomial(f), len(f[0])) != block_product
    altered = ((4, 5, 4, 3, 3, 1), f[1])
    assert polynomial(altered) != polynomial(f)
    print('CONTROL: the supplied 19-cell pair is equal with unequal full block inventories; internal units defeat the unqualified top-degree reading')
    print('SHARP CONTROL: each ordinary five-row block has three negatives and is in the held rigid domain; its sharp images are nonrotation-equal.')

    # The scalar unit-count identity is checked directly on every profile in
    # this complete row-length box, including non-Hessenberg and hidden units.
    total = clean_count = hidden_count = 0
    for n in range(1, 5):
        for r in product(range(1, 5), repeat=n):
            for g in product(*(range(min(r[i], r[i + 1])) for i in range(n - 1))):
                p = (r, g)
                x, y = betas(p)
                common = len(set(x) & set(y))
                poly = polynomial(p)
                assert n - min(len(m) for m, _ in poly) == common
                internal = common - g.count(0)
                assert internal == sum(len(set(betas(b)[0]) & set(betas(b)[1])) for b in blocks(p))
                assert internal >= 0
                if internal == 0:
                    prod = (((), 1),)
                    for b in blocks(p):
                        assert zero_free(b)
                        prod = multiply(prod, polynomial(b))
                    assert homogeneous(poly, n) == prod
                    k = len(blocks(p))
                    low = tuple((m, (-1) ** (k - 1) * c) for m, c in polynomial(total_merge(p)))
                    assert homogeneous(poly, n - k + 1) == low
                    clean_count += 1
                else:
                    hidden_count += 1
                total += 1
    print('UNIT COUNT / EXTREMES:', total, 'profiles;', clean_count, 'zero-free-block cases;', hidden_count, 'hidden-unit controls')


def evaluate(p, values, modulus):
    x, y = betas(p)
    n = len(x)
    a = [[0 if u < v else (1 if u == v else values[u - v]) for v in y] for u in x]
    result = 1
    for i in range(n):
        pivot = next((j for j in range(i, n) if a[j][i] % modulus), None)
        if pivot is None:
            return 0
        if pivot != i:
            a[pivot], a[i] = a[i], a[pivot]
            result = -result
        entry = a[i][i] % modulus
        result = result * entry % modulus
        inverse = pow(entry, modulus - 2, modulus)
        for j in range(i + 1, n):
            scale = a[j][i] * inverse % modulus
            if scale:
                for k in range(i + 1, n):
                    a[j][k] = (a[j][k] - scale * a[i][k]) % modulus
            a[j][i] = 0
    return result % modulus


def fast_search(cap, start):
    modulus = 65521
    rng = Random(7139)
    alphabets = [tuple(rng.randrange(1, modulus) for _ in range(cap + 1)) for _ in range(2)]
    for p in (((3, 3, 3), (1, 1)), ((3, 3, 3), (2, 2)),
              ((1, 2, 2, 3), (0, 0, 1)), ((1, 2, 3, 2), (0, 1, 0))):
        for values in alphabets:
            scalar = 0
            for mon, coeff in polynomial(p):
                term = coeff
                for j in mon:
                    term = term * values[j] % modulus
                scalar = (scalar + term) % modulus
            assert evaluate(p, values, modulus) == scalar
    for area in range(start, cap + 1):
        seen = {}
        count = candidates = exact_pairs = 0
        for p in no_singleton_profiles(area):
            count += 1
            if p > rotate(p):
                continue
            # The proved invariant excludes these sources, and also excludes
            # their equality with a hidden-unit source.  No numerical filter
            # is being used to declare the zero-free-block cases settled.
            x, y = betas(p)
            if len(set(x) & set(y)) == p[1].count(0):
                continue
            key = (tuple(sorted(p[0])), tuple(sorted(p[1])),
                   *(evaluate(p, values, modulus) for values in alphabets))
            bucket = seen.setdefault(key, [])
            for q in bucket:
                candidates += 1
                if polynomial(p) != polynomial(q):
                    continue
                exact_pairs += 1
                if inventory(p) != inventory(q):
                    assert sympy_polynomial(p) == polynomial(p) == sympy_polynomial(q)
                    print('NO-ONE-ROW-BLOCK WITNESS, AREA', area)
                    print('F =', q, 'blocks =', blocks(q))
                    print('H =', p, 'blocks =', blocks(p))
                    print('Every smaller searched area completed; positive equality checked as full integer polynomials.')
                    return q, p
            bucket.append(p)
        print('FILTERED SEARCH completed area', area, ':', count, 'profiles;',
              candidates, 'nonrotation evaluation collisions;', exact_pairs, 'exact equal pairs; no inventory split', flush=True)
    print('No split with both sides lacking one-row blocks in completed areas', start, 'through', cap)
    return None


def search(cap):
    for area in range(8, cap + 1):
        seen = {}
        count = 0
        for p in no_singleton_profiles(area):
            key = polynomial(p)
            inv = inventory(p)
            count += 1
            if key in seen:
                q, other = seen[key]
                if other != inv:
                    assert p not in (q, rotate(q))
                    assert sympy_polynomial(p) == key == sympy_polynomial(q)
                    print('SMALLEST BOTH-SIDES NO-ONE-ROW-BLOCK WITNESS, AREA', area)
                    print('F =', q, 'blocks =', blocks(q))
                    print('H =', p, 'blocks =', blocks(p))
                    print('internal unit counts =', [len(set(betas(z)[0]) & set(betas(z)[1])) - z[1].count(0) for z in (q, p)])
                    print('complete earlier areas and the exhibited equality were checked exactly')
                    return q, p
            else:
                seen[key] = (p, inv)
        print('SEARCH completed area', area, ':', count, 'profiles,', len(seen), 'full polynomial classes; no inventory split', flush=True)
    print('No split with both sides lacking one-row blocks through area', cap)
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cap', type=int, default=16)
    parser.add_argument('--fast', action='store_true', help='use exact finite-field rejection before full polynomial comparison')
    parser.add_argument('--start', type=int, default=8, help='first area for the filtered search')
    args = parser.parse_args()
    controls()
    if args.fast:
        fast_search(args.cap, args.start)
    else:
        search(args.cap)
    print('ALL PASS')


if __name__ == '__main__':
    main()
