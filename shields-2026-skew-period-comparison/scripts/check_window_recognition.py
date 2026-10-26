#!/usr/bin/env python3
"""Paper sections `sec:recovered-entry` (Discrete-source entry and high identities)
and `sec:recovered-recognition` (Complete two-window ribbon recognition); targets
`prop:exact-high-identity`, `lem:oo-window-construction`, `eq:oo-window-sum`.

Exact finite checks for the complete window theorem and actual singleton seams.

Coarsening sums are compared with permutation determinants.  A separate raw
Jacobi--Trudi sweep differentiates genuine discrete-interior diagrams, including
both derivatives of a two-section product.  These bounded checks are not proofs.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import prod


def clean(p):
    return {m: c for m, c in p.items() if c}


def add(*terms):
    out = defaultdict(F)
    for p in terms:
        for m, c in p.items():
            out[m] += c
    return clean(out)


def scale(p, c):
    return clean({m: c * v for m, v in p.items()})


def mul(p, q):
    out = defaultdict(F)
    for m, c in p.items():
        for n, d in q.items():
            out[tuple(sorted(m + n))] += c * d
    return clean(out)


def h(i):
    return {} if i < 0 else {(): F(1)} if i == 0 else {(i,): F(1)}


def subsets(values):
    values = sorted(values)
    for size in range(len(values) + 1):
        yield from combinations(values, size)


def ribbon(n, cuts):
    if n == 0:
        return {(): F(1)}
    out = defaultdict(F)
    for chosen in subsets(cuts):
        ends = (0,) + chosen + (n,)
        mon = tuple(sorted(b - a for a, b in zip(ends, ends[1:])))
        out[mon] += (-1) ** len(chosen)
    return clean(out)


def jt(rows, gaps):
    size = len(rows)
    y = [0] * size
    x = [0] * size
    x[-1] = rows[-1]
    for i in range(size - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    out = {}
    for perm in permutations(range(size)):
        inversions = sum(perm[i] > perm[j] for i in range(size) for j in range(i + 1, size))
        term = {(): F((-1) ** inversions)}
        for i, j in enumerate(perm):
            term = mul(term, h(x[i] - y[j]))
        out = add(out, term)
    return out


def window(n, A, C, U, V, Q, theta):
    out = {}
    left = {0} | set(A) | ({n} if U else set())
    right = {n} | set(C) | ({0} if V else set())
    for l, z in product(sorted(left), sorted(right)):
        if l > z:
            continue
        term = mul(h(z - l), mul(ribbon(l, {x for x in A if x < l}), ribbon(n - z, {x - z for x in C if x > z})))
        out = add(out, scale(term, (-1) ** ((l > 0) + (z < n)) * (Q * (z - l) + theta)))
    return out


def normalized(p, n):
    top = p.get((n,), F(0))
    assert top > 0
    return scale(p, 1 / top), top


def integral(p):
    return all(c.denominator == 1 for c in p.values())


def derivative(p, shift, Q, theta):
    out = defaultdict(F)
    for mon, coef in p.items():
        for i, val in enumerate(mon):
            if val < shift:
                continue
            reduced = val - shift
            rest = mon[:i] + mon[i + 1:] + ((reduced,) if reduced else ())
            out[tuple(sorted(rest))] += coef * (Q * reduced + theta)
    return clean(out)


def run():
    ntests = [0, 0, 0]
    witnesses = [0, 0, 0]
    phases = (F(1, 3), F(1, 2), F(2, 3))
    for n in range(2, 7):
        cuts = list(map(set, subsets(range(1, n))))
        # An independent permutation-determinant route checks every output.
        for A in cuts:
            ends = [0] + sorted(A) + [n]
            rows = [b - a for a, b in zip(ends, ends[1:])]
            assert ribbon(n, A) == scale(jt(rows, [0] * (len(rows) - 1)), (-1) ** len(A))
        for A, C, U, V, theta in product(cuts, cuts, (0, 1), (0, 1), phases):
            p, top = normalized(window(n, A, C, U, V, 1, theta), n)
            assert top == n + (1 - U - V) * theta
            assert integral(p) == (A == C), (n, A, C, U, V, theta)
            if integral(p):
                assert p == ribbon(n, A)
                witnesses[0] += 1
            ntests[0] += 1
        for m in range(1, n // 2 + 1):
            a = n - m
            if a <= m:
                continue
            for A, C, theta in product(cuts, cuts, phases):
                R = A & set(range(1, m))
                end = {a + x for x in R}
                if a in A or (A & set(range(a + 1, n))) != end or (C & set(range(a + 1, n))) != end:
                    continue
                e0 = int(a in C)
                for V in (0, 1):
                    base = window(n, A, C, 0, V, 1, theta)
                    p, top = normalized(add(base, scale(ribbon(n, A), -(m + (1 - e0) * theta))), n)
                    target = A == C - {a}
                    assert top == a + (e0 - V) * theta
                    assert integral(p) == target, (1, n, m, A, C, V, theta)
                    if target:
                        assert p == ribbon(n, C)
                        witnesses[1] += 1
                    ntests[1] += 1
                if m in C or C & set(range(1, m)) != R:
                    continue
                u, v = int(m in A), int(a in C)
                base = window(n, A, C, 0, 0, 1, theta)
                p, top = normalized(add(base, scale(ribbon(n, A), -(m + (1 - v) * theta)), scale(ribbon(n, C), -(m + (1 - u) * theta))), n)
                target = A - {m} == C - {a}
                assert top == a - m + (u + v - 1) * theta
                assert integral(p) == target, (2, n, m, A, C, theta)
                if target:
                    assert p == ribbon(n, A | C)
                    witnesses[2] += 1
                ntests[2] += 1
    # Actual original diagrams: their positive seams are isolated cells.
    actual = k2 = signed = 0
    for length in range(2, 5):
        for rows in product(range(1, 6), repeat=length):
            for gaps in product((0, 1), repeat=length - 1):
                if not any(gaps) or any(g >= min(rows[i], rows[i + 1]) for i, g in enumerate(gaps)):
                    continue
                if any(gaps[i - 1] == gaps[i] == 1 and rows[i] < 3 for i in range(1, length - 1)):
                    continue
                sections = [rows[0]]
                for i, gap in enumerate(gaps):
                    if gap:
                        sections.append(rows[i + 1])
                    else:
                        sections[-1] += rows[i + 1]
                for b in range(2, 5):
                    if any(s < b + 1 or (s - 1) % b for s in sections):
                        continue
                    K = sum((s - 1) // b for s in sections)
                    t = sum(gaps)
                    raw = jt(rows, gaps)
                    for theta in (F(-1, 2), F(0), F(1, 2)):
                        differentiated = derivative(raw, b * (K - 1), 1, theta)
                        assert differentiated
                        quot = {}
                        for mon, coef in differentiated.items():
                            assert mon.count(1) >= t
                            remaining = list(mon)
                            for _ in range(t):
                                remaining.remove(1)
                            quot[tuple(remaining)] = coef * (-1) ** (length - 1)
                        ray, top = normalized(quot, b + 1)
                        assert all(sum(mon) == b + 1 for mon in ray)
                        if theta > 0:
                            outputs = [ribbon(b + 1, c) for c in subsets(range(1, b + 1))]
                            assert integral(ray) == (ray in outputs)
                            actual += 1
                            k2 += K == 2
                        else:
                            signed += 1
    assert min(ntests) > 0 and min(witnesses) > 0 and actual and k2 and signed
    print('PASS window cases by minimal ends:', ntests, '; integral outputs:', witnesses)
    print('PASS raw JT positive-phase cases:', actual, '; K=2:', k2, '; nonpositive phase identities:', signed)


if __name__ == '__main__':
    run()
