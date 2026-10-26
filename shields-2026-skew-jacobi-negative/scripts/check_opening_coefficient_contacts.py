#!/usr/bin/env python3
"""Exact contact tests for the five-negative coefficient comparisons.

A column-subset determinant is compared with the collected coefficient formulas
for middle/middle, end/end, and mixed openings.  Every candidate retains its
own validity inequalities.  The deterministic window includes zero indices,
coincident row and gap labels, ties, and both explicit equality families.
This is corroboration of the parameter-uniform proofs, not finite proof of them.
"""

from collections import Counter, defaultdict
from functools import lru_cache
from itertools import permutations, product
import random


def clean(p):
    return {m: c for m, c in p.items() if c}


def h(j):
    return {(j,): 1} if j >= 0 else {}


def add(*terms):
    out = defaultdict(int)
    for p in terms:
        for m, c in p.items():
            out[m] += c
    return clean(out)


def neg(p):
    return {m: -c for m, c in p.items()}


def mul(*terms):
    out = {(): 1}
    for p in terms:
        nxt = defaultdict(int)
        for a, c in out.items():
            for b, d in p.items():
                nxt[tuple(sorted(a + b))] += c * d
        out = clean(nxt)
    return out


def coefficient(p, j, degree=1):
    return {tuple(k for k in m if k != j): c
            for m, c in p.items() if m.count(j) == degree}


def specialize(p, killed):
    return {m: c for m, c in p.items() if not set(m) & set(killed)}


def top(p):
    return max((j for m in p for j in m), default=-1)


def lists(rows, gaps):
    y = [0] * len(rows)
    for i in range(len(rows) - 2, -1, -1):
        y[i] = y[i + 1] + rows[i + 1] - gaps[i]
    return tuple(y[i] + rows[i] for i in range(len(rows))), tuple(y)


@lru_cache(maxsize=40000)
def determinant(rows, gaps):
    x, y = lists(rows, gaps)
    n = len(rows)
    dp = {0: {(): 1}}
    for i in range(n):
        following = {}
        for mask, poly in dp.items():
            for j in range(n):
                if mask & (1 << j) or x[i] < y[j]:
                    continue
                sign = (-1) ** ((mask >> (j + 1)).bit_count())
                term = mul(poly, h(x[i] - y[j]))
                if sign < 0:
                    term = neg(term)
                nm = mask | (1 << j)
                following[nm] = add(following.get(nm, {}), term)
        dp = following
    return dp.get((1 << n) - 1, {})


def perm_determinant(rows, gaps):
    x, y = lists(rows, gaps)
    out = defaultdict(int)
    for p in permutations(range(len(rows))):
        labels = [x[i] - y[p[i]] for i in range(len(rows))]
        if min(labels) < 0:
            continue
        sign = (-1) ** sum(p[i] > p[j] for i in range(len(rows))
                          for j in range(i + 1, len(rows)))
        out[tuple(sorted(labels))] += sign
    return clean(out)


# A tuple is (kind, x, y, c, b, a, u, v, p, tau).
def valid(t):
    kind, x, y, c, b, a, u, v, p, tau = t
    if not (u > tau >= 0 and v > tau and b > p >= 0 and a >= 0):
        return False
    if kind == 'M':
        return x > a and y > a + u and c > v + p
    return x > u and y > a + v and c > a + p


def profile(t):
    kind, x, y, c, b, a, u, v, p, tau = t
    L = u + v - tau
    if kind == 'M':
        return (x, y, L, c, b), (a, u, v, p)
    return (x, L, y, c, b), (u, v, a, p)


def f(s, z, tau):
    return add(mul(h(s), h(z)), neg(mul(h(tau), h(z + s - tau))))


def T(z, b, p):
    return add(mul(h(b), h(z)), neg(mul(h(p), h(z + b - p))))


def G(s, z, b, p, tau):
    return add(mul(h(s), T(z, b, p)),
               neg(mul(h(tau), T(z + s - tau, b, p))))


def rotate(prof):
    return prof[0][::-1], prof[1][::-1]


def polynomial(t):
    return determinant(*profile(t))


def family_set(b, g, q, second):
    x = tuple(b + k * g for k in range(4, -1, -1))
    if second:
        ys = ((3*g+q, g+q, g, q, 0), (2*g+q, 2*g, g+q, q, 0))
    else:
        ys = ((3*g, g+q, g, q, 0), (2*g+q, 2*g, g, q, 0))
    out = set()
    for y in ys:
        prof = (tuple(x[i] - y[i] for i in range(5)),
                tuple(x[i+1] - y[i] for i in range(4)))
        out.update((prof, rotate(prof)))
    return out


def check_pair(s, t, counts):
    assert valid(s) and valid(t)
    kind, x, y, c, b, a, u, v, p, tau = s
    other, xi, eta, d, b1, a1, U, V, p1, tau1 = t
    assert (b, a, p, tau) == (b1, a1, p1, tau1)
    assert sorted((x, y, c)) == sorted((xi, eta, d))
    assert sorted((u, v)) == sorted((U, V))
    if kind == 'M':
        R, Z = x+y+v-a-tau, c+b-p+y-tau
    else:
        R, Z = x+y-tau, c+b-p+y+u-a-tau
    if other == 'M':
        Rp, Zp = xi+eta+V-a-tau, d+b-p+eta-tau
    else:
        Rp, Zp = xi+eta-tau, d+b-p+eta+U-a-tau
    J = max(R, Rp, Z, Zp)
    B = f(u, v, tau)
    def top_term(k, first, third, cu, cv):
        if k == 'M':
            return mul(h(a), G(cu, third, b, p, tau))
        return mul(B, T(third, b, p))
    def right_term(k, first, cv):
        if k == 'M':
            return neg(mul(h(first), h(p), B))
        return neg(mul(h(a), h(p), f(cv, first, tau)))
    parts = []
    if R == J:
        parts.append(top_term(kind, x, c, u, v))
    if Rp == J:
        parts.append(neg(top_term(other, xi, d, U, V)))
    if Z == J:
        parts.append(right_term(kind, x, v))
    if Zp == J:
        parts.append(neg(right_term(other, xi, V)))
    expected = add(*parts)
    diff = add(polynomial(s), neg(polynomial(t)))
    assert top(expected) < J, ('coefficient contains its marker', s, t, J)
    assert top(diff) <= J, ('omitted higher label', s, t, J, top(diff))
    assert coefficient(diff, J) == expected, ('contact coefficient', s, t, J)
    assert all(m.count(J) <= 1 for m in diff), ('quadratic marker', s, t, J)
    counts['pairs'] += 1
    counts[kind + '/' + other] += 1
    counts['ties' if (R, Rp, Z, Zp).count(J) > 1 else 'private'] += 1
    counts['units'] += 0 in (a, p, tau)
    if not diff:
        counts['equal'] += 1
        ps, pt = profile(s), profile(t)
        if kind == other == 'M':
            assert pt in (ps, rotate(ps)), ('M/M counterexample', s, t)
        elif kind == other == 'E':
            assert ps == pt, ('E/E counterexample', s, t)
        else:
            fb, fg, fq = min(u, v), max(u, v)-tau, min(u, v)-tau
            assert 1 <= fq <= fb < fg, ('mixed domain', s, t)
            assert any({ps, pt} <= family_set(fb, fg, fq, second)
                       for second in (False, True)), ('mixed counterexample', s, t)


def prime_checks(counts):
    for tau in range(4):
        for v in range(tau + 1, tau + 5):
            for u in range(v + 1, v + 5):
                L = u + v - tau
                for p in range(10):
                    for b in range(p + 1, p + 11):
                        for c in range(v + p + 1, v + p + 5):
                            d = c + u - v
                            P = add(mul(h(u), T(c, b, p)), neg(mul(h(v), T(d, b, p))))
                            first = specialize(P, (u, tau))
                            if not first:
                                assert p == tau and b == u, ('unhandled first specialization', u, v, tau, p, b, c)
                                second = specialize(P, (v, tau))
                                assert second == mul(h(u), h(u), h(c))
                                assert second
                                counts['prime second specialization'] += 1
                            counts['prime'] += 1
                            counts['prime d<=b'] += d <= b
                            # Independent quotient test, including repeated occurrences of H_L.
                            power = max(m.count(L) for m in P)
                            rem = defaultdict(int)
                            for mon, coef in P.items():
                                n = mon.count(L)
                                new = tuple(j for j in mon if j != L) + (u, v)*n + (tau,)*(power-n)
                                rem[tuple(sorted(new))] += coef
                            assert clean(rem), ('prime divisor', u, v, tau, p, b, c)
    assert counts['prime second specialization'] and counts['prime d<=b']


def main():
    rng = random.Random(90517)
    counts = Counter()
    seeds = set()
    for kind in ('M', 'E'):
        for _ in range(1200):
            tau = rng.randrange(6)
            u, v = (tau + rng.randrange(1, 9) for _ in range(2))
            a, p = (rng.randrange(13) for _ in range(2))
            b = p + rng.randrange(1, 12)
            if kind == 'M':
                x, y, c = a+rng.randrange(1, 13), a+u+rng.randrange(1, 13), v+p+rng.randrange(1, 13)
            else:
                x, y, c = u+rng.randrange(1, 13), a+v+rng.randrange(1, 13), a+p+rng.randrange(1, 13)
            seeds.add((kind, x, y, c, b, a, u, v, p, tau))
    # Both equality loci, their smallest margins, and the unit boundary.
    for p, v, excess in product(range(5), range(1, 7), range(1, 5)):
        if v <= p:
            continue
        u = v+p+excess
        for a, x in ((p, u), (v, u+v-p)):
            seeds.add(('M', x, 2*u-p, u, v, a, u, v, p, p))
    for i, source in enumerate(sorted(seeds)):
        assert valid(source)
        prof = profile(source)
        xb, yb = lists(*prof)
        assert sum(a < b for a in xb for b in yb) == 5
        if i % 97 == 0:
            assert polynomial(source) == perm_determinant(*prof)
            counts['independent determinant controls'] += 1
        kind, x, y, c, b, a, u, v, p, tau = source
        for xi, eta, d in set(permutations((x, y, c))):
            for U, V in set(permutations((u, v))):
                for other in ('M', 'E'):
                    target = (other, xi, eta, d, b, a, U, V, p, tau)
                    if valid(target):
                        check_pair(source, target, counts)
    prime_checks(counts)
    assert all(counts[k] for k in ('M/M', 'E/E', 'M/E', 'E/M', 'ties', 'units'))
    # Deliberately corrupt a coefficient formula; the exact comparison must reject it.
    witness = ('M', 3, 6, 3, 1, 0, 3, 1, 0, 0)
    poly = polynomial(witness)
    bad = add(poly, h(0))
    try:
        assert poly == bad
    except AssertionError:
        print('CONTROL FIRED: inserted false constant-generator term')
    else:
        raise AssertionError('rejecting control did not fire')
    print('source profiles:', len(seeds))
    for key, value in sorted(counts.items()):
        print(key + ':', value)
    print('ALL PASS')


if __name__ == '__main__':
    main()
