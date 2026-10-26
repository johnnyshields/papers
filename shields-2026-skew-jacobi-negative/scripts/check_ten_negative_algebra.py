"""Independent exact determinant utilities and cofactor-budget checks.

The determinant implementation is full signed-permutation expansion, not a
mate-search or a call to the classification implementation.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import permutations
import sympy as sp


@lru_cache(None)
def signed_permutations(n):
    return tuple((p, (-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i+1, n)))
                 for p in permutations(range(n)))


def clean(P):
    return {m: c for m, c in P.items() if c}


def determinant(matrix):
    """Entries are generator names (integers or strings), None, or ().

    None denotes a zero matrix entry; () denotes a unit. Every other entry
    denotes an independent commuting variable.
    """
    out = defaultdict(int)
    for p, sign in signed_permutations(len(matrix)):
        entries = [matrix[i][p[i]] for i in range(len(matrix))]
        if any(e is None for e in entries):
            continue
        mon = tuple(sorted(e for e in entries if e != ()))
        out[mon] += sign
    return clean(out)


@lru_cache(None)
def det(X, Y):
    return determinant(tuple(tuple(None if x-y < 0 else () if x == y else x-y for y in Y) for x in X))


def add(*terms):
    out = defaultdict(int)
    for scalar, P in terms:
        for mon, c in P.items():
            out[mon] += scalar*c
    return clean(out)


def mul(P, Q):
    out = defaultdict(int)
    for a, c in P.items():
        for b, d in Q.items():
            out[tuple(sorted(a+b))] += c*d
    return clean(out)


def h(j):
    return {} if j < 0 else {(): 1} if j == 0 else {(j,): 1}


def times(P, *indices):
    for j in indices:
        P = mul(P, h(j))
    return P


def coefficient(P, j, power=1):
    return {tuple(x for x in mon if x != j): c for mon, c in P.items() if mon.count(j) == power}


def top(P):
    return max((max(m, default=0) for m in P), default=0)


def evaluate(P, values):
    return sum(c*sp.prod(values(j) for j in m) for m, c in P.items())


def normalize(X, Y):
    return tuple(x-Y[-1] for x in X), tuple(y-Y[-1] for y in Y)


def profile(X, Y):
    return tuple(x-y for x, y in zip(X, Y)), tuple(X[i+1]-Y[i] for i in range(len(X)-1))


def lists(rows, gaps):
    Y = [0]*len(rows)
    for i in range(len(rows)-2, -1, -1):
        Y[i] = Y[i+1]+rows[i+1]-gaps[i]
    return tuple(Y[i]+rows[i] for i in range(len(rows))), tuple(Y)


def connected(X, Y):
    r, z = profile(X, Y)
    return all(a > 0 for a in r) and all(0 <= t < min(r[i], r[i+1]) for i, t in enumerate(z))


def rotate(X, Y):
    X, Y = normalize(X, Y)
    return tuple(X[0]-y for y in Y[::-1]), tuple(X[0]-x for x in X[::-1])


def gamma(X, Y):
    return tuple(2*x+1 for x in X), tuple(2*y for y in Y)


def endpoint(X, Y, t, up=True):
    return ((X[0]+t,)+X[1:], Y) if up else (X, Y[:-1]+(Y[-1]-t,))


def difference(X, Y, t):
    return add((1, det(*endpoint(X, Y, t))), (-1, det(*endpoint(X, Y, t, False))))


def border(X, Y, u, v):
    X, Y = normalize(X, Y)
    return normalize((X[0]+u,)+X, Y+(-v,))


def context(C, D, s, u, v, g):
    z = v+C[0]+g
    return (z+s+u, z+s)+tuple(v+c for c in C), (z,)+tuple(v+d for d in D)+(0,)


def negative_partition(X, Y):
    return tuple(c for c in (sum(x < y for y in Y) for x in X[::-1]) if c)


def conjugate(rho):
    return tuple(sum(p >= j for p in rho) for j in range(1, max(rho, default=0)+1))


def minimum(rho):
    return 1+max((p+i+1 for i, p in enumerate(rho)), default=0)


def partitions(total, bound=None):
    if total == 0:
        yield ()
        return
    for first in range(min(total, bound or total), 1-1, -1):
        for tail in partitions(total-first, first):
            yield (first,)+tail


def realization(n, rho):
    t = ((tuple(rho)+(0,)*n)[:n])[::-1]
    return tuple((n+1)*(n-t[i])-i-1 for i in range(n)), tuple((n+1)*(n-j-1) for j in range(n))


def blocks(X, Y):
    starts = [0]+[i for i in range(1, len(X)) if X[i] < Y[i-1]]+[len(X)]
    return [normalize(X[a:b], Y[a:b]) for a, b in zip(starts, starts[1:])]


def five_cores(i, p, q, G):
    X = tuple(p+r*G for r in range(4, -1, -1))
    FY = (3*G, G+q, G, q, 0) if i == 1 else (3*G+q, G+q, G, q, 0)
    HY = (2*G+q, 2*G, G, q, 0) if i == 1 else (2*G+q, 2*G, G+q, q, 0)
    return (X, FY), (X, HY)


def firing_control(name, callback):
    try:
        callback()
    except AssertionError:
        print('CONTROL FIRED:', name)
    else:
        raise AssertionError('CONTROL DID NOT FIRE: '+name)


def check_budgets(expected):
    budgets = {}
    for orders in partitions(6):
        if len(orders) < 2:
            continue
        cross = sum(a*b for i, a in enumerate(orders) for b in orders[i+1:])
        capacity = sum((n-1)*(n-2)//2 for n in orders)
        if cross <= 10 <= cross+capacity:
            budgets[tuple(sorted(orders))] = (cross, 10-cross)
    assert budgets == expected
    patterns = [rho for rho in partitions(10) if minimum(rho) == 7]
    assert len(patterns) == 15
    assert len({min(rho, conjugate(rho)) for rho in patterns}) == 8
    for rho in patterns:
        X, Y = realization(7, rho)
        child = blocks(X[1:], Y[:-1])
        orders = tuple(sorted(len(C) for C, D in child))
        assert orders in expected
        assert sum(sum(negative_partition(C, D)) for C, D in child) == expected[orders][1]
    named = {
        (4, 4, 2): [(2, 0), (4, 2)],
        (4, 4, 1, 1): [(2, 0), (4, 2)],
        (4, 3, 3): [(3, 0), (3, 1)],
    }
    for rho, expected_blocks in named.items():
        assert rho != conjugate(rho)
        for pattern in (rho, conjugate(rho)):
            X, Y = realization(7, pattern)
            got = sorted((len(C), sum(negative_partition(C, D))) for C, D in blocks(X[1:], Y[:-1]))
            assert got == expected_blocks
            for n in (8, 9):
                X, Y = realization(n, pattern)
                assert connected(X[1:], Y[:-1])
                assert negative_partition(X[1:], Y[:-1]) == pattern
    print('PASS: four budgets, fifteen patterns, eight orbits, and three held rigid orbits')


if __name__ == '__main__':
    expected = {(1, 5): (5, 5), (2, 4): (8, 2), (3, 3): (9, 1), (1, 1, 4): (9, 1)}
    check_budgets(expected)
    wrong = dict(expected)
    del wrong[(1, 1, 4)]
    firing_control('omitted one-negative three-component budget', lambda: check_budgets(wrong))
    print('ALL PASS')
