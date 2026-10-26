"""Exact full-board Jacobi--Trudi polynomials and profile constructions."""
from collections import Counter
from itertools import permutations


def normalize(X, Y):
    return tuple(x - Y[-1] for x in X), tuple(y - Y[-1] for y in Y)


def validate(X, Y):
    assert len(X) == len(Y) > 0
    assert all(a > b for a, b in zip(X, X[1:]))
    assert all(a > b for a, b in zip(Y, Y[1:]))
    assert all(x > y for x, y in zip(X, Y))
    assert all(x >= y for x, y in zip(X[1:], Y[:-1]))


def from_profile(rows, gaps):
    assert len(rows) == len(gaps) + 1
    assert all(r > 0 for r in rows)
    assert all(0 <= g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps))
    Y = [0] * len(rows)
    for i in range(len(rows) - 2, -1, -1):
        Y[i] = Y[i + 1] + rows[i + 1] - gaps[i]
    X = tuple(y + r for y, r in zip(Y, rows))
    validate(X, Y)
    return X, tuple(Y)


def profile(X, Y):
    validate(X, Y)
    return tuple(x - y for x, y in zip(X, Y)), tuple(x - y for x, y in zip(X[1:], Y[:-1]))


def rotation(X, Y):
    X, Y = normalize(X, Y)
    return tuple(X[0] - y for y in reversed(Y)), tuple(X[0] - x for x in reversed(X))


def negatives(X, Y):
    return frozenset((i + 1, j + 1) for i, x in enumerate(X) for j, y in enumerate(Y) if x < y)


def clean(poly):
    return {m: c for m, c in poly.items() if c}


def add(*signed):
    out = Counter()
    for sign, poly in signed:
        for m, c in poly.items():
            out[m] += sign * c
    return clean(out)


def multiply(P, Q):
    out = Counter()
    for m, c in P.items():
        for n, d in Q.items():
            out[tuple(sorted(m + n, reverse=True))] += c * d
    return clean(out)


def h(k):
    return {} if k < 0 else {(): 1} if k == 0 else {(k,): 1}


def determinant(X, Y):
    """Column-subset dynamic programming; units are retained, negatives rejected."""
    assert len(X) == len(Y)
    dp = {0: {(): 1}}
    for x in X:
        nxt = {}
        for mask, poly in dp.items():
            for j, y in enumerate(Y):
                if mask >> j & 1 or x < y:
                    continue
                sign = (-1) ** (mask >> (j + 1)).bit_count()
                newmask = mask | (1 << j)
                nxt[newmask] = add((1, nxt.get(newmask, {})),
                                  (sign, multiply(poly, h(x - y))))
        dp = nxt
    return dp.get((1 << len(X)) - 1, {})


def permutation_determinant(X, Y):
    out = Counter()
    for p in permutations(range(len(X))):
        labels = tuple(X[i] - Y[j] for i, j in enumerate(p))
        if min(labels, default=0) < 0:
            continue
        sign = (-1) ** sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))
        out[tuple(sorted((k for k in labels if k), reverse=True))] += sign
    return clean(out)


def coefficient(P, k, power=1):
    out = {}
    for m, c in P.items():
        if m.count(k) == power:
            out[tuple(x for x in m if x != k)] = c
    return out


def largest(P):
    return max((k for m in P for k in m), default=0)


def border(X, Y, u, v):
    assert u > 0 and v > 0
    return normalize((X[0] + u,) + tuple(X), tuple(Y) + (Y[-1] - v,))


def extend(X, Y, t, top=True):
    assert t > 0
    return normalize((X[0] + t,) + X[1:], Y) if top else normalize(X, Y[:-1] + (Y[-1] - t,))


def gamma(X, Y):
    return tuple(2 * x + 1 for x in X), tuple(2 * y for y in Y)


def homogenize(P, n):
    out = {}
    for m, c in P.items():
        key = tuple(sorted(tuple(2 * k + 1 for k in m) + (1,) * (n - len(m)), reverse=True))
        assert key not in out
        out[key] = c
    return out


def hessenberg(rows, gaps):
    """Interval-cycle expansion, independently of determinant dynamic programming."""
    n = len(rows)
    out = Counter()
    for mask in range(1 << (n - 1)):
        labels = [g for i, g in enumerate(gaps) if mask >> i & 1]
        i = 0
        while i < n:
            w = rows[i]
            while i < n - 1 and mask >> i & 1:
                w += rows[i + 1] - gaps[i]
                i += 1
            labels.append(w)
            i += 1
        assert min(labels) >= 0
        out[tuple(sorted((k for k in labels if k), reverse=True))] += (-1) ** mask.bit_count()
    return clean(out)


def five_family(kind, b, g, q):
    assert 1 <= q <= b < g
    X = tuple(b + k * g for k in range(4, -1, -1))
    if kind == 1:
        return (X, (3*g, g+q, g, q, 0)), (X, (2*g+q, 2*g, g, q, 0))
    assert kind == 2
    return (X, (3*g+q, g+q, g, q, 0)), (X, (2*g+q, 2*g, g+q, q, 0))


def staircase_family(kind, a, b, d, t=0):
    assert d >= 0 and t >= 0
    if kind <= 2:
        assert a != b and min(a, b) > t + d
        k = a + b if kind == 1 else a + b - t
        rows = ((a,b,a,k,b), (a,k,b,a,b))
        gaps = ((t,0,t,t), (t,t,0,t)) if kind == 1 else ((0,t,0,0), (0,0,t,0))
    else:
        assert a >= 1 and b > a + d
        rows = ((a,b,b,b,a+b),(a,b,a+b,b,b)) if kind == 3 else ((a,b,b,a+b,a+b),(a,b,a+b,a+b,b))
        gaps = ((0,0,0,a),(0,a,0,0)) if kind == 3 else ((0,0,a,a),(0,a,a,0))
    return tuple(from_profile(tuple(x+d for x in r), tuple(x+d for x in z)) for r,z in zip(rows,gaps))


def rejects(action):
    try:
        action()
    except (AssertionError, RuntimeError, TimeoutError):
        return
    raise AssertionError('Rejecting control did not fire')


def require(claim):
    assert claim
