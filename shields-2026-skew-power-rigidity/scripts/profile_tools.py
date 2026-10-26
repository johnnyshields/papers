"""Exact sparse determinants and profile operations for the cross-checks."""
from collections import defaultdict
from functools import lru_cache


def clean(p):
    return {m: c for m, c in p.items() if c}


def add(*polys):
    out = defaultdict(int)
    for p in polys:
        for m, c in p.items():
            out[m] += c
    return clean(out)


def scale(p, c):
    return {m: c * v for m, v in p.items() if c * v}


def mul(p, q):
    out = defaultdict(int)
    for a, x in p.items():
        for b, y in q.items():
            out[tuple(sorted(a + b))] += x * y
    return clean(out)


def monomial(indices, c=1):
    return {tuple(sorted(i for i in indices if i > 0)): c}


def derivative(p, j):
    out = defaultdict(int)
    for m, c in p.items():
        if j in m:
            a = list(m)
            a.remove(j)
            out[tuple(a)] += c * m.count(j)
    return clean(out)


def coefficient(p, indices):
    """Coefficient with exactly the prescribed multiplicities of these variables."""
    want = {i: indices.count(i) for i in set(indices)}
    return {tuple(i for i in m if i not in want): c for m, c in p.items()
            if all(m.count(i) == k for i, k in want.items())}


def component(p, degree):
    return {m: c for m, c in p.items() if len(m) == degree}


def determinant(matrix, max_degree=None):
    """Subset DP over all permutation terms; negative entry means zero."""
    n = len(matrix)
    assert all(len(row) == n for row in matrix)
    # Simultaneous reversal has sign +1 and visits sparse bottom rows first.
    matrix = tuple(tuple(reversed(row)) for row in reversed(matrix))
    states = {0: {(): 1}}
    for row in matrix:
        nxt = {}
        for mask, poly in states.items():
            for j, index in enumerate(row):
                if mask >> j & 1 or index < 0:
                    continue
                sign = (-1) ** ((mask >> (j + 1)).bit_count())
                target = nxt.setdefault(mask | (1 << j), defaultdict(int))
                for m, c in poly.items():
                    key = tuple(sorted(m + (index,))) if index else m
                    if max_degree is None or len(key) <= max_degree:
                        target[key] += sign * c
        states = {mask: clean(poly) for mask, poly in nxt.items() if clean(poly)}
    return states.get((1 << n) - 1, {})


def betas(profile):
    rows, gaps = profile
    n = len(rows)
    assert n == len(gaps) + 1
    x, y = [0] * n, [0] * n
    x[-1] = rows[-1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return tuple(x), tuple(y)


def board(profile, t=0):
    x, y = betas(profile)
    return tuple(tuple(a + t - b for b in y) for a in x)


def schur(profile, t=0, max_degree=None):
    return determinant(board(profile, t), max_degree)


def excesses(profile):
    r, q = profile
    return tuple(a - (q[i - 1] if i else 0)
                 - (q[i] if i < len(q) else 0) for i, a in enumerate(r))


def from_excess(gaps, excess):
    n = len(excess)
    assert len(gaps) == n - 1
    return (tuple(excess[i] + (gaps[i - 1] if i else 0)
                  + (gaps[i] if i < n - 1 else 0) for i in range(n)), tuple(gaps))


def inner(g, p):
    return from_excess(g, (p,) * (len(g) + 1))


def rotate(profile):
    return tuple(tuple(reversed(v)) for v in profile)


def near(a, b):
    r, q = a
    s, v = b
    return r[:-1] + (r[-1] + s[0],) + s[1:], q + v


def concat(a, b):
    return a[0] + b[0], a[1] + (0,) + b[1]


def power(e, m):
    assert m > 0
    a = e
    for _ in range(m - 1):
        a = near(a, e)
    return a


def family(e, alpha):
    a = power(e, alpha[0])
    for m in alpha[1:]:
        a = concat(a, power(e, m))
    return a


def compositions(n):
    if n == 0:
        yield ()
    for mask in range(1 << max(0, n - 1)) if n else ():
        cuts = (0,) + tuple(i for i in range(1, n) if mask >> (i - 1) & 1) + (n,)
        yield tuple(b - a for a, b in zip(cuts, cuts[1:]))


@lru_cache(maxsize=512)
def hessenberg(profile):
    """Independent interval expansion, not the determinant DP."""
    rows, gaps = profile
    n = len(rows)
    assert min(excesses(profile)) > 0
    out = defaultdict(int)
    for mask in range(1 << (n - 1)):
        cuts = (0,) + tuple(i for i in range(1, n) if mask >> (i - 1) & 1) + (n,)
        labels = []
        for a, b in zip(cuts, cuts[1:]):
            labels.append(sum(rows[a:b]) - sum(gaps[a:b - 1]))
            labels.extend(gaps[a:b - 1])
        out[tuple(sorted(i for i in labels if i > 0))] += (-1) ** (n - len(cuts) + 1)
    return clean(out)


def boundary(profile, side, i):
    if side == 'right':
        profile = rotate(profile)
    rows, gaps = profile
    if not i:
        return 0, {(): 1}, ()
    return (sum(rows[:i]) - sum(gaps[:i]),
            scale(hessenberg((rows[:i], gaps[:i - 1])), (-1) ** i), gaps[:i])


def cap(profile, l, H, G):
    rows, gaps = profile
    assert 0 < H < G and 1 <= l < len(rows)
    return (rows[:l - 1] + (rows[l - 1] - gaps[l - 1] + H, G),
            gaps[:l - 1] + (H,))


def balanced_positions(g):
    return {s for s in range(len(g)) if sorted(g[:s]) == sorted(g[len(g)-s:])
            and g[s] != g[-s-1]}


def admitted(g):
    if g[0] != g[-1] or g == g[::-1]:
        return True
    d = next(i for i, (a, b) in enumerate(zip(g, g[::-1])) if a != b)
    return balanced_positions(g) == {d}


def core_data(e, alpha):
    x, y = betas(e)
    S, p = x[0], x[0] - x[1]
    M = sum(alpha)
    T = {sum(alpha[i:]) for i in range(1, len(alpha))}
    K = set(range(1, M)) - T
    J = {a + p for a in x[2:]}
    Z = {a * S + j for a in range(M) for j in J} | {a*S for a in T} | {a*S+p for a in T}
    U = tuple(sorted({M*S+p, M*S} | {a*S for a in K}, reverse=True))
    V = tuple(sorted({0, p} | {a*S+p for a in K}, reverse=True))
    return S, p, J, T, K, Z, U, V


def word_matrix(delta, a, b, c):
    if not delta:
        return ((c,),)
    xi = [0]
    for d in delta:
        xi.append(xi[-1] + d)
    M, L = xi[-1], len(delta)
    return (tuple(b[x] for x in xi[1:]) + (c,),) + tuple(
        tuple(a[xi[j]-xi[i-1]] if j >= i else -1 for j in range(1, L+1))
        + (b[M-xi[i-1]],) for i in range(1, L+1))
