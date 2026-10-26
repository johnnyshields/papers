"""Exact cell geometry and free-complete-function arithmetic.

Shapes use English coordinates, with the southwest cell at (0, 0).
Polynomials map sorted tuples of positive h-indices to integer coefficients.
No external composition, root-search, or determinant implementation is imported.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations, product

ONE = {(): 1}


def translate(shape, v):
    return frozenset((i + v[0], j + v[1]) for i, j in shape)


def canonical(shape):
    if not shape:
        return frozenset()
    return translate(shape, (-max(i for i, _ in shape), -min(j for _, j in shape)))


def components(shape):
    remaining = set(shape)
    out = []
    while remaining:
        start = min(remaining)
        remaining.remove(start)
        todo, comp = [start], {start}
        while todo:
            i, j = todo.pop()
            for z in ((i-1, j), (i+1, j), (i, j-1), (i, j+1)):
                if z in remaining:
                    remaining.remove(z)
                    comp.add(z)
                    todo.append(z)
        out.append(frozenset(comp))
    return out


def is_skew(shape):
    if not shape:
        return True
    rows = sorted({i for i, _ in shape})
    ends = []
    for i in rows:
        js = sorted(j for a, j in shape if a == i)
        if js != list(range(js[0], js[-1]+1)):
            return False
        ends.append((js[0], js[-1]))
    return all(a >= c and b >= d for (a, b), (c, d) in zip(ends, ends[1:]))


def connected_skew(shape):
    return bool(shape) and is_skew(shape) and len(components(shape)) == 1


def interior(shape):
    return frozenset((i, j) for i, j in shape if (i+1, j+1) in shape)


def span(shape):
    return len({j-i for i, j in shape})


def rows(shape):
    return len({i for i, _ in shape})


def columns(shape):
    return len({j for _, j in shape})


def profile_shape(lengths, gaps):
    out = set()
    left = 0
    for k in range(len(lengths)-1, -1, -1):
        if k < len(lengths)-1:
            left += lengths[k+1] - gaps[k] - 1
        out.update((k-len(lengths)+1, j) for j in range(left, left+lengths[k]))
    return frozenset(out)


def profile(shape):
    shape = canonical(shape)
    rs = sorted({i for i, _ in shape})
    bounds = [(min(j for a, j in shape if a == i),
               max(j for a, j in shape if a == i)) for i in rs]
    lengths = tuple(b-a+1 for a, b in bounds)
    gaps = tuple(bounds[i+1][1]-bounds[i][0] for i in range(len(bounds)-1))
    return lengths, gaps


def compositions(n):
    if n == 0:
        yield ()
    else:
        for a in range(1, n+1):
            for rest in compositions(n-a):
                yield (a,) + rest


def shapes_of_area(n):
    for lengths in compositions(n):
        for gaps in product(*(range(min(a, b)) for a, b in zip(lengths, lengths[1:]))):
            yield profile_shape(lengths, gaps)


def boxed_shapes(maxrows, maxcols):
    for n in range(1, maxrows+1):
        for ascending in combinations(range(1, maxcols+n), n):
            lam = tuple(ascending[n-1-i]-(n-1-i) for i in range(n))
            for mu in product(*(range(x) for x in lam[:-1])):
                mu = mu + (0,)
                if any(a < b for a, b in zip(mu, mu[1:])):
                    continue
                shape = frozenset((i-n+1, j) for i in range(n) for j in range(mu[i], lam[i]))
                if connected_skew(shape):
                    yield shape


def add(a, b, scale=1):
    out = dict(a)
    for mon, c in b.items():
        out[mon] = out.get(mon, 0) + scale*c
        if not out[mon]:
            del out[mon]
    return out


def multiply(a, b):
    out = defaultdict(int)
    for u, c in a.items():
        for v, d in b.items():
            out[tuple(sorted(u+v))] += c*d
    return {m: c for m, c in out.items() if c}


def power(a, n):
    assert n >= 0
    out = ONE
    for _ in range(n):
        out = multiply(out, a)
    return out


def polynomial_span(poly):
    return max((max(m, default=0) for m in poly), default=0)


def determinant(indices):
    """Signed subset expansion; includes cancellation and every permutation."""
    size = len(indices)
    if size == 0:
        return ONE
    for cut in range(1, size):
        if all(indices[i][j] < 0 for i in range(cut, size) for j in range(cut)):
            left = tuple(tuple(row[:cut]) for row in indices[:cut])
            right = tuple(tuple(row[cut:]) for row in indices[cut:])
            return multiply(determinant(left), determinant(right))
    states = {0: ONE}
    for i in range(size):
        following = {}
        for mask, poly in states.items():
            for j, degree in enumerate(indices[i]):
                if degree < 0 or mask & (1 << j):
                    continue
                sign = (-1)**((mask >> (j+1)).bit_count())
                term = multiply(poly, {(degree,): 1} if degree else ONE)
                target = mask | (1 << j)
                following[target] = add(following.get(target, {}), term, sign)
        states = following
    return states.get((1 << size)-1, {})


def jt_indices(shape):
    assert connected_skew(shape)
    rs = sorted({i for i, _ in shape})
    lam = [max(j for a, j in shape if a == i)+1 for i in rs]
    mu = [min(j for a, j in shape if a == i) for i in rs]
    return tuple(tuple(lam[i]-mu[j]-i+j for j in range(len(rs))) for i in range(len(rs)))


@lru_cache(maxsize=10000)
def schur_connected(shape):
    return determinant(jt_indices(shape))


def schur(shape):
    out = ONE
    for comp in components(shape):
        out = multiply(out, schur_connected(canonical(comp)))
    return out


def corner_cofactor(shape):
    """Direct parent Jacobi--Trudi minor, without constructing the interior."""
    matrix = jt_indices(shape)
    n = len(matrix)
    N = span(shape)
    assert [(i, j) for i in range(n) for j in range(n) if matrix[i][j] == N] == [(0, n-1)]
    return determinant(tuple(row[:-1] for row in matrix[1:]))


def corner_from_polynomial(shape):
    N, n = span(shape), rows(shape)
    out = {}
    for mon, c in schur(shape).items():
        if N in mon:
            assert mon.count(N) == 1
            out[tuple(j for j in mon if j != N)] = (-1)**(n-1)*c
    return out


def strip_contains(E, v, z):
    """Exact infinite-strip membership using its finite content support."""
    p, N = v[1]-v[0], span(E)
    content = z[1]-z[0]
    lo = -((N-1-content)//p)
    hi = content//p
    return any((z[0]-k*v[0], z[1]-k*v[1]) in E for k in range(lo, hi+1))


def mark_sets(E, W, v):
    O = E - W - translate(W, v)
    What = set()
    for i, j in W:
        if strip_contains(E, v, (i+1, j+1)):
            What.add((i, j))
        if strip_contains(E, v, (i-1, j-1)):
            What.add((i-1, j-1))
    return O, frozenset(What), interior(O)


def nonadjacent(a, b):
    return not (a & b) and all((i+x, j+y) not in b for i, j in a
                             for x, y in ((1, 0), (-1, 0), (0, 1), (0, -1)))


def legal_marks(E, require_iv=True):
    """Enumerate end subsets, then check I--IV directly, including maximality."""
    E = canonical(E)
    N = span(E)
    ne = max(E, key=lambda z: z[1]-z[0])
    yield frozenset(), (ne[0], ne[1]+1), 'a'
    yield frozenset(), (ne[0]-1, ne[1]), 'b'
    for w in range(1, (N-1)//2+1):
        p = N-w
        band = sorted(z for z in E if 0 <= z[1]-z[0] < w)
        possibilities = []
        for mask in range(1 << len(band)):
            W = frozenset(z for j, z in enumerate(band) if mask & (1 << j))
            if (0, 0) not in W or span(W) != w or not connected_skew(W):
                continue
            for v in E:
                if v[1]-v[0] != p:
                    continue
                upper = translate(W, v)
                if upper <= E and ne in upper:
                    possibilities.append((W, v))
        for W, v in possibilities:
            if any(W < bigger for bigger, _ in possibilities):
                continue
            upper = translate(W, v)
            if not connected_skew(E-W) or not connected_skew(E-upper):
                continue
            O, What, Ohat = mark_sets(E, W, v)
            assert connected_skew(O)
            swO = min(O, key=lambda z: z[1]-z[0])
            neO = max(O, key=lambda z: z[1]-z[0])
            lowerH = (swO[0], swO[1]-1) in W
            lowerV = (swO[0]+1, swO[1]) in W
            upperH = (neO[0], neO[1]+1) in upper
            upperV = (neO[0]-1, neO[1]) in upper
            cases = []
            if lowerH and upperH: cases.append('a')
            if lowerV and upperV: cases.append('b')
            if lowerH and upperV: cases.append('c')
            if lowerV and upperH: cases.append('d')
            assert len(cases) == 1, (profile(E), W, cases)
            if require_iv and any(not nonadjacent(Ohat, translate(What, (k*v[0], k*v[1])))
                                  for k in (-1, 0, 1, 2)):
                continue
            yield W, v, cases[0]


def compose(D, E, W, v, case, supplemental=True):
    """Cell union from placements, including mixed vertical-ribbon supplements."""
    heights = defaultdict(list)
    for i, j in D:
        heights[j-i].append(i)
    low = {k: min(a) for k, a in heights.items()}
    high = {k: max(a) for k, a in heights.items()}
    upper = translate(W, v)
    out = set()
    for i, j in D:
        k = j-i
        z = {'a': i, 'b': -i, 'c': i-low[k], 'd': i-high[k]}[case]
        shift = (k*v[0]+z, k*v[1]+z)
        out.update(translate(E, shift))
        if supplemental and case in ('c', 'd') and (i-1, j) in D:
            rank = (lambda x, y: x-low[y-x]) if case == 'c' else (lambda x, y: high[y-x]-x)
            if rank(i, j) == rank(i-1, j):
                eps = 1 if case == 'c' else -1
                out.update(translate(upper, (shift[0]+eps, shift[1]+eps)))
    result = canonical(frozenset(out))
    assert connected_skew(result), (profile(D), profile(E), case, result)
    return result


def normalization(E, W, v):
    p, w = v[1]-v[0], span(W)
    O, What, Ohat = mark_sets(E, W, v)
    minus = frozenset(z for z in interior(E) if 0 <= z[1]-z[0] < w)
    plus = frozenset(z for z in interior(E) if p <= z[1]-z[0] < p+w)
    return schur(W), schur(What), schur(Ohat), multiply(schur(minus), schur(plus))
