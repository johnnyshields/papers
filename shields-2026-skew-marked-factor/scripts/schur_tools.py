"""Exact cell geometry and symmetric functions, independent of external engines."""

from collections import Counter
from functools import lru_cache
from itertools import product
from math import factorial

import sympy as sp


@lru_cache(None)
def h(k):
    return sp.Integer(k == 0) if k <= 0 else sp.Symbol(f"h{k}")


def translate(cells, shift):
    a, b = shift
    return frozenset((i + a, j + b) for i, j in cells)


def normalize(cells):
    if not cells:
        return frozenset()
    return translate(cells, (-max(i for i, j in cells), -min(j for i, j in cells)))


def partitions(n, largest=None):
    if n == 0:
        yield ()
    else:
        for k in range(min(n, largest or n), 0, -1):
            for tail in partitions(n - k, k):
                yield (k,) + tail


def compositions(n):
    if n == 0:
        yield ()
    else:
        for k in range(1, n + 1):
            for tail in compositions(n - k):
                yield (k,) + tail


def from_profile(rows, gaps):
    """A gap is one less than the overlap of consecutive rows."""
    left = [0] * len(rows)
    for i in range(len(rows) - 2, -1, -1):
        left[i] = left[i + 1] + rows[i + 1] - gaps[i] - 1
    return normalize(frozenset((i, j) for i, r in enumerate(rows)
                               for j in range(left[i], left[i] + r)))


def shapes(area):
    for rows in compositions(area):
        for gaps in product(*(range(min(a, b)) for a, b in zip(rows, rows[1:]))):
            yield from_profile(rows, gaps)


def is_skew(cells):
    if not cells:
        return False
    rr = sorted({i for i, j in cells})
    if rr != list(range(rr[0], rr[-1] + 1)):
        return False
    bounds = []
    for i in rr:
        js = sorted(j for a, j in cells if a == i)
        if js != list(range(js[0], js[-1] + 1)):
            return False
        bounds.append((js[0], js[-1]))
    return all(a >= c and b >= d for (a, b), (c, d) in zip(bounds, bounds[1:]))


def connected(cells):
    if not cells:
        return False
    seen = set()
    stack = [next(iter(cells))]
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        i, j = x
        stack.extend(y for y in ((i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1))
                     if y in cells and y not in seen)
    return len(seen) == len(cells)


def span(cells):
    return len({j - i for i, j in cells})


def dimensions(cells):
    return len({i for i, j in cells}), len({j for i, j in cells}), span(cells)


def transpose(cells):
    return normalize(frozenset((j, i) for i, j in cells))


def rotate(cells):
    return normalize(frozenset((-i, -j) for i, j in cells))


def antitranspose(cells):
    return rotate(transpose(cells))


def lambda_mu(cells):
    cells = normalize(cells)
    rr = sorted({i for i, j in cells})
    lam = tuple(max(j for a, j in cells if a == i) + 1 for i in rr)
    mu = tuple(min(j for a, j in cells if a == i) for i in rr)
    return lam, mu


@lru_cache(None)
def determinant(indices):
    """Laplace expansion along the sparsest row, cached by the whole minor."""
    n = len(indices)
    if not n:
        return sp.Integer(1)
    row = min(range(n), key=lambda i: sum(k >= 0 for k in indices[i]))
    result = 0
    for j, k in enumerate(indices[row]):
        if k < 0:
            continue
        minor = tuple(tuple(v for c, v in enumerate(rr) if c != j)
                      for r, rr in enumerate(indices) if r != row)
        result += (-1) ** (row + j) * h(k) * determinant(minor)
    return sp.expand(result)


@lru_cache(None)
def schur(cells):
    if not cells:
        return sp.Integer(1)
    lam, mu = lambda_mu(cells)
    return determinant(tuple(tuple(lam[i] - mu[j] - i + j for j in range(len(lam)))
                             for i in range(len(lam))))


def delta(poly, k):
    assert k > 0
    return sp.expand(sum(h(int(x.name[1:]) - k) * sp.diff(poly, x)
                         for x in poly.free_symbols if int(x.name[1:]) >= k))


def apply(poly, indices):
    for k in indices:
        poly = delta(poly, k)
    return poly


def primitive(poly):
    poly = sp.expand(poly)
    if not poly.free_symbols:
        assert poly != 0
        return sp.Integer(1)
    variables = sorted(poly.free_symbols, key=lambda x: int(x.name[1:]))
    pp = sp.Poly(poly, *variables, domain=sp.QQ)
    _, integral = pp.clear_denoms()
    _, integral = integral.primitive()
    costs = [(sum(e * int(v.name[1:]) ** 2 for e, v in zip(mon, variables)), coeff)
             for mon, coeff in integral.terms()]
    minimum = min(c for c, a in costs)
    winners = [a for c, a in costs if c == minimum]
    assert len(winners) == 1
    return sp.expand(sp.sign(winners[0]) * integral.as_expr())


@lru_cache(None)
def power_sum(k):
    return sp.expand(k * h(k) - sum(power_sum(i) * h(k - i) for i in range(1, k)))


def z_value(nu):
    return sp.prod(k ** m * factorial(m) for k, m in Counter(nu).items())


@lru_cache(None)
def standard_tableaux(cells):
    """Count linear extensions by removing each possible largest entry."""
    if not cells:
        return 1
    corners = [(i, j) for i, j in cells if (i + 1, j) not in cells and (i, j + 1) not in cells]
    return sum(standard_tableaux(cells - {x}) for x in corners)


def hats(E, W, v):
    Wtop = translate(W, v)
    O = E - W - Wtop
    periodic = frozenset().union(*(translate(E, (k * v[0], k * v[1])) for k in range(-2, 3)))
    What = frozenset(x for x in periodic if (x[0] + 1, x[1] + 1) in W)
    What |= frozenset(x for x in W if (x[0] + 1, x[1] + 1) in periodic)
    Ohat = frozenset(x for x in O if (x[0] + 1, x[1] + 1) in O)
    return O, What, Ohat


def legal_marks(E):
    """Test I--IV directly on end subdiagrams, including both empty edges."""
    E = normalize(E)
    N = span(E)
    ne = min(E, key=lambda x: (x[0], -x[1]))
    yield frozenset(), (ne[0], ne[1] + 1), 'a'
    yield frozenset(), (ne[0] - 1, ne[1]), 'b'
    for w in range(1, (N - 1) // 2 + 1):
        p = N - w
        for target in (x for x in E if x[1] - x[0] == p):
            v = target  # The southwest cell is (0, 0).
            W = E & translate(E, (-v[0], -v[1]))
            if (0, 0) not in W or span(W) != w or not connected(W) or not is_skew(W):
                continue
            top = translate(W, v)
            if ne not in top or not top <= E or W & top:
                continue
            O, What, Ohat = hats(E, W, v)
            if not connected(O) or not is_skew(O):
                continue
            if any(not connected(E - part) or not is_skew(E - part) for part in (W, top)):
                continue
            osw = max(O, key=lambda x: (x[0], -x[1]))
            one = min(O, key=lambda x: (x[0], -x[1]))
            lower = 'H' if (osw[0], osw[1] - 1) in W else 'V'
            upper = 'H' if (one[0], one[1] + 1) in top else 'V'
            if lower == 'V' and (osw[0] + 1, osw[1]) not in W:
                continue
            if upper == 'V' and (one[0] - 1, one[1]) not in top:
                continue
            bad = False
            for k in range(-2, 3):
                other = translate(Ohat, (k * v[0], k * v[1]))
                if any((i + di, j + dj) in other for i, j in What
                       for di, dj in ((0, 1), (0, -1), (1, 0), (-1, 0))):
                    bad = True
            if not bad:
                yield W, v, {('H', 'H'): 'a', ('V', 'V'): 'b',
                             ('H', 'V'): 'c', ('V', 'H'): 'd'}[(lower, upper)]


def compose(D, E, W, v, case, require_connected=True):
    assert D and E
    copies = []
    for i, j in D:
        t = j - i
        diagonal = [a for a, b in D if b - a == t]
        level = {'a': i, 'b': -i, 'c': i - min(diagonal), 'd': i - max(diagonal)}[case]
        shift = (t * v[0] + level, t * v[1] + level)
        copies.append(translate(E, shift))
        if case in ('c', 'd') and (i - 1, j) in D:
            other = [a for a, b in D if b - a == t + 1]
            rank = i - min(diagonal) if case == 'c' else max(diagonal) - i
            rank_above = i - 1 - min(other) if case == 'c' else max(other) - (i - 1)
            if rank == rank_above:
                sign = 1 if case == 'c' else -1
                copies.append(translate(W, (shift[0] + v[0] + sign, shift[1] + v[1] + sign)))
    F = normalize(frozenset().union(*copies))
    if require_connected:
        assert connected(F) and is_skew(F), (D, E, W, v, case)
    return F


def removals(cells, k):
    """Southeast-removable k-ribbons from beta-number moves, not derivatives."""
    lam, mu = lambda_mu(cells)
    n = len(lam)
    X = {lam[i] + n - 1 - i for i in range(n)}
    for x in sorted(X):
        y = x - k
        if y < 0 or y in X:
            continue
        beta = sorted((X - {x}) | {y}, reverse=True)
        nu = tuple(beta[i] - n + 1 + i for i in range(n))
        if any(a < b for a, b in zip(nu, mu)):
            continue
        remainder = frozenset((i - n + 1, j) for i in range(n)
                              for j in range(mu[i], nu[i]))
        ribbon = normalize(cells) - remainder
        assert len(ribbon) == k and connected(ribbon)
        assert not any((i + 1, j) in ribbon and (i, j + 1) in ribbon
                       and (i + 1, j + 1) in ribbon for i, j in ribbon)
        yield remainder, ribbon, len({i for i, j in ribbon}) - 1


def decode(P, p):
    """The decoder receives no diagram, area, normalization, or attachment type."""
    derivatives = [P]
    while True:
        nxt = delta(derivatives[-1], p)
        if nxt == 0:
            break
        derivatives.append(nxt)
    a = len(derivatives) - 1
    if a == 0:
        raise ValueError('No ordinary chart at this period')
    T, U = derivatives[-1], derivatives[-2]
    inner = primitive(sp.cancel(U / sp.gcd(U, T)))
    outer = 0
    ratios = {}
    for nu in partitions(a):
        ratio = sp.cancel(apply(P, (p * k for k in nu)) / T)
        if ratio.free_symbols:
            raise ValueError('A top-weight derivative ratio is not scalar')
        ratios[nu] = ratio
        outer += ratio * sp.prod(power_sum(k) for k in nu) / z_value(nu)
    return a, inner, primitive(outer), T, U, ratios
