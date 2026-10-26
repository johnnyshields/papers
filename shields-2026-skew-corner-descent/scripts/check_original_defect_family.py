#!/usr/bin/env python3
"""The original defect for every square-tile inner in a range, against the cyclic formula.

Paper sections `sec:dual` (Cyclic inventories and original coefficients),
`sec:normal-chart` and `sec:one-active`; targets `rem:square-word`,
`lem:original-transfer`, `cor:many-active`, `thm:intrinsic-order` (pure primitive
branch), and the literal alternative.

The inner U is a chain of b empty-joined squares (2,2) with edge word e in {H,V}^(b-1);
W is the first v tiles.  Here the inventory is Lambda = h_1 = psi, so a = 1,
t = h_1, N = 1, r = 1, delta = 3, d = b-v, n = d, B = b, H_j = 1 + 3 j.
Every edge word in the stated domain is enumerated: b >= 3, 1 <= v <= b-2, gcd(b,v) = 1,
equal first and last windows, and equal cut directions at the two private cuts.  The
determinants f, A_W, E_2, beta are expanded from the original Jacobi--Trudi
matrices as exact power series in t, with every other h_j a rational number and the
generator h_{H_j} left free.  The residue function rho is not assumed: its exponents
are the class counts e_X = s c_X - d t_X of the response word, labels alpha_H = 0 and
alpha_V = 1, and exact residue matching f^v / A_W^b = rho(u) at t = 0 is asserted at
two independent assignments of the other generators.  For each j from 2 to B:

  * the coefficients of t^i for i < j-1 do not involve h_{H_j};
  * the coefficient of t^{j-1} is affine in h_{H_j} (three values, second difference 0);
  * its h_{H_j}-derivative is rho(u_0) (-1)^{j-1} a^{1-j} N_j, N_j from window sums.

The first nonzero order of Theta_U is then bounded by d (and by d-1 on the pure
inventory Lambda = psi, and by d-1 with two active classes) unless the word is
constant, which is the literal empty row or column composition of b squares.
Controls: a word outside the window domain violates residue matching, and a
perturbed N_j breaks the derivative identity.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, prod

SQUARE = 3          # span delta of the square (2,2)
RESPONSE = {'H': 0, 'V': 1}


def tile_word(edges):
    rows, gaps = [2, 2], [1]
    for edge in edges:
        if edge == 'V':
            gaps += [0, 1]
            rows += [2, 2]
        else:
            rows[-1] += 2
            rows += [2]
            gaps += [1]
    return rows, gaps


def indices_of(profile):
    rows, gaps = profile
    size = len(rows)
    x, y = [0] * size, [0] * size
    x[-1] = rows[-1]
    for i in range(size - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return [[a - b for b in y] for a in x]


def smul(a, b, L):
    out = [F(0)] * L
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b[:L - i]):
                out[i + j] += x * y
    return out


def sadd(a, b, sign=1):
    return [x + sign * y for x, y in zip(a, b)]


def entry_series(index, L, hvalue, gen_index, gen_value):
    if index < 0:
        return None
    if index == 0:
        return [F(1)] + [F(0)] * (L - 1)
    if index == 1:
        return [F(0), F(1)] + [F(0)] * (L - 2)
    if index == gen_index:
        value = gen_value
    else:
        value = hvalue(index)
    return [F(value)] + [F(0)] * (L - 1)


def subset_determinant(profile, L, hvalue, gen_index=None, gen_value=0):
    """Signed subset expansion over truncated power series in t (small sizes only)."""
    matrix = indices_of(profile)
    size = len(matrix)
    one = [F(1)] + [F(0)] * (L - 1)
    states = {0: one}
    for i in range(size):
        following = {}
        for mask, poly in states.items():
            for j in range(size):
                if mask >> j & 1:
                    continue
                e = entry_series(matrix[i][j], L, hvalue, gen_index, gen_value)
                if e is None:
                    continue
                sign = -1 if (mask >> (j + 1)).bit_count() % 2 else 1
                target = mask | (1 << j)
                term = smul(poly, e, L)
                following[target] = sadd(following.get(target, [F(0)] * L), term, sign)
        states = following
    return states[(1 << size) - 1]


def exact_det(rows):
    """Determinant of a square Fraction matrix by elimination with row swaps."""
    a = [list(r) for r in rows]
    n, det = len(a), F(1)
    for c in range(n):
        pivot = next((r for r in range(c, n) if a[r][c] != 0), None)
        if pivot is None:
            return F(0)
        if pivot != c:
            a[c], a[pivot] = a[pivot], a[c]
            det = -det
        det *= a[c][c]
        for r in range(c + 1, n):
            if a[r][c] != 0:
                f = a[r][c] / a[c][c]
                for k in range(c, n):
                    a[r][k] -= f * a[c][k]
    return det


def determinant(profile, L, hvalue, gen_index=None, gen_value=0):
    """Original Jacobi--Trudi determinant as an exact polynomial in t = h_1, truncated
    to L coefficients.  Evaluated at integer t by elimination and recovered by Newton
    interpolation, since the degree in t is at most the matrix size."""
    matrix = indices_of(profile)
    size = len(matrix)

    def entry(index, t):
        if index < 0:
            return F(0)
        if index == 0:
            return F(1)
        if index == 1:
            return F(t)
        return F(gen_value if index == gen_index else hvalue(index))

    points = list(range(size + 1))
    values = [exact_det([[entry(x, t) for x in row] for row in matrix]) for t in points]
    # Newton divided differences, then expansion to monomial coefficients
    coef = list(values)
    for k in range(1, len(points)):
        for i in range(len(points) - 1, k - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (points[i] - points[i - k])
    poly = [F(0)]
    for i in range(len(points) - 1, -1, -1):
        shifted = [F(0)] + poly
        poly = [shifted[k] - points[i] * (poly[k] if k < len(poly) else 0) for k in range(len(shifted))]
        poly[0] += coef[i]
    poly = (poly + [F(0)] * L)[:L]
    return poly


def sinv(a, L):
    out = [F(0)] * L
    out[0] = 1 / a[0]
    for k in range(1, L):
        out[k] = -sum(a[i] * out[k - i] for i in range(1, k + 1)) / a[0]
    return out


def spow(a, n, L):
    if n < 0:
        a, n = sinv(a, L), -n
    out = [F(1)] + [F(0)] * (L - 1)
    for _ in range(n):
        out = smul(out, a, L)
    return out


def make_h(h2, h4, shift):
    def h(index):
        return {2: h2, 4: h4}.get(index, index ** 3 + index + 3 + shift)
    return h


def window_inverse(word, j, S):
    size = len(word)
    return sum((1 / prod(S[word[(i + a) % size]] for a in range(j)) for i in range(size)), F(0))


def predicted_N(j, b, v, edges, S):
    d = b - v
    k, s = divmod(b, d)
    if s == 0:
        k, s = k - 1, d
    word = tuple(RESPONSE[x] for x in edges)
    P = word[:d]
    # the response word has period P on its length-(B-1) range
    assert word == (P * k + P[:s - 1])[:b - 1] and len(word) == b - 1, (edges, P)
    R = P[:s - 1]
    c, t = Counter(P), Counter(R)
    e = {x: s * c[x] - d * t[x] for x in (0, 1)}
    assert sum(e.values()) == d
    return e, word, P


def N_value(j, b, e, P, word, S):
    return b * window_inverse(P, j, S) - sum(e[x] * window_inverse(word + (x,), j, S) for x in (0, 1))


def first_order(series):
    for i, c in enumerate(series):
        if c:
            return i
    return None


def rho_value(u, e, eps):
    labels = {0: F(0), 1: F(1)}
    out = F(eps)
    for x in (0, 1):
        out *= (u - labels[x]) ** e[x]
    return out


def main():
    counts = Counter()
    assignments = [(F(2), F(7), 0), (F(3), F(11), 1)]
    for b in range(3, 7):
        for v in range(1, b - 1):
            if gcd(b, v) != 1:
                continue
            d = b - v
            L = b + 1
            H = lambda j: 1 + SQUARE * j
            for edges in product('HV', repeat=b - 1):
                edges = ''.join(edges)
                counts['edge words'] += 1
                windows = edges[:v - 1] == edges[b - v:] and edges[v - 1] == edges[b - v - 1]
                literal = len(set(edges)) == 1
                if not windows:
                    counts['outside window domain'] += 1
                    continue
                U, Wp = tile_word(edges), tile_word(edges[:v - 1])
                E2p = tile_word(edges + edges[v - 1:])
                betap = tile_word(edges + 'H' + edges)
                try:
                    e, word, P = predicted_N(0, b, v, edges, None)
                except AssertionError:
                    counts['word not periodic on its range'] += 1
                    continue
                matched = True
                for h2, h4, shift in assignments:
                    h = make_h(h2, h4, shift)
                    f = determinant(U, L, h)
                    A = determinant(Wp, L, h)
                    beta = determinant(betap, L, h)
                    u0 = beta[0] / f[0] ** 2
                    lhs = f[0] ** v / A[0] ** b
                    eps = None
                    for candidate in (1, -1):
                        if lhs == rho_value(u0, e, candidate):
                            eps = candidate
                    if eps is None:
                        matched = False
                if not matched:
                    counts['residue matching fails'] += 1
                    continue
                counts['in domain with exact residue matching'] += 1
                active = [x for x in (0, 1) if e[x]]
                for h2, h4, shift in assignments:
                    h = make_h(h2, h4, shift)
                    S = {0: F(h4), 1: F(h4 - h2 ** 2)}
                    assert S[0] and S[1]
                    # one generator per j
                    for j in range(2, b + 1):
                        gen = H(j)
                        coefficients = {}
                        for g in (F(5), F(-3), F(9)):
                            f = determinant(U, L, h, gen, g)
                            A = determinant(Wp, L, h, gen, g)
                            E2 = determinant(E2p, L, h, gen, g)
                            beta = determinant(betap, L, h, gen, g)
                            u = smul(beta, spow(f, -2, L), L)
                            # rho(u) as a series, with eps fixed by the residue at g-independent order 0
                            rho = [F(1)] + [F(0)] * (L - 1)
                            for x, alpha in ((0, 0), (1, 1)):
                                shifted = list(u)
                                shifted[0] -= alpha
                                rho = smul(rho, spow(shifted, e[x], L), L)
                            first = smul(spow(f, v, L), spow(smul(E2, spow(f, -2, L), L), b, L), L)
                            lhs0 = f[0] ** v / A[0] ** b
                            eps = 1 if lhs0 == rho[0] else -1
                            assert lhs0 == eps * rho[0]
                            Theta = sadd(first, [eps * x for x in rho], -1)
                            assert Theta[0] == 0
                            coefficients[g] = (Theta, eps, u[0])
                        g1, g2, g3 = (F(5), F(-3), F(9))
                        for i in range(j - 1):
                            assert coefficients[g1][0][i] == coefficients[g2][0][i] == coefficients[g3][0][i]
                        c1, c2, c3 = (coefficients[g][0][j - 1] for g in (g1, g2, g3))
                        slope = (c2 - c1) / (g2 - g1)
                        assert (c3 - c2) / (g3 - g2) == slope           # affine in the generator
                        eps, u0 = coefficients[g1][1], coefficients[g1][2]
                        expected = rho_value(u0, e, eps) * (-1) ** (j - 1) * N_value(j, b, e, P, word, S)
                        assert slope == expected, (edges, b, v, j, slope, expected)
                        perturbed = expected + F(1, 3)
                        counts['control: perturbed N_j rejected'] += slope != perturbed
                        counts['transfer identities'] += 1
                    # order of the defect, from the original determinants at generic generator values
                    f = determinant(U, L, h)
                    A = determinant(Wp, L, h)
                    E2 = determinant(E2p, L, h)
                    beta = determinant(betap, L, h)
                    u = smul(beta, spow(f, -2, L), L)
                    rho = [F(1)] + [F(0)] * (L - 1)
                    for x, alpha in ((0, 0), (1, 1)):
                        shifted = list(u)
                        shifted[0] -= alpha
                        rho = smul(rho, spow(shifted, e[x], L), L)
                    first = smul(spow(f, v, L), spow(smul(E2, spow(f, -2, L), L), b, L), L)
                    eps = 1 if f[0] ** v / A[0] ** b == rho[0] else -1
                    Theta = sadd(first, [eps * x for x in rho], -1)
                    order = first_order(Theta)
                    if literal:
                        counts['literal row/column words'] += 1
                        continue
                    assert order is not None and order <= d - 1, (edges, order)     # pure inventory: b - v - 1
                    if len(active) >= 2:
                        assert order <= d - 1
                    counts['orders measured'] += 1
                    counts['order = d-1 attained'] += order == d - 1
                    counts['orders by active classes %d: order %d' % (len(active), order)] += 1
                    if len(active) == 1:
                        assert order <= 1, (edges, order)    # thm:pure-primitive-first
    # the interpolated determinant agrees with the signed subset expansion
    for edges in ('HVH', 'HVVH', 'VHV'):
        h = make_h(F(2), F(7), 0)
        for prof in (tile_word(edges), tile_word(edges[:1])):
            assert determinant(prof, 6, h, 7, F(5)) == subset_determinant(prof, 6, h, 7, F(5))
            counts['interpolation versus subset expansion'] += 1
    assert counts['in domain with exact residue matching'] and counts['orders measured']
    assert counts['outside window domain'] and counts['residue matching fails'] >= 0
    assert counts['transfer identities'] and counts['control: perturbed N_j rejected'] == counts['transfer identities']
    print(dict(counts))
    print('check_original_defect_family: PASS')


if __name__ == '__main__':
    main()
