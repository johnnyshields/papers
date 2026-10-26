#!/usr/bin/env python3
"""Check a fresh original coefficient against the cyclic response formula.

The actual inner consists of five square tiles with edge word H,V,V,H.
Its two-copy end windows are equal, and its three-gap period has signed
class exponents (-1,4).  Determinants are computed directly by a full subset
expansion over original rows, using exact first-order dual numbers.
"""
from fractions import Fraction as F
from math import prod


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def mul(x, y):
    return x[0] * y[0], x[0] * y[1] + x[1] * y[0]


def power(x, n):
    if n < 0:
        x = F(1, x[0]), -F(x[1], x[0] ** 2)
        n = -n
    out = (F(1), F(0))
    for _ in range(n):
        out = mul(out, x)
    return out


def tile_word(edges):
    rows, gaps = [2, 2], [1]
    for edge in edges:
        if edge == 'V':
            gaps += [0, 1]
            rows += [2, 2]
        else:
            assert edge == 'H'
            rows[-1] += 2
            rows += [2]
            gaps += [1]
    return rows, gaps


def determinant(profile, h7):
    rows, gaps = profile
    size = len(rows)
    x, y = [0] * size, [0] * size
    x[-1] = rows[-1]
    for i in range(size - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    def entry(index):
        if index < 0:
            return 0, 0
        if index == 0:
            return 1, 0
        if index == 1:
            return 0, 1
        return ({2: 2, 4: 7, 7: h7}.get(index, index**3 + index + 3), 0)
    matrix = [[entry(a - b) for b in y] for a in x]
    dp = [(0, 0)] * (1 << size)
    dp[0] = (1, 0)
    for mask in range((1 << size) - 1):
        row = mask.bit_count()
        if dp[mask] == (0, 0):
            continue
        for col in range(size):
            if mask >> col & 1:
                continue
            term = mul(dp[mask], matrix[row][col])
            if (mask >> (col + 1)).bit_count() % 2:
                term = -term[0], -term[1]
            target = mask | (1 << col)
            dp[target] = add(dp[target], term)
    return dp[-1]


def defect(h7):
    edges = 'HVVH'
    f = determinant(tile_word(edges), h7)
    W = determinant(tile_word('H'), h7)
    E2 = determinant(tile_word(edges + edges[1:]), h7)
    beta = determinant(tile_word(edges + 'H' + edges), h7)
    u = mul(beta, power(f, -2))
    rho = mul(power(u, -1), power((1 - u[0], -u[1]), 4))
    theta = add(mul(power(f, 2), power(mul(E2, power(f, -2)), 5)), (-rho[0], -rho[1]))
    assert f[0] == 4 * 7**2 * 3**2 and W[0] == 4 * 7
    assert u[0] == F(7, 4)
    assert F(f[0]**2, W[0]**5) == rho[0]
    assert theta[0] == 0
    return theta[1], rho[0]


def run():
    # Two independent original h7 evaluations verify the asserted affineness.
    first, rho = defect(31)
    second, _ = defect(32)
    third, _ = defect(33)
    S = {0: F(7), 1: F(3)}
    P, word, exponents = (0, 1, 1), (0, 1, 1, 0), {0: -1, 1: 4}
    def windows(w):
        return sum((1 / prod(S[w[(i + j) % len(w)]] for j in range(2)) for i in range(len(w))), F(0))
    N2 = 5 * windows(P) - sum(exponents[c] * windows(word + (c,)) for c in (0, 1))
    assert N2 != 0
    expected = -rho * N2
    assert second - first == third - second == expected
    assert first != 0
    assert tile_word('HVVH') != tile_word('HHHH')
    assert tile_word('HVVH') != tile_word('VVVV')
    print('PASS actual b=5, v=2, r=1 original defect: order 1')
    print('PASS derivative in h7:', expected, '; direct consecutive differences agree')


if __name__ == '__main__':
    run()
