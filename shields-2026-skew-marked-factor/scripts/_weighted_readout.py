r"""Exact operators for `sec:weighted-action` and `sec:mixed-extraction`.

Reuse the cell geometry and Jacobi--Trudi implementation in schur_tools.
The mixed decoder accepts only a parent polynomial and a supplied period;
normalizers, phases, diagrams, and outer area are not decoder inputs.
"""

from functools import lru_cache

import sympy as sp

from schur_tools import (compose, delta, determinant, h, lambda_mu, partitions,
                         power_sum, primitive)


def weighted(poly, k):
    """V_k: the terminal generator h_k has zero weighted derivative."""
    assert k > 0
    poly = sp.sympify(poly)
    return sp.expand(sum((int(x.name[1:]) - k) * h(int(x.name[1:]) - k)
                         * sp.diff(poly, x) for x in poly.free_symbols
                         if int(x.name[1:]) > k))


def coarse(poly, k, period, offset):
    return sp.expand(period * weighted(poly, k) + offset * delta(poly, k))


def word(poly, indices, operator):
    """Apply indices in their listed order, first listed acting first."""
    for k in indices:
        poly = operator(poly, k)
    return sp.expand(poly)


@lru_cache(None)
def elementary(j):
    if j == 0:
        return sp.Integer(1)
    return sp.expand(sum((-1) ** (i - 1) * h(i) * elementary(j - i)
                         for i in range(1, j + 1)))


def involution(poly):
    poly = sp.sympify(poly)
    return sp.expand(poly.xreplace({x: elementary(int(x.name[1:]))
                                   for x in poly.free_symbols}))


def full_betas(cells):
    lam, mu = lambda_mu(cells)
    n = len(lam)
    return (tuple(lam[i] + n - i - 1 for i in range(n)),
            tuple(mu[i] + n - i - 1 for i in range(n)))


def beta_det(X, Y):
    """Leave both lists in their original orders, including moved indices."""
    return determinant(tuple(tuple(x - y for y in Y) for x in X))


def beta_weighted(X, Y, k):
    rows = [beta_det(X[:i] + (x - k,) + X[i + 1:], Y)
            for i, x in enumerate(X)]
    cols = [beta_det(X, Y[:j] + (y + k,) + Y[j + 1:])
            for j, y in enumerate(Y)]
    return sp.expand(sum((x - k) * f for x, f in zip(X, rows))
                     - sum(y * f for y, f in zip(Y, cols))), rows, cols


@lru_cache(None)
def row_image(E, W, v, case, j):
    from schur_tools import schur
    if j == 0:
        return sp.Integer(1)
    row = frozenset((0, col) for col in range(j))
    return sp.expand(schur(W) ** (j - 1) * schur(compose(row, E, W, v, case)))


def composition_map(poly, E, W, v, case, read_outer=True):
    """Phi is Psi composed with omega only for the ordinary vertical reading."""
    poly = sp.sympify(poly)
    if case == 'b' and read_outer:
        poly = involution(poly)
    return sp.expand(poly.xreplace({x: row_image(E, W, v, case, int(x.name[1:]))
                                   for x in poly.free_symbols}))


def mixed_sign(D):
    """Count vertical steps within the actual northwest boundary ribbons."""
    lowest = {}
    for i, j in D:
        content = j - i
        lowest[content] = min(i, lowest.get(content, i))
    northbound = sum((i - 1, j) in D
                     and i - lowest[j - i] == i - 1 - lowest[j - i + 1]
                     for i, j in D)
    return (-1) ** northbound


def power_product(nu):
    return sp.expand(sp.prod(power_sum(j) for j in nu))


def integer_content(poly):
    variables = sorted(poly.free_symbols, key=lambda x: int(x.name[1:]))
    if not variables:
        return abs(sp.Integer(poly))
    return abs(sp.Poly(poly, *variables, domain=sp.ZZ).content())


def alphabet_value(poly, x):
    """Specialization from complete generators, independent of operator words."""
    return sp.expand(poly.xreplace({v: sp.rf(x, int(v.name[1:]))
                                   / sp.factorial(int(v.name[1:]))
                                   for v in poly.free_symbols}))


def decode_mixed(P, period):
    """Recover a mixed ribbon chart from (P, period), under that supplied domain."""
    if period <= 0 or P == 0 or delta(P, period) != 0:
        raise ValueError('Not in the mixed supplied-period domain')
    tail = [P]
    while True:
        following = weighted(tail[-1], period)
        if following == 0:
            break
        tail.append(following)
    area = len(tail) - 1
    if area < 1:
        raise ValueError('No nonzero mixed weighted tail at this period')
    terminal, previous = tail[-1], tail[-2]
    inner = primitive(sp.cancel(previous / sp.gcd(previous, terminal)))
    first = weighted(inner, period)
    rho = integer_content(first)
    if not 0 < rho < period:
        raise ValueError('Recovered phase difference is outside the mixed domain')
    chi = sp.expand(first / rho)
    assert sp.expand(previous * rho * chi - terminal * inner) == 0

    nus = sorted(partitions(area), key=lambda nu: (len(nu), nu))
    basis = [power_product(nu) for nu in nus]
    op = lambda f, k: coarse(f, k, period, rho)
    matrix = sp.Matrix([[word(f, nu, op) for f in basis] for nu in nus])
    ratios = {nu: sp.cancel(word(P, [period * k for k in nu], weighted) / terminal)
              for nu in nus}
    if any(not value.is_Rational for value in ratios.values()):
        raise ValueError('Nonrational mixed outer ratio')
    coefficients = matrix.LUsolve(sp.Matrix([ratios[nu] for nu in nus]))
    normalized = sp.expand(sum(c * f for c, f in zip(coefficients, basis)))
    outer = primitive(normalized)
    return {'area': area, 'inner': inner, 'outer': outer, 'rho': rho,
            'chi': chi, 'terminal': terminal, 'penultimate': previous,
            'ratios': ratios, 'matrix': matrix, 'partitions': nus,
            'normalized_outer': normalized}
