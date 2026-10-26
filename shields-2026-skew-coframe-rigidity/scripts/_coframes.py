r"""Exact full-flag Jacobi--Trudi machinery shared by the section checks.

Matrices are constructed from actual decreasing row and column beta lists.
A common beta is retained as one coherent unit, never deleted on input.
All arithmetic is symbolic over the rational numbers.
"""

from functools import lru_cache
from itertools import combinations

import sympy as sp

z = sp.Symbol("z")
theta = sp.Symbol("theta", nonzero=True)
epsilon = sp.Symbol("epsilon")


@lru_cache(maxsize=None)
def letter(index):
    return sp.Symbol(f"h{index}")


def raw(index, unit=theta, scale=sp.S.One):
    if index < 0:
        return sp.S.Zero
    if index == 0:
        return sp.sympify(unit)
    return scale * letter(index)


def matrix(rows, columns, unit=theta, scale=sp.S.One):
    return sp.Matrix([[raw(x - y, unit, scale) for y in columns] for x in rows])


def determinant(board, unit=theta, scale=sp.S.One):
    return sp.expand(matrix(*board, unit, scale).det())


def corner(board, unit=theta, scale=sp.S.One):
    rows, columns = board
    return (-1) ** (len(rows) - 1) * matrix(rows[1:], columns[:-1], unit, scale).det()


def right_coframe(board, unit=theta, scale=sp.S.One):
    rows, columns = board
    if len(rows) == 1:
        return sp.S.One
    proper = matrix(rows[1:], columns[:-1], unit, scale)
    border = sp.Matrix([raw(i, unit, scale) for i in rows[1:]])
    solution = -proper.inv() * border
    return sp.Add(sp.S.One, *(sp.cancel(c) * z ** j for c, j in zip(solution, columns[:-1])))


def left_coframe(board, unit=theta, scale=sp.S.One):
    rows, columns = board
    if len(rows) == 1:
        return sp.S.One
    span = rows[0]
    proper = matrix(rows[1:], columns[:-1], unit, scale)
    border = sp.Matrix([[raw(span - j, unit, scale) for j in columns[:-1]]])
    solution = -border * proper.inv()
    return sp.Add(sp.S.One, *(sp.cancel(c) * z ** (span - i) for c, i in zip(solution, rows[1:])))


def clock(degree, unit=theta):
    return unit + sp.Add(*(letter(i) * z ** i for i in range(1, degree + 1)))


def coefficient(expression, degree):
    return sp.cancel(sp.expand(expression).coeff(z, degree))


def clip(expression, cutoff):
    polynomial = sp.Poly(sp.expand(expression), z)
    return sp.Add(*(c * z ** k[0] for k, c in polynomial.terms() if k[0] < cutoff))


def operator(g, c, argument, span):
    return sp.expand(g * clip(argument * c, span) - c * clip(argument * g, span))


def zero(expression):
    return sp.cancel(expression) == 0


def order(expression):
    polynomial = sp.Poly(sp.expand(expression), z)
    powers = [k[0] for k, c in polynomial.terms() if not zero(c)]
    return min(powers) if powers else sp.oo


def connected(board):
    rows, columns = board
    return (
        bool(rows)
        and len(rows) == len(columns)
        and rows == tuple(sorted(set(rows), reverse=True))
        and columns == tuple(sorted(set(columns), reverse=True))
        and columns[-1] == 0
        and all(x > y for x, y in zip(rows, columns))
        and all(x >= y for x, y in zip(rows[1:], columns[:-1]))
    )


def connected_boards(span):
    positions = tuple(range(1, span))
    for rank in range(span):
        for rows in combinations(positions, rank):
            for columns in combinations(positions, rank):
                board = ((span,) + tuple(reversed(rows)), tuple(reversed(columns)) + (0,))
                if connected(board):
                    yield board


def rotate(board):
    rows, columns = board
    span = rows[0]
    return (tuple(sorted((span - y for y in columns), reverse=True)),
            tuple(sorted((span - x for x in rows), reverse=True)))


def splice(cap, child):
    cap_rows, cap_columns = cap
    child_rows, child_columns = child
    span = child_rows[0]
    return (tuple(sorted({span + x for x in cap_rows} | set(child_rows[1:]), reverse=True)),
            tuple(sorted({span + y for y in cap_columns if y != 0} | set(child_columns), reverse=True)))


def cells(board):
    rows, columns = board
    rank = len(rows)
    return frozenset((i + 1, j)
                     for i, (x, y) in enumerate(zip(rows, columns))
                     for j in range(y - rank + i + 2, x - rank + i + 2))


def from_partitions(lam, mu):
    rank = len(lam)
    mu = tuple(mu) + (0,) * (rank - len(mu))
    shift = mu[-1]
    return (tuple(a + rank - i - 1 - shift for i, a in enumerate(lam)),
            tuple(a + rank - i - 1 - shift for i, a in enumerate(mu)))


def vacancies(board):
    rows, columns = board
    return tuple(i for i in range(1, rows[0]) if i not in rows and i not in columns)


def restore(board, position):
    rows, columns = board
    return (tuple(sorted(rows + (position,), reverse=True)),
            tuple(sorted(columns + (position,), reverse=True)))


def insertion_sign(board, position):
    rows, columns = board
    return (-1) ** (sum(x < position for x in rows) + sum(y < position for y in columns))


def restoration_polynomial(board, position):
    rows, columns = board
    base = matrix(rows, columns, unit=1)
    a = sp.Matrix([raw(x - position, 1) for x in rows])
    b = sp.Matrix([[raw(position - y, 1) for y in columns]])
    return sp.expand(-(b * base.adjugate() * a)[0])


def vacancy_pulse(board, position):
    rows, columns = board
    g = right_coframe(board, unit=0)
    positive = clock(rows[0] - 1, unit=0)
    residual = coefficient(positive * g, position)
    if len(rows) == 1:
        feedback = sp.S.Zero
    else:
        proper = matrix(rows[1:], columns[:-1], unit=0)
        border = sp.Matrix([raw(i - position, unit=0) for i in rows[1:]])
        solved = proper.inv() * border
        feedback = sp.Add(*(sp.cancel(c) * z ** j for c, j in zip(solved, columns[:-1])))
    return sp.expand(-residual * (z ** position - feedback))


def absolute_adjugate(board, unit=theta, scale=sp.S.One):
    rows, columns = board
    adjugate = matrix(rows, columns, unit, scale).adjugate()
    return {(x, y): sp.expand(adjugate[j, i])
            for i, x in enumerate(rows) for j, y in enumerate(columns)}
