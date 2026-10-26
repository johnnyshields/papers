r"""Paper section `sec:unshifted` (Unshifted opposite-end exclusion).

Targets `ph:unshifted-exclusion` and `ph:first-D`, including the full
highest-letter expansion, genuine units, cell endpoints, the exponent-two
two-cell-row exception, and the final span-seven/eight flag exhaustion.
SymPy computes complete right/left coframes from one board and its rotation.
The universal statement is not inferred from these bounded exact checks.
"""

from itertools import combinations

import sympy as sp

from _coframes import (
    z, theta, letter, determinant, corner, right_coframe, left_coframe,
    clock, coefficient, clip, operator, zero, connected, connected_boards,
    rotate, splice,
)

CELL = ((1,), (0,))


def unshifted(board, power):
    span = board[0][0]
    h = clock(span - 1)
    g, c = right_coframe(board), left_coframe(board)
    d = operator(g, c, h, span)
    return clip(operator(g, c, h ** power, span) - power * h ** (power - 1) * d, 2 * span)


def check_opposite_ends():
    nonself = 0
    for span in range(3, 5):
        for board in connected_boards(span):
            mate = rotate(board)
            assert zero(determinant(board) - determinant(mate))
            assert zero(left_coframe(board) - right_coframe(mate))
            assert zero(unshifted(board, 1))  # The excluded exponent-one boundary.
            for power in (2, 3, 4):
                assert zero(unshifted(board, power)) == (board == mate)
            if board == mate:
                continue
            nonself += 1
            h = clock(span - 1)
            g, c = right_coframe(board), left_coframe(board)
            d = operator(g, c, h, span)
            kappa = corner(board)
            whole = determinant(board)
            top = sp.solve(whole, letter(span))[0]
            j2 = determinant(splice(board, CELL)) - determinant(splice(CELL, board))
            neutral_j2 = sp.cancel(j2.subs(letter(span), top))
            assert not zero(neutral_j2)
            assert zero(coefficient(d, span + 1) + neutral_j2 / kappa)
    assert nonself > 0
    print("PASS: actual opposite-end exclusion, first defect coefficient, and exponent-one boundary")


def check_highest_letter_expansion():
    boards = [((3, 1), (1, 0)), ((4, 3, 1), (2, 1, 0)),
              ((5, 4, 2), (2, 1, 0))]
    for board in boards:
        assert connected(board) and board != rotate(board)
        span = board[0][0]
        m = span - 1
        y = letter(m)
        h = clock(span - 1) - y * z ** m
        g, c = right_coframe(board), left_coframe(board)
        g0, c0 = g.subs(y, 0), c.subs(y, 0)
        a, b = sp.diff(g, y), sp.diff(c, y)
        assert zero(g - g0 - y * a) and zero(c - c0 - y * b)
        assert zero(sp.diff(a, y)) and zero(sp.diff(b, y))
        delta = g0 - c0
        for power in (2, 3):
            def defect(first, second):
                return clip(operator(first, second, h ** power, span)
                            - power * h ** (power - 1) * operator(first, second, h, span), 2 * span)
            constant = defect(g0, c0)
            linear = defect(a, c0) + defect(g0, b) + power * (theta ** (power - 1) - h ** (power - 1)) * z ** m * delta
            quadratic = defect(a, b) + power * (theta ** (power - 1) - h ** (power - 1)) * z ** m * (a - b)
            rebuilt = clip(constant + y * linear + y ** 2 * quadratic, 2 * span)
            assert zero(unshifted(board, power) - rebuilt)
    print("PASS: whole highest-letter expansion for unit, disconnected, and connected proper corners")


def check_exceptional_components():
    for power in (2, 3, 4):
        unit_alpha = coefficient(clock(1) ** power - power * theta ** (power - 1) * clock(1), 1)
        unit_alpha -= power * (power - 1) * theta ** (power - 2) * letter(1) * theta
        assert zero(unit_alpha + power * (power - 1) * theta ** (power - 1) * letter(1))
        for span in range(1, 5):
            for board in connected_boards(span):
                g = right_coframe(board)
                h = clock(span + 1)
                k = coefficient(h * g, span)
                alpha = coefficient((h ** power - power * theta ** (power - 1) * h) * g, span + 1)
                alpha -= power * (power - 1) * theta ** (power - 2) * letter(1) * k
                exceptional = power == 2 and board == ((2,), (0,))
                assert zero(alpha) == exceptional
                if span >= 2:
                    assert zero(sp.diff(alpha, letter(span)))
                if span == 1:
                    assert zero(alpha + sp.binomial(power, 2) * theta ** (power - 2) * letter(1) ** 2)
    possibilities = set()
    for board in connected_boards(3):
        value = sp.factor(coefficient(right_coframe(board), 2))
        possibilities.add(value)
        assert not zero(letter(1) ** 2 * value - 2 * letter(2) ** 2)
    expected = {sp.S.Zero, -letter(2) / theta,
                (letter(1) ** 2 - theta * letter(2)) / theta ** 2}
    assert len(possibilities) == len(expected)
    assert all(any(zero(value - target) for target in expected) for value in possibilities)
    print("PASS: unit/cell component formulas and the unique two-cell-row exponent-two exception")


def check_small_span_flags():
    witnessed = set()
    for span in (7, 8):
        interior = tuple(range(4, span - 3))
        for rank in range(len(interior) + 1):
            for rows in combinations(interior, rank):
                for columns in combinations(interior, rank):
                    board = (tuple(sorted((span, span - 1, 3) + rows, reverse=True)),
                             tuple(sorted((span - 3, 1, 0) + columns, reverse=True)))
                    assert connected(board)
                    assert board == rotate(board)
                    witnessed.add((span, rows, columns))
    assert (7, (), ()) in witnessed
    assert (8, (), ()) in witnessed and (8, (4,), (4,)) in witnessed
    # Beyond that exhaustion window, an off-center intervening unit is possible.
    board = ((9, 8, 4, 3), (6, 4, 1, 0))
    assert connected(board) and board != rotate(board)
    assert not zero(unshifted(board, 2))
    print("PASS: span-seven/eight balanced flags are self-rotating; an off-center-unit boundary at span nine is excluded algebraically")


if __name__ == "__main__":
    check_opposite_ends()
    check_highest_letter_expansion()
    check_exceptional_components()
    check_small_span_flags()
    print("ALL PASS")
