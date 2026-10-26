r"""Paper section `sec:unit-restoration` (Complete unit restoration).

Targets `sc:unit-expansion`, `sc:core-leading-term`, `sc:vacancy-pulse`,
`sc:finite-injectivity`, `sc:restoration-polynomial`, `sc:bordered-grade`,
`sc:linearized-cap`, `sc:splice-nonzero`, and `sc:whole-unit-series`.
SymPy derives bordered determinants and full native solves independently.
Constant-weight injectivity is tested by coefficient rank over Q, not by
rank over the raw rational field.  Native feedback and rational-weight
boundary controls deliberately retain the distinction between these fields.
All enumerations are finite and do not establish the uniform inductions.
"""

import sympy as sp

from _coframes import (
    z, theta, epsilon, letter, determinant, right_coframe, clock,
    coefficient, clip, operator, zero, connected, connected_boards,
    rotate, splice, vacancies, restore, insertion_sign,
    restoration_polynomial, vacancy_pulse, absolute_adjugate,
)

CELL = ((1,), (0,))


def polynomial_observation_rank(observations, variables):
    """Use distinct rows for each observation and each raw monomial."""
    columns = []
    keys = set()
    for pair in observations:
        column = {}
        for channel, polynomial in enumerate(pair):
            for monomial, value in sp.Poly(polynomial, *variables).terms():
                column[(channel, monomial)] = value
                keys.add((channel, monomial))
        columns.append(column)
    return sp.Matrix([[column.get(key, 0) for column in columns] for key in sorted(keys)]).rank()


def check_borders_and_pulses():
    feedback_seen = False
    for span in range(2, 5):
        for board in connected_boards(span):
            rows, columns = board
            if set(rows) & set(columns):
                continue
            base = determinant(board, unit=1)
            g = right_coframe(board, unit=0)
            positive = clock(span - 1, unit=0)
            for position in vacancies(board):
                restored = restore(board, position)
                assert connected(restored)
                sign = insertion_sign(board, position)
                variation = restoration_polynomial(board, position)
                actual = determinant(restored, unit=theta, scale=epsilon)
                predicted = sign * (theta * epsilon ** len(rows) * base
                                    + epsilon ** (len(rows) + 1) * variation)
                assert zero(actual - predicted)
                moving = right_coframe(restored, unit=1, scale=epsilon)
                series = sp.series(sp.cancel(moving), epsilon, 0, 2).removeO().expand()
                assert zero(series.coeff(epsilon, 0) - g)
                pulse = vacancy_pulse(board, position)
                assert zero(series.coeff(epsilon, 1) - pulse)
                assert coefficient(pulse, 0) == 0
                assert zero(coefficient(pulse, position) + coefficient(positive * g, position))
                assert all(zero(coefficient(positive * pulse, i)) for i in rows[1:])
                bare = coefficient(pulse, position) * z ** position
                if not zero(pulse - bare):
                    feedback_seen = True
                    assert any(not zero(coefficient(positive * bare, i)) for i in rows[1:])
    assert feedback_seen
    print("PASS: complete bordered grade and vacancy pulses include old-column feedback")


def check_finite_injectivity():
    for span in range(2, 4):
        unknowns = sp.symbols(f"d1:{span}")
        delta = sum(value * z ** i for i, value in enumerate(unknowns, 1))
        for board in connected_boards(span):
            rows, columns = board
            for unit, shifts in [(theta, range(span)), (0, range(span - 1))]:
                if unit == 0 and set(rows) & set(columns):
                    continue
                g = right_coframe(board, unit=unit)
                h = clock(span - 1, unit=unit)
                native = [coefficient(h * delta, i) for i in rows[1:]]
                for shift in shifts:
                    wedge = operator(g, delta, z ** shift * h, span)
                    equations = native + [coefficient(wedge, i) for i in range(2 * span - 1)]
                    system, _ = sp.linear_eq_to_matrix(equations, unknowns)
                    assert system.rank() == span - 1
    # The zero-free bound stops before a shift that clips away the whole positive input.
    span = 4
    h = clock(span - 1, unit=0)
    assert z != 0
    assert zero(operator(1, z, z ** (span - 1) * h, span))
    assert not zero(operator(1, z, z ** (span - 2) * h, span))
    print("PASS: finite native-equation injectivity and its zero-free shift boundary")


def check_constant_weights():
    caps = (CELL, ((2,), (0,)), ((3, 2), (1, 0)))
    nonempty = 0
    for span in range(2, 5):
        for child in connected_boards(span):
            if set(child[0]) & set(child[1]):
                continue
            positions = vacancies(child)
            if not positions:
                continue
            for cap in caps:
                assert not (set(cap[0]) & set(cap[1]))
                joined = splice(cap, child)
                assert connected(joined) and not (set(joined[0]) & set(joined[1]))
                assert all(b in vacancies(joined) for b in positions)
                observations = [(restoration_polynomial(child, b), restoration_polynomial(joined, b))
                                for b in positions]
                variables = tuple(letter(i) for i in range(1, joined[0][0] + 1))
                assert polynomial_observation_rank(observations, variables) == len(positions)
                nonempty += 1
    assert nonempty > 0

    # A genuine two-observation example: the child alone has a constant kernel.
    child = ((3,), (0,))
    joined = splice(CELL, child)
    child_variation = restoration_polynomial(child, 1) - restoration_polynomial(child, 2)
    cap_variation = restoration_polynomial(joined, 1) - restoration_polynomial(joined, 2)
    assert zero(child_variation)
    assert zero(cap_variation - (letter(2) ** 2 - letter(1) * letter(3)))
    assert not zero(cap_variation)

    # Raw-rational weights are outside sc:linearized-cap, even on zero-free rows.
    child = ((4,), (0,))
    joined = splice(CELL, child)
    first = sp.Matrix([restoration_polynomial(child, b) for b in (1, 2, 3)])
    second = sp.Matrix([restoration_polynomial(joined, b) for b in (1, 2, 3)])
    weights = first.cross(second)
    assert any(not zero(value) for value in weights)
    assert any(value.free_symbols for value in weights)
    assert zero(first.dot(weights)) and zero(second.dot(weights))
    # The native pulse equations nevertheless allow these raw-dependent weights.
    tangent = sum((weight * vacancy_pulse(child, b) for weight, b in zip(weights, (1, 2, 3))), sp.S.Zero)
    assert not zero(tangent)
    assert coefficient(tangent, 0) == 0
    print("PASS: constant-weight two-observation rank; a nonconstant-weight kernel is excluded by hypothesis")


def first_epsilon_grade(expression):
    polynomial = sp.Poly(sp.expand(expression), epsilon)
    return min((power[0] for power, value in polynomial.terms() if value != 0), default=sp.oo)


def check_cell_splice_grades():
    nonself_core_seen = False
    self_core_seen = False
    for span in range(3, 5):
        for board in connected_boards(span):
            mate = rotate(board)
            if board == mate:
                continue
            common = set(board[0]) & set(board[1])
            core = (tuple(x for x in board[0] if x not in common),
                    tuple(y for y in board[1] if y not in common))
            assert connected(core) and not (set(core[0]) & set(core[1]))
            k = len(core[0])
            core_self = core == rotate(core)
            self_core_seen |= core_self
            nonself_core_seen |= not core_self
            lam = k + int(core_self)
            cell_difference = determinant(splice(board, CELL), scale=epsilon) - determinant(splice(CELL, board), scale=epsilon)
            assert first_epsilon_grade(cell_difference) == lam
            left = absolute_adjugate(board, scale=epsilon)
            right = absolute_adjugate(mate, scale=epsilon)
            grades = [first_epsilon_grade(left.get(key, 0) - right.get(key, 0)) for key in left.keys() | right.keys()]
            assert min(grades) == lam - 1
    assert nonself_core_seen and self_core_seen
    print("PASS: first whole cell-splice and absolute-adjugate grades in both core cases")


if __name__ == "__main__":
    check_borders_and_pulses()
    check_finite_injectivity()
    check_constant_weights()
    check_cell_splice_grades()
    print("ALL PASS")
