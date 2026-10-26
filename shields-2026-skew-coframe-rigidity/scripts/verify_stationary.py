r"""Paper section `sec:stationary` (Finite stationary separation).

Targets `sc:component-column`, `sc:component-remainder`,
`sc:nonzero-remainder`, `sc:top-support`, `sc:positive-power`,
`sc:power-equation`, `cor:stationary-field-descent`, and
`ex:terminal-coframes`.  SymPy derives coframes from their full matrices.
Connected components of span at most four test the remainder; coequal
pairs of span at most four test explicit rational potentials and the
support bound when their selected highest columns agree.  The exact
moving-clock example retains all jets through the supplied horizon.
The script does not decide the universal rational-potential quantifier.
"""

from collections import defaultdict
from itertools import combinations

import sympy as sp

from _coframes import (
    z, theta, letter, determinant, right_coframe, clock, coefficient,
    clip, operator, zero, order, connected_boards,
)


def jet(expression, cutoff):
    return sp.series(expression, z, 0, cutoff).removeO().expand()


def check_component_remainders():
    for span in range(2, 5):
        for board in connected_boards(span):
            g = right_coframe(board)
            h = clock(span)
            k = coefficient(h * g, span)
            assert zero(sp.diff(k, letter(span)) - 1)
            for power in (2, 3, 4):
                remainder = coefficient(h ** power * g, span) - power * theta ** (power - 1) * k
                assert not zero(remainder)
                assert zero(sp.diff(remainder, letter(span)))
    for power in (2, 3, 4):
        # Genuine unit and cell both have coframe one, but different top quotients.
        unit_ratio = theta ** power / theta
        cell_ratio = coefficient(clock(1) ** power, 1) / letter(1)
        assert zero(unit_ratio - theta ** (power - 1))
        assert zero(cell_ratio - power * theta ** (power - 1))
        assert not zero(cell_ratio - unit_ratio)
    print("PASS: component remainders, including the two-cell row at exponent two; unit/cell distinction")


def check_actual_pairs():
    groups = defaultdict(list)
    for span in range(1, 5):
        for board in connected_boards(span):
            groups[(span, determinant(board, unit=1))].append(board)
    pairs = 0
    for (span, _), boards in groups.items():
        for a, b in combinations(boards, 2):
            pairs += 1
            g, c = right_coframe(a), right_coframe(b)
            h = clock(span - 1)
            d = operator(g, c, h, span)
            delta = c - g
            assert not zero(d) and not zero(delta)
            for power in (2, 3, 4):
                for potential in (sp.S.Zero, -power * h ** (power - 1), -h ** (power - 1), jet(1 / (1 + h), 2 * span)):
                    residual = clip(operator(g, c, z * h ** power, span) + z * d * potential, 2 * span)
                    assert not zero(residual)
                    assert zero(operator(g, g, z * h ** power, span))
            y = letter(span - 1)
            if span - 1 in a[0][1:] and span - 1 in b[0][1:]:
                ga, cb = sp.diff(g, y), sp.diff(c, y)
                if zero(ga - cb):
                    least_column = order(ga)
                    assert 1 <= order(delta) <= least_column - 2
    assert pairs > 0
    print("PASS: shifted residuals for explicit potentials on actual coequal pairs through span four")


def check_whole_clock():
    span = 3
    a, b = ((3, 1), (1, 0)), ((3, 2), (2, 0))
    g, c = right_coframe(a), right_coframe(b)
    assert zero(determinant(a) - (letter(1) * letter(2) - theta * letter(3)))
    assert zero(determinant(a) - determinant(b))
    assert zero(g - (1 - letter(1) * z / theta))
    assert zero(c - (1 - letter(2) * z ** 2 / theta))
    low = clock(span - 1)
    d = operator(g, c, low, span)
    expected = letter(2) * (theta * letter(2) - letter(1) ** 2) * z ** 4 / theta ** 2
    assert zero(d - expected) and order(d) == 2 * span - 2
    amplitude = sp.Rational(7, 3)
    neutral_potential = 1 / (1 + theta)
    full = clock(2 * span - 1)
    moving_potential = jet(1 / (1 + full), 2 * span)
    assert zero(moving_potential.subs(z, 0) - neutral_potential)
    assert zero(clip((1 + full) * moving_potential, 2 * span) - 1)
    assert not zero(coefficient(moving_potential, 1))
    assert zero(clip(z * d * moving_potential, 2 * span - 1))
    terminal = coefficient(z * d * moving_potential, 2 * span - 1)
    assert zero(terminal - coefficient(d, 2 * span - 2) * neutral_potential)
    assert not zero(terminal)
    for power in (2, 3, 4):
        assert zero(operator(g, c, full, span) - d)
        assert zero(operator(g, c, z * full ** power, span) - operator(g, c, z * low ** power, span))
        assert zero(clip(amplitude * operator(g, c, z * full ** power, span) + z * d * moving_potential, 2 * span)
                    - clip(amplitude * operator(g, c, z * low ** power, span) + z * d * jet(1 / (1 + low), 2 * span), 2 * span))
    tail_effect = jet(z * d * (1 / (1 + full) - 1 / (1 + low)), 2 * span + 3)
    assert order(tail_effect) == 2 * span + 2
    # The dependent inverse moves: freezing it violates the homomorphism equation.
    assert not zero(clip((1 + full) * neutral_potential, 2 * span) - 1)
    print("PASS: exact M=3 coframes, terminal potential coefficient, moving inverse, and full-clock tail compatibility")


if __name__ == "__main__":
    check_component_remainders()
    check_actual_pairs()
    check_whole_clock()
    print("ALL PASS")
