r"""Paper section `sec:coframe-coordinates` (Complete coframe coordinates).

Targets `sc:coframe-definition`, `sc:row-degree`, `sc:atlas`,
`sc:atlas-support`, `sc:atlas-inverse`, `sc:coprime`, `sc:coequal-data`,
`sc:defect-orders`, `sc:exact-shift-cap`, and `lem:cap-recognition`.
SymPy constructs each determinant and native solve from full flags.
The census covers connected spans one through four; weak-cap checks use
explicit feasible lists, including units and disconnected blocks.
These exact finite checks are not proofs of the uniform statements.
"""

from collections import defaultdict
from itertools import combinations

import sympy as sp

from _coframes import (
    z, theta, letter, matrix, determinant, corner, right_coframe,
    left_coframe, clock, coefficient, clip, operator, zero, order,
    connected, connected_boards, rotate, from_partitions,
)


def check_connected_coordinates():
    groups = defaultdict(list)
    for span in range(1, 5):
        h = clock(span)
        for board in connected_boards(span):
            assert connected(board)
            rows, columns = board
            whole = determinant(board)
            kappa = corner(board)
            assert not zero(kappa)
            assert zero(sp.diff(whole, letter(span)) - kappa)
            assert sp.Poly(whole, *(letter(i) for i in range(1, span + 1))).total_degree() == len(rows)
            g = right_coframe(board)
            p = clip(h * g, span)
            assert coefficient(g, 0) == 1
            assert all((not zero(coefficient(g, j))) == (j in columns[:-1]) for j in range(1, span))
            assert all(zero(coefficient(p, i)) == (i in rows[1:]) for i in range(1, span))
            assert zero(whole - kappa * coefficient(h * g, span))
            recovered = sp.series(p / g, z, 0, span).removeO()
            assert zero(recovered - clip(h, span))
            assert zero(left_coframe(board) - right_coframe(rotate(board)))
            if g != 1:
                assert sp.Poly(g, z).degree() > 0
                factors = sp.factor_list(g, z)[1]
                assert len(factors) == 1 and factors[0][1] == 1
                assert sp.degree(sp.gcd(sp.together(g), sp.together(p)), z) == 0
            groups[(span, sp.expand(whole.subs(theta, 1)))].append(board)

            # Independent atlas coordinates are reconstructed before the native solve.
            native = {j: sp.Symbol(f"g{j}") for j in columns[:-1]}
            available = {i: sp.Symbol(f"p{i}") for i in range(1, span) if i not in rows[1:]}
            generic_g = 1 + sum(v * z ** j for j, v in native.items())
            generic_p = theta + sum(v * z ** i for i, v in available.items())
            generic_h = sp.series(generic_p / generic_g, z, 0, span).removeO()
            substitution = {letter(i): coefficient(generic_h, i) for i in range(1, span)}
            assert zero(g.subs(substitution, simultaneous=True) - generic_g)

    distinct_pairs = 0
    for (span, _), boards in groups.items():
        for a, b in combinations(boards, 2):
            distinct_pairs += 1
            assert a != b
            assert zero(determinant(a) - determinant(b))
            g, c = right_coframe(a), right_coframe(b)
            assert not zero(g - c)
            d = operator(g, c, clock(span - 1), span)
            assert not zero(d)
            assert span + 1 <= order(d)
            assert sp.Poly(d, z).degree() <= 2 * span - 2
            assert sp.degree(sp.gcd(sp.together(g), sp.together(c)), z) == 0
    assert distinct_pairs > 0
    print("PASS: complete coordinates, independent atlas, and coequal defects through span four")


def check_row_boundaries():
    cases = [((2, 1), (1, 0)), ((3, 2, 1), (2, 2, 0)),
             ((4, 4, 2), (2, 0, 0)), ((2, 1), (0, 0))]
    for lam, mu in cases:
        board = from_partitions(lam, mu)
        whole = determinant(board)
        positive = tuple(letter(i) for i in range(1, board[0][0] + 1))
        assert sp.Poly(whole, *positive).total_degree() == sum(x > y for x, y in zip(lam, mu))
    print("PASS: positive row degree includes disconnected and internal-empty-row boundaries")


def check_weak_caps():
    cases = [((1,), (1,)), ((2,), (1,)), ((2, 1), (2, 1)),
             ((3, 1), (2, 1)), ((4, 2), (3, 1)), ((4, 3), (2, 1))]
    for rows, columns in cases:
        assert tuple(sorted(set(rows), reverse=True)) == rows
        assert tuple(sorted(set(columns), reverse=True)) == columns
        assert min(columns) > 0 and all(x >= y for x, y in zip(rows, columns))
        a = matrix(rows, columns, unit=1)
        denominator = a.det()
        border = sp.Matrix([letter(i) for i in rows])
        powers = sp.Matrix([[z ** j for j in columns]])
        v = a.adjugate() * border
        numerator = sp.expand(denominator - (powers * v)[0])
        assert denominator != 0
        assert sp.expand(numerator).coeff(z, 0) == denominator
        assert all(coefficient(numerator, j) != 0 for j in columns)
        assert {j for j in range(1, max(columns) + 1) if coefficient(numerator, j) != 0} == set(columns)
        factors = sp.factor_list(numerator)[1]  # Joint polynomial ring, not just the z-field.
        assert len(factors) == 1 and factors[0][1] == 1
        assert sp.gcd(numerator, denominator) in (1, -1)
        head_column = a.adjugate()[:, 0]
        assert zero(-sp.diff(numerator, letter(rows[0])) - (powers * head_column)[0])
        if len(rows) > 1:
            tail = a[1:, 1:]
            tail_v = tail.adjugate() * border[1:, :]
            for j in range(1, len(rows)):
                assert zero((head_column[0] * v[j] - head_column[j] * v[0]) / denominator - tail_v[j - 1])
    unit_board = ((3, 2, 1), (2, 1, 0))
    assert zero(right_coframe(unit_board, unit=1) - (1 - letter(1) * z + (letter(1) ** 2 - letter(2)) * z ** 2))
    print("PASS: joint weak-cap numerators, absolute support, and recursive tail recovery")


def check_shift_cap():
    span = 4
    g = right_coframe(((4, 2), (1, 0)))
    c = right_coframe(((4, 3), (2, 0)))
    u = clock(span + 1) ** 2
    lhs = operator(g, c, z * u, span) - z * operator(g, c, u, span)
    rhs = -z ** span * (g * coefficient(u * c, span - 1) - c * coefficient(u * g, span - 1))
    assert zero(lhs - rhs)
    assert not zero(rhs)
    # Literal equal coframes have zero whole cap without separate scalar zeros.
    scalar = coefficient(u * g, span - 1)
    assert not zero(scalar)
    assert zero(operator(g, g, z * u, span) - z * operator(g, g, u, span))
    print("PASS: exact shift correction is a whole cap polynomial")


if __name__ == "__main__":
    check_connected_coordinates()
    check_row_boundaries()
    check_weak_caps()
    check_shift_cap()
    print("ALL PASS")
