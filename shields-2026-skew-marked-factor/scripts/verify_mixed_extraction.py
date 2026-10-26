r"""Paper section `sec:mixed-extraction` (Recovering mixed ribbon factors).

Checks `rt:mixed-readout`, `rt:outer-triangle`, `eq:mixed-terminal-evaluation`,
and `lem:terminal-readout` on every mixed legal mark on inners of three
through five cells and every ribbon outer of one through four cells.
A six-cell inner and its physical transforms add a nonempty hatted mark.
The decoder receives only (P, p); factor functions, integer phase content,
all character values, and the whole signed normalizer are checked against
independently constructed cell diagrams.  SymPy arithmetic is exact.
"""

from functools import lru_cache

import sympy as sp

from schur_tools import (antitranspose, apply, compose, compositions, dimensions,
                         from_profile, h, hats, legal_marks, rotate, schur,
                         shapes, z_value)
from _weighted_readout import (alphabet_value, coarse, decode_mixed, involution,
                               weighted, word)


@lru_cache(None)
def refines(fine, coarse_parts):
    """Assign each fine part to a coarse part, independently of differentiation."""
    if not fine:
        return not coarse_parts
    first, rest = fine[0], fine[1:]
    for i, target in enumerate(coarse_parts):
        if first > target:
            continue
        remaining = list(coarse_parts)
        remaining[i] -= first
        bins = tuple(sorted((v for v in remaining if v), reverse=True))
        if refines(rest, bins):
            return True
    return False


def main():
    inners = {E for n in range(3, 6) for E in shapes(n)}
    extra = from_profile((4, 2), (1,))
    inners.update((extra, rotate(extra), antitranspose(extra), rotate(antitranspose(extra))))
    outers = [from_profile(rows, (0,) * (len(rows) - 1))
              for n in range(1, 5) for rows in compositions(n)]
    cases = set()
    recovered_phases = set()
    normalizer_with_hat = False
    charts = characters = 0
    for E in sorted(inners, key=lambda E: (len(E), sorted(E))):
        for W, v, case in legal_marks(E):
            if case not in ('c', 'd'):
                continue
            cases.add(case)
            period = v[1] - v[0]
            O, What, Ohat = hats(E, W, v)
            rho = period - dimensions(O)[2]
            assert 0 < rho < period
            A, B, C = (schur(X) for X in (W, What, Ohat))
            chi = (-1) ** (-v[0]) * A * B * C
            normalizer_with_hat |= bool(What)
            op = lambda f, k: coarse(f, k, period, rho)
            for D in outers:
                m = len(D)
                rows, cols, diagonals = dimensions(D)
                assert diagonals == m
                Q = schur(D)
                parent = compose(D, E, W, v, case)
                P = schur(parent)
                got = decode_mixed(P, period)
                assert got['area'] == m
                assert got['inner'] == schur(E)
                assert got['outer'] == Q
                assert got['rho'] == rho and got['chi'] == sp.expand(chi)
                recovered_phases.add(int(got['rho']))
                T, U = got['terminal'], got['penultimate']
                assert T != 0 and weighted(T, period) == 0
                assert sp.expand(U * rho * chi - T * schur(E)) == 0

                # Independent alphabet specialization and actual composition modifier.
                x = sp.Rational(rho, period)
                terminal_scalar = sp.factorial(m) * period ** m * alphabet_value(Q, x)
                assert terminal_scalar != 0
                assert terminal_scalar == word(Q, [1] * m, op)
                assert alphabet_value(Q, x) == (-1) ** m * alphabet_value(involution(Q), -x)
                normalizer = (-1) ** (rows - 1) * A ** (m - rows) * B ** (m - cols) * C ** (m - diagonals)
                assert sp.expand(normalizer * T - chi ** m * terminal_scalar) == 0
                assert sp.cancel(T / terminal_scalar) == sp.cancel(chi ** m / normalizer)
                assert sp.expand(got['normalized_outer'] * terminal_scalar - Q) == 0

                # Every normalized character is also read by Hall differentiation.
                nus = got['partitions']
                for i, nu in enumerate(nus):
                    expected_character = apply(Q, nu)
                    recovered_character = apply(got['outer'], nu)
                    assert recovered_character == expected_character
                    assert got['ratios'][nu] == word(Q, nu, op) / terminal_scalar
                    assert got['matrix'][i, i] == rho ** len(nu) * z_value(nu)
                    for j, lam in enumerate(nus):
                        if not refines(nu, lam):
                            assert got['matrix'][i, j] == 0
                        if len(nu) == len(lam) and nu != lam:
                            assert got['matrix'][i, j] == 0
                    characters += 1
                charts += 1
    assert cases == {'c', 'd'} and {1, 2} <= recovered_phases
    assert normalizer_with_hat

    # Weighted words genuinely require an order; Hall-adjoint commutativity is inapplicable.
    op = lambda f, k: coarse(f, k, 3, 2)
    assert word(h(3), (1, 2), op) - word(h(3), (2, 1), op) == 6
    E = from_profile((2, 1), (0,))
    W, v, case = next(mark for mark in legal_marks(E) if mark[2] == 'd')
    column = from_profile((1, 1), (0,))
    P = schur(compose(column, E, W, v, case))
    got = decode_mixed(P, 2)
    assert got['outer'] == schur(column) and got['outer'] != involution(schur(column))
    assert got['chi'] == -h(1) and got['chi'] != h(1)
    assert sp.expand(got['penultimate'] * h(1) - got['terminal'] * schur(E)) != 0
    print('PASS: mixed cell charts and complete character comparisons:', charts, characters)
    print('PASS: fractional alphabet, integer phase content, full signed normalizers, and ordered inversion')
    print('PASS: wrong involution, wrong local sign, and operator-order controls')
    print('ALL PASS')


if __name__ == '__main__':
    main()
