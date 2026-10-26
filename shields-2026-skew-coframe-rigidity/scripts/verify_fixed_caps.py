r"""Paper section `sec:fixed-caps` (Rigidity with the same literal cap).

Targets `sc:splice-flags`, `sc:splice-identity`, `sc:fixed-cap`,
`ex:same-cell-cap`, and `fig:cell-splice`.  SymPy rebuilds actual splices
from complete flags and compares their determinants with the two-coframe
coefficient formula.  Connected children have span at most four; the
literal caps are a cell, a two-cell row, and a two-cell column.
The finite sweep corroborates the mechanism, not the uniform induction.
"""

from collections import defaultdict
from itertools import combinations

from _coframes import (
    z, letter, determinant, corner, right_coframe, left_coframe, clock,
    coefficient, zero, connected, connected_boards, rotate, splice, cells,
)

CELL = ((1,), (0,))
HOOK = ((3, 1), (1, 0))
MATE = ((3, 2), (2, 0))


def check_splice_identity():
    caps = (CELL, ((2,), (0,)), ((2, 1), (1, 0)))
    groups = defaultdict(list)
    for span in range(1, 5):
        for child in connected_boards(span):
            groups[(span, determinant(child, unit=1))].append(child)
            for cap in caps:
                joined = splice(cap, child)
                assert connected(cap) and connected(child) and connected(joined)
                assert joined[0][0] == span + cap[0][0]
                assert len(cells(joined)) == len(cells(cap)) + len(cells(child))
                g = right_coframe(child, unit=1)
                c = left_coframe(cap, unit=1)
                rhs = corner(cap, unit=1) * corner(child, unit=1) * coefficient(
                    clock(span + cap[0][0], unit=1) * c * g, span + cap[0][0])
                assert zero(determinant(joined, unit=1) - rhs)
    pairs = 0
    for boards in groups.values():
        for first, second in combinations(boards, 2):
            pairs += 1
            assert first != second
            for cap in caps:
                assert not zero(determinant(splice(cap, first), unit=1)
                                - determinant(splice(cap, second), unit=1))
    assert pairs > 0
    print("PASS: actual 00-splice lists, areas, full coframe identity, and fixed-cap separation")


def check_cell_illustration():
    assert rotate(HOOK) == MATE
    assert zero(determinant(HOOK, unit=1) - determinant(MATE, unit=1))
    first, second = splice(CELL, HOOK), splice(CELL, MATE)
    assert first == ((4, 1), (1, 0))
    assert second == ((4, 2), (2, 0))
    assert cells(HOOK) == frozenset({(1, 1), (1, 2), (2, 1)})
    assert cells(MATE) == frozenset({(1, 2), (2, 1), (2, 2)})
    assert cells(first) == cells(HOOK) | {(1, 3)}
    assert cells(second) == cells(MATE) | {(1, 3)}
    assert len(first[0]) == len(HOOK[0]) and len(second[0]) == len(MATE[0])
    assert set(first[0]) & set(first[1]) == {1}
    assert set(second[0]) & set(second[1]) == {2}
    assert zero(determinant(first, unit=1) - (letter(1) * letter(3) - letter(4)))
    assert zero(determinant(second, unit=1) - (letter(2) ** 2 - letter(4)))
    assert not zero(determinant(first, unit=1) - determinant(second, unit=1))
    # Equal cap FUNCTIONS do not meet the same-literal-cap hypothesis.
    assert HOOK != MATE
    assert zero(determinant(splice(HOOK, HOOK), unit=1)
                - determinant(splice(MATE, MATE), unit=1))
    print("PASS: figure cells and determinants; replacing a literal cap by an equal-function cap fails")


if __name__ == "__main__":
    check_splice_identity()
    check_cell_illustration()
    print("ALL PASS")
