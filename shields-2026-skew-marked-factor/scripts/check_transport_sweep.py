r"""Paper section `sec:transport` (Equal functions at a common period).

Targets: `lem:mark-atlas` (at most one ordinary mark of each type at a fixed
inner and period; two types differ by \(e\) and are related by `eq:gauge`),
`thm:transport` (the common-period comparison under the rigidity hypothesis),
and `cor:two-row` (a two-row inner is rigid).

Every proper ordinary chart \(D\circ_\eta E\) with an inner of 2 to
`--max-inner` cells and an outer of 2 to 4 cells is built from its cells, and
charts are grouped by the pair \((p,s_F)\), which is exactly the comparison
the theorem makes.  The rigidity hypothesis ("every connected diagram with
function \(s_E\) is a translate of \(E\) or \(E^*\)") is decided by grouping all
connected diagrams of the inner's area by their Schur function.  In every group
whose inner is rigid the other members have inner \(E\) or \(E^*\) and equal
read outers; in every group whose inner is not rigid the conclusion is
counted, so the hypothesis is shown load-bearing or the box is reported as not
reaching a failure.  `cor:two-row` is swept over every connected diagram of up
to `--max-rigid` cells: the class of a two-row diagram is itself and its
rotation.  A mixed chart never shares \((p,s_F)\) with an ordinary one.
SymPy arithmetic is exact.
"""

import argparse
from collections import Counter, defaultdict

from schur_tools import (antitranspose, compose, delta, legal_marks, rotate, schur,
                         shapes, translate)


def rows(E):
    return len({i for i, j in E})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-inner', type=int, default=6)
    parser.add_argument('--max-rigid', type=int, default=11)
    args = parser.parse_args()

    # cor:two-row, and the rigidity of every inner in the box
    rigid = {}
    classes = {}
    two_row_classes = 0
    for n in range(2, max(args.max_inner, args.max_rigid) + 1):
        by_function = defaultdict(list)
        for E in shapes(n):
            by_function[schur(E)].append(E)
        for members in by_function.values():
            for E in members:
                is_rigid = all(M == E or M == rotate(E) for M in members)
                rigid[E] = is_rigid
                if rows(E) == 2:
                    assert is_rigid, ('cor:two-row', sorted(E))
                    two_row_classes += 1
            classes[n] = classes.get(n, 0) + 1
    nonrigid = sum(1 for E, r in rigid.items() if not r)
    assert two_row_classes and nonrigid
    print(f'PASS: every two-row diagram of up to {args.max_rigid} cells is rigid '
          f'({two_row_classes} diagrams); {nonrigid} diagrams in the box are not rigid')

    outers = [D for a in range(2, 5) for D in shapes(a)]
    atlas = gauge = 0
    groups = defaultdict(list)
    mixed_keys = set()
    for n in range(3, args.max_inner + 1):
        for E in shapes(n):
            by_period = defaultdict(list)
            marks = list(legal_marks(E))
            for W, v, case in marks:
                by_period[v[1] - v[0]].append((W, v, case))
            for p, entries in by_period.items():
                atlas += 1
                ordinary = [e for e in entries if e[2] in 'ab']
                assert len(ordinary) <= 2 and len({e[2] for e in ordinary}) == len(ordinary)
                assert len([e for e in entries if e[2] in 'cd']) <= 2
                if len(ordinary) == 2:
                    (wa, va, _), (wb, vb, _) = sorted(ordinary, key=lambda e: e[2])
                    assert va == (vb[0] + 1, vb[1] + 1)
                    for D in outers:
                        assert compose(D, E, wa, va, 'a') == compose(antitranspose(D), E, wb, vb, 'b')
                        gauge += 1
                for W, v, case in entries:
                    for D in outers:
                        F = compose(D, E, W, v, case)
                        P = schur(F)
                        if case in 'ab':
                            read = schur(D) if case == 'a' else schur(antitranspose(D))
                            groups[(p, P)].append((E, read, case))
                        else:
                            assert delta(P, p) == 0
                            mixed_keys.add((p, P))
    equal = failures_nonrigid = checked_rigid = 0
    for key, group in groups.items():
        assert key not in mixed_keys          # a mixed chart is never at an ordinary chart's period
        E0, Q0, _ = group[0]
        for E, Q, case in group[1:]:
            if rigid[E0] or rigid[E]:
                anchor = E0 if rigid[E0] else E
                other = E if anchor is E0 else E0
                assert other == anchor or other == rotate(anchor), ('thm:transport', key[0])
                assert Q == Q0, ('thm:transport outer', key[0])
                checked_rigid += 1
            else:
                if not (E == E0 or E == rotate(E0)) or Q != Q0:
                    failures_nonrigid += 1
            equal += 1
    assert not (set(groups) & mixed_keys)
    print(f'PASS: mark atlas on {atlas} (inner, period) pairs, and the literal gauge on {gauge} compositions')
    print(f'PASS: thm:transport on {checked_rigid} equal-function pairs with a rigid inner '
          f'(inner E or E*, equal read outer); {equal - checked_rigid} pairs with neither inner rigid, '
          f'of which {failures_nonrigid} break the conclusion')
    print('ALL PASS')


if __name__ == '__main__':
    main()
