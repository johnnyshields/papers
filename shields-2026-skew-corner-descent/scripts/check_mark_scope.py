"""Count Hypothesis V failures and distinguish them from ordinary gauge changes."""
from collections import Counter
from diagram_tools import (canonical, compose, legal_marks, mark_sets, profile_shape,
                           schur, shapes_of_area, translate)
from check_without_v import adjacent_cells


def main():
    counts = Counter()
    by_area = {}
    for n in range(2, 10):
        current = Counter()
        for E in shapes_of_area(n):
            for W, v, case in legal_marks(E):
                O, _, _ = mark_sets(E, W, v)
                if case in 'cd':
                    status = 'V not required (mixed)'
                elif not W:
                    status = 'empty convention'
                elif min(len(adjacent_cells(W, O)), len(adjacent_cells(translate(W, v), O))) == 1:
                    status = 'satisfies V'
                else:
                    status = 'fails V'
                current[case+' '+status] += 1
        counts.update(current)
        by_area[n] = (sum(c for k, c in current.items() if k.endswith('fails V')),
                      sum(c for k, c in current.items() if k.endswith(('fails V', 'satisfies V'))))
        if n == 8:
            assert sum(counts.values()) == 1438
            assert sum(c for k, c in counts.items() if k.endswith('fails V')) == 6
            assert sum(c for k, c in counts.items() if k.endswith(('fails V', 'satisfies V'))) == 294
            print('through 8 cells:', dict(sorted(counts.items())))
    assert counts['a fails V'] == counts['b fails V'] == 8
    assert counts['a satisfies V'] == counts['b satisfies V'] == 344
    assert counts['c V not required (mixed)'] == counts['d V not required (mixed)'] == 345
    assert counts['a empty convention'] == counts['b empty convention'] == 985
    assert 16*294 > 6*704  # the two measured cumulative proportions, without extrapolation
    print('all marks by case and V:', dict(sorted(counts.items())))
    print('V failures by inner area:', by_area)
    E = profile_shape((2, 1), (0,))
    D = profile_shape((2,), ())
    ATD = canonical(frozenset((-j, -i) for i, j in D))
    marks = list(legal_marks(E))
    # Empty edge readings have an ordinary gauge without any mark adjacency.
    W, v, case = next(m for m in marks if not m[0] and m[2] == 'a')
    Wb, vb, _ = next(m for m in marks if not m[0] and m[2] == 'b')
    assert compose(D, E, W, v, 'a') == compose(ATD, E, Wb, vb, 'b')
    assert schur(D) != schur(ATD)
    dual_counts = Counter()
    for n in range(2, 9):
        for inner in shapes_of_area(n):
            ms = list(legal_marks(inner))
            for Wa, va, ca in ms:
                if not Wa or ca != 'a':
                    continue
                for Wb, vb, cb in ms:
                    if cb != 'b' or va[1]-va[0] != vb[1]-vb[0]:
                        continue
                    O, _, _ = mark_sets(inner, Wa, va)
                    fails = min(len(adjacent_cells(Wa, O)), len(adjacent_cells(translate(Wa, va), O))) > 1
                    dual_counts['fails V' if fails else 'satisfies V'] += 1
    assert dual_counts == {'fails V': 3}
    print('positive-width ordinary gauge pairs:', dict(dual_counts))
    print('empty-edge gauge requires the involution without a non-V configuration')
    print('check_mark_scope: PASS')


if __name__ == '__main__':
    main()
