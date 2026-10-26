r"""Paper section `sec:descent` (Strict descent and actual realization).

Also checks `prop:full-image` and `cor:equal-width-ribbon` by explicit
nonminimal empty charts, and constructs nonline minimal-inner inputs for
`lem:oim`.  For `app:aligned` (Aligned reconstruction before minimality),
it tests the imported composition covariance from the factor-recovery paper
on actual empty square-inner compositions, as consumed by `prop:full-image`.
It also checks `lem:weighted-peeling` on actual empty ribbon compositions
and `eq:source-high-current`, including both two-cell cut occurrences.
SymPy derives Schur polynomials from the constructed cell sets.  The
non-vacuity witnesses do not prove class-wide recognition.
"""
import sympy as sp


def row(length):
    return {(0, j) for j in range(length)}


def normalize(cells):
    first_row = min(i for i,j in cells)
    first_column = min(j for i,j in cells)
    return {(i-first_row, j-first_column) for i,j in cells}


def empty_horizontal_copies(inner, copies):
    """Ordinary empty marks translate by (1-r(E), c(E))."""
    inner = normalize(inner)
    height = max(i for i,j in inner)+1
    width = max(j for i,j in inner)+1
    displacement = (1-height, width)
    assembled = set()
    for k in range(copies):
        placed = {(i+k*displacement[0], j+k*displacement[1]) for i,j in inner}
        assert assembled.isdisjoint(placed)
        assembled.update(placed)
    return normalize(assembled), displacement[1]-displacement[0]


def flags(cells):
    cells = normalize(cells)
    number_rows = max(i for i,j in cells)+1
    left, right = [], []
    for i in range(number_rows):
        occupied = sorted(j for r,j in cells if r == i)
        assert occupied == list(range(occupied[0], occupied[-1]+1))
        left.append(occupied[0])
        right.append(occupied[-1]+1)
    assert all(a >= b for a,b in zip(left, left[1:]))
    assert all(a >= b for a,b in zip(right, right[1:]))
    reachable = {next(iter(cells))}
    frontier = set(reachable)
    while frontier:
        following = {(i+di,j+dj) for i,j in frontier
                     for di,dj in [(1,0),(-1,0),(0,1),(0,-1)]}
        frontier = (following & cells)-reachable
        reachable.update(frontier)
    assert reachable == cells
    X = [right[i]+number_rows-i-1 for i in range(number_rows)]
    Y = [left[i]+number_rows-i-1 for i in range(number_rows)]
    span = len({j-i for i,j in cells})
    assert span == max(X)-min(Y)
    return X, Y, span


def schur(cells, h):
    X, Y, _ = flags(cells)
    return sp.expand(sp.Matrix([[h.get(x-y, 0) for y in Y] for x in X]).det())


def hall(poly, period, h):
    return sp.expand(sum(sp.diff(poly, h[j])*h[j-period]
                         for j in h if j >= period and j > 0))


def check_square_covariance(h):
    square = {(0,0),(0,1),(1,0),(1,1)}
    probes = {0: sp.Integer(1)}
    for copies in range(1,4):
        actual, period = empty_horizontal_copies(square, copies)
        assert period == 3
        probes[copies] = schur(actual, h)
    xi = hall(probes[1], period, h)
    assert sp.expand(xi+h[1]) == 0
    for copies, polynomial in probes.items():
        if copies == 0:
            continue
        for r in range(1,copies+2):
            coarse_remainder = probes[copies-r] if r <= copies else 0
            raw_hall = hall(polynomial, r*period, h)
            raw_weighted = sp.expand(sum(
                (j-r*period)*sp.diff(polynomial, h[j])*h[j-r*period]
                for j in h if j >= r*period and j > 0))
            assert sp.expand(raw_hall-xi**r*coarse_remainder) == 0
            assert sp.expand(raw_weighted-xi**r*period*(copies-r)*coarse_remainder) == 0
    print('PASS: ordinary covariance with nonconstant local factor, exhaustion and beyond-exhaustion modes')


def check_weighted_peeling(h):
    inners = [
        row(1),
        row(2),
        {(0,0),(0,1),(1,0),(1,1)},
        {(i,j) for i in range(3) for j in range(2)},
    ]
    ribbons = [
        row(2),
        {(0,0),(1,0)},
        row(3),
        {(0,0),(0,1),(1,0)},
    ]
    for ribbon in ribbons:
        rows = sorted({i for i,j in ribbon})
        cuts, partial = set(), 0
        for i in rows[:-1]:
            partial += sum(r == i for r,c in ribbon)
            cuts.add(partial)
        copies = len(ribbon)
        epsilon = 1-int(1 in cuts)-int(copies-1 in cuts)
        canonical = (-1)**(len(rows)-1)*schur(ribbon, h)
        mode = copies-1
        weighted = sp.expand(sum(
            (j-mode)*sp.diff(canonical, h[j])*h[j-mode]
            for j in h if j >= mode and j > 0))
        assert sp.expand(weighted-h[1]) == 0
        assert sp.expand(hall(canonical, mode, h)-epsilon*h[1]) == 0
    print('PASS: original ribbon current coefficients retain both two-cell cut occurrences')
    for inner in inners:
        X, _, period = flags(inner)
        sigma_inner = (-1)**(len(X)-1)
        inner_schur = schur(inner, h)
        inner_canonical = sigma_inner*inner_schur
        kappa = sp.diff(inner_canonical, h[period])
        xi = hall(inner_schur, period, h)
        assert sp.expand(xi-sigma_inner*kappa) == 0
        inner_height = max(i for i,j in inner)+1
        inner_width = max(j for i,j in inner)+1
        for ribbon in ribbons:
            assembled = set()
            for i,j in ribbon:
                content = j-i
                origin = (content*(1-inner_height)+i, content*inner_width+i)
                placed = {(r+origin[0], c+origin[1]) for r,c in inner}
                assert assembled.isdisjoint(placed)
                assembled.update(placed)
            assembled = normalize(assembled)
            full_X, _, span = flags(assembled)
            copies = len(ribbon)
            assert span == copies*period
            sigma_outer = (-1)**(len({i for i,j in ribbon})-1)
            sigma_full = (-1)**(len(full_X)-1)
            assert sigma_full == sigma_outer*sigma_inner**copies
            polynomial = schur(assembled, h)
            mode = (copies-1)*period
            weighted = sp.expand(sum(
                (j-mode)*sp.diff(polynomial, h[j])*h[j-mode]
                for j in h if j >= mode and j > 0))
            assert sp.expand(
                weighted-period*xi**(copies-1)*sigma_outer*inner_schur) == 0
            assert sp.expand(
                sigma_full*weighted-period*kappa**(copies-1)*inner_canonical) == 0
    print('PASS: signed empty covariance and canonical weighted peeling on actual ribbon compositions')


def main():
    h = {0: sp.Integer(1), **{j: sp.Symbol(f'h{j}') for j in range(1,25)}}
    check_square_covariance(h)
    check_weighted_peeling(h)
    original, p = empty_horizontal_copies(row(3), 8)
    smaller, d = empty_horizontal_copies(row(2), 12)
    assert original == smaller and len(original) == 24
    assert (0, d) < (0, p)
    assert flags(original)[2] == p*8
    print('PASS: proper equal-period row witness lies outside source-minimal, line-inner-free domain')

    coarse, p = empty_horizontal_copies(row(6), 4)
    fine, q = empty_horizontal_copies(row(3), 8)
    assert coarse == fine and p == 2*q
    polynomial = schur(coarse, h)
    terminal = polynomial
    for _ in range(3):
        terminal = hall(terminal, p, h)
    assert sp.expand(terminal-schur(row(6), h)) == 0
    assert hall(terminal, p, h) == 1
    fine_row_image, _ = empty_horizontal_copies(row(3), 2)
    assert sp.expand(schur(fine_row_image, h)-terminal) == 0
    z = sp.symbols('z1:9')
    pullback = terminal.xreplace({h[j*q]: z[j-1] for j in range(1,9)})
    assert pullback == z[1]
    print('PASS: nonminimal aligned row witness has whole extracted numerator of coarse span two')

    square = {(0,0),(0,1),(1,0),(1,1)}
    for copies in (3,9):
        actual, p = empty_horizontal_copies(square, copies)
        X, Y, span = flags(actual)
        assert len(actual) == 4*copies and span == 3*copies and p == 3
        assert any({(i,j),(i+1,j),(i,j+1),(i+1,j+1)} <= actual for i,j in actual)
        candidate_smaller_periods = [d for d in range(2,p) if span % d == 0]
        assert candidate_smaller_periods == []
        assert all(x > y for x,y in zip(X,Y))
    print('PASS: actual square-inner charts meet the nonline minimum input at areas 12 and 36')
    print('ALL PASS')


if __name__ == '__main__':
    main()
