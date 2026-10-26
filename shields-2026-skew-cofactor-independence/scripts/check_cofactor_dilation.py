#!/usr/bin/env python3
"""Exact checks for cofactor independence and dilation of skew Schur functions.

Paper sections `sec:boundary` (Boundary coefficients and dense rigidity), `sec:cofactors`
(Linear relations among cofactors), `sec:restoration` (Common beta entries and first
variations), `sec:dilation` (Integral dilation), `sec:full-equality` (Restoration and full equality).

The finite populations corroborate the manuscript's proofs; they are not
premises of its unbounded statements.  No research engine is imported.
Run with Python 3.10 or newer; only the standard library is required.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product


def add_to(out, poly, scale=1):
    for monomial, coefficient in poly.items():
        out[monomial] += scale * coefficient
        if not out[monomial]:
            del out[monomial]


def multiply(left, right):
    out = Counter()
    for u, a in left.items():
        for v, b in right.items():
            out[tuple(sorted(u + v))] += a * b
    return Counter({u: a for u, a in out.items() if a})


def generator(index):
    return {} if index < 0 else {(() if index == 0 else (index,)): 1}


def sign(word):
    return (-1) ** sum(a > b for i, a in enumerate(word) for b in word[i + 1:])


def determinant_permutations(indices):
    """Full signed permutations, including genuine zero-index units."""
    out = Counter()
    for perm in permutations(range(len(indices))):
        labels = [indices[i][j] for i, j in enumerate(perm)]
        if all(label >= 0 for label in labels):
            out[tuple(sorted(label for label in labels if label))] += sign(perm)
    return Counter({u: a for u, a in out.items() if a})


def determinant_dp(entries):
    """Independent row-by-row subset recurrence for polynomial entries."""
    states = {0: Counter({(): 1})}
    for row in entries:
        new = {}
        for mask, poly in states.items():
            for j, entry in enumerate(row):
                if mask & (1 << j) or not entry:
                    continue
                inversions = (mask >> (j + 1)).bit_count()
                target = new.setdefault(mask | (1 << j), Counter())
                add_to(target, multiply(poly, entry), (-1) ** inversions)
        states = new
    return states.get((1 << len(entries)) - 1, Counter())


def board(a, b):
    return [[x - y for y in b] for x in a]


def determinant(a, b):
    return determinant_dp([[generator(x - y) for y in b] for x in a])


def cofactors(a, b):
    return [
        [Counter({u: (-1) ** (i + j) * c for u, c in
                  determinant_permutations(board(a[:i] + a[i + 1:],
                                                 b[:j] + b[j + 1:])).items()})
         for j in range(len(b))]
        for i in range(len(a))
    ]


def available(a, b):
    return tuple(z for z in range(1, a[0]) if z not in a and z not in b)


def unit(a, b, z, cofs=None):
    cofs = cofactors(a, b) if cofs is None else cofs
    out = Counter()
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if x > z > y:
                add_to(out, multiply(cofs[i][j], {tuple(sorted((x-z, z-y))): 1}))
    return out


def rank(polys):
    """Exact sparse elimination over the rationals, with monomials as rows."""
    basis = {}
    for poly in polys:
        vector = {u: Fraction(c) for u, c in poly.items() if c}
        while vector:
            pivot = max(vector)
            coefficient = vector[pivot]
            if pivot not in basis:
                basis[pivot] = {u: c / coefficient for u, c in vector.items()}
                break
            for u, c in basis[pivot].items():
                vector[u] = vector.get(u, 0) - coefficient * c
                if not vector[u]:
                    del vector[u]
    return len(basis)


def derivative(poly, index):
    out = Counter()
    for monomial, coefficient in poly.items():
        multiplicity = monomial.count(index)
        if multiplicity:
            labels = list(monomial)
            labels.remove(index)
            out[tuple(labels)] += multiplicity * coefficient
    return out


def component(poly, degree):
    return Counter({u: a for u, a in poly.items() if len(u) == degree})


def scaled(poly, t):
    return Counter({tuple(t * j for j in u): a for u, a in poly.items()})


def symmetric(a, b):
    return a == tuple(a[0] - y for y in reversed(b))


def modulus(a, b):
    from math import gcd
    g = 0
    for x in a:
        g = gcd(g, a[0] - x)
    for y in b:
        g = gcd(g, y)
    return g


def dense_boards(max_span, max_order=5):
    for span in range(3, max_span + 1):
        for n in range(2, min(max_order, (span + 1) // 2) + 1):
            for sites in combinations(range(1, span), 2 * n - 2):
                b = tuple(reversed(sites[:n-1])) + (0,)
                a = (span,) + tuple(reversed(sites[n-1:]))
                assert a[-1] > b[0]
                yield a, b


def validate_diagram(a, b):
    """Recover literal row intervals; check both boundaries and connections."""
    assert len(a) == len(b) and b[-1] == 0
    assert all(a[i] > a[i+1] and b[i] > b[i+1] for i in range(len(a)-1))
    starts = [b[i] + i + 1 for i in range(len(a))]
    stops = [a[i] + i + 1 for i in range(len(a))]
    assert all(u < v for u, v in zip(starts, stops))
    assert all(starts[i] >= starts[i+1] and stops[i] >= stops[i+1]
               and stops[i+1] > starts[i] for i in range(len(a)-1))
    return tuple(stops[i] - starts[i] for i in range(len(a)))


def check_cofactors():
    counts = Counter()
    for a, b in dense_boards(10):
        n = len(a)
        validate_diagram(a, b)
        cofs = cofactors(a, b)
        flat = sum(cofs, [])
        is_symmetric = symmetric(a, b)
        assert rank(flat) == (n * (n + 1) // 2 if is_symmetric else n * n)
        assert determinant(a, b) == determinant_permutations(board(a, b))
        counts['boards'] += 1
        counts['symmetric' if is_symmetric else 'nonsymmetric'] += 1
        for z in sorted(set(a + b)):
            assert not unit(a, b, z, cofs)
            counts['endpoint_zeros'] += 1
        if is_symmetric:
            for i in range(n):
                for j in range(n):
                    assert cofs[i][j] == cofs[n-1-j][n-1-i]
                    counts['reflection_identities'] += 1
            # Independently inspect the explicit maximum-square leaders after
            # reversing the columns, rather than reading the rank calculation.
            leaders = set()
            for i in range(n):
                for j in range(i, n):
                    minor = determinant_permutations([
                        [a[u] + a[v] - a[0] for v in range(n) if v != j]
                        for u in range(n) if u != i])
                    top = max(sum(k*k for k in monomial) for monomial in minor)
                    maximum = [u for u in minor if sum(k*k for k in u) == top]
                    expected = tuple(sorted(
                        [2*a[k]-a[0] for k in range(i)] +
                        [a[k]+a[k+1]-a[0] for k in range(i, j)] +
                        [2*a[k]-a[0] for k in range(j+1, n)]))
                    assert maximum == [expected] and abs(minor[expected]) == 1
                    assert expected not in leaders
                    leaders.add(expected)
                    counts['distinct_leaders'] += 1
        if n >= 3:
            remainder = Counter({monomial: coefficient for monomial, coefficient in
                                 determinant(a, b).items() if a[0] not in monomial})
            u, v = a[0]-a[1], b[-2]
            second = max(j for monomial in remainder for j in monomial)
            assert second == a[0]-min(u, v)
            if u < v:
                extension = determinant((a[1]+u,) + a[2:], b[:-1])
            elif v < u:
                extension = determinant(a[1:], b[:-2] + (0,))
            else:
                extension = None
                assert derivative(derivative(remainder, second), second)
            if extension is not None:
                assert derivative(remainder, second) == Counter({
                    monomial: (-1)**n * coefficient
                    for monomial, coefficient in extension.items()})
            counts['exterior_gap_readings'] += 1
            child = cofactors(a[1:], b[:-1])
            for i in range(1, n):
                for j in range(n-1):
                    expected = Counter({u: (-1)**(n-1)*c
                                        for u, c in child[i-1][j].items()})
                    assert derivative(cofs[i][j], a[0]) == expected
                    counts['private_derivatives'] += 1
            center = a[1] + b[-2]
            child_symmetric = all(a[i+1] + b[n-2-i] == center for i in range(n-1))
            if not is_symmetric and child_symmetric:
                counts['symmetric_child_nonsymmetric_parent'] += 1
    assert all(counts[key] > 0 for key in counts)
    print('COFACTORS', dict(counts))


def check_dilation():
    counts = Counter()
    for a, b in dense_boards(8, 3):
        if symmetric(a, b):
            continue
        base_sites = available(a, b)
        base_units = [unit(a, b, z) for z in base_sites]
        base_nullity = len(base_sites) - rank(base_units)
        g = modulus(a, b)
        for t in range(1, 5):
            aa, bb = tuple(t*x for x in a), tuple(t*y for y in b)
            sites = available(aa, bb)
            cc = cofactors(aa, bb)
            units = {z: unit(aa, bb, z, cc) for z in sites}
            for z, poly in zip(base_sites, base_units):
                assert units[t*z] == scaled(poly, t)
                counts['grid_identities'] += 1
            q = t*g
            off = []
            for r in range(q):
                partner = (t*a[0]-r) % q
                if r % t and r < partner:
                    vector = {z: int(z % q == r)-int(z % q == partner)
                              for z in sites}
                    assert any(vector.values())
                    residual = Counter()
                    for z, weight in vector.items():
                        add_to(residual, units[z], weight)
                    assert not residual
                    off.append(vector)
                    counts['arithmetic_relations'] += 1
            nullity = len(sites) - rank(units.values())
            assert nullity == base_nullity + len(off)
            fixed_new = sum((2*r-t*a[0]) % q == 0 for r in range(q))
            fixed_old = sum((2*r-a[0]) % g == 0 for r in range(g))
            assert 2 * len(off) == (t-1)*g-fixed_new+fixed_old
            counts['dilations'] += 1
    # Dropping cofactor independence really does break the asserted law.
    a, b = (4, 3), (1, 0)
    assert symmetric(a, b) and modulus(a, b) == 1
    base = [unit(a, b, z) for z in available(a, b)]
    aa, bb = (8, 6), (2, 0)
    double = [unit(aa, bb, z) for z in available(aa, bb)]
    assert len(base)-rank(base) == 0 and len(double)-rank(double) == 2
    counts['rejecting_symmetric_control'] = 1
    print('DILATION', dict(counts))


def all_subsets(values):
    for n in range(len(values)+1):
        yield from combinations(values, n)


def lift(a, b, z):
    return tuple(sorted(a + tuple(z), reverse=True)), tuple(sorted(b + tuple(z), reverse=True))


def deletion_sign(a, b, z):
    z = tuple(sorted(z, reverse=True))
    x, y = lift(a, b, z)
    return sign([x.index(v) for v in a+z]) * sign([y.index(v) for v in b+z])


def path_matrix(a, b, z):
    out = []
    for x in a:
        row = []
        for y in b:
            poly = Counter()
            if x > y:
                middle = [v for v in z if x > v > y]
                for subset in all_subsets(middle):
                    vertices = (x,) + tuple(sorted(subset, reverse=True)) + (y,)
                    gaps = tuple(sorted(u-v for u, v in zip(vertices, vertices[1:])))
                    poly[gaps] += (-1)**len(subset)
            row.append(poly)
        out.append(row)
    return out


def check_paths_and_failure():
    counts = Counter()
    for a, b in [((4, 2), (1, 0)), ((7, 6), (1, 0)),
                 ((7, 6, 3), (4, 2, 0))]:
        cc = cofactors(a, b)
        for z in all_subsets(available(a, b)):
            x, y = lift(a, b, z)
            validate_diagram(x, y)
            epsilon = deletion_sign(a, b, z)
            actual = determinant_permutations(board(x, y))
            expected = determinant_dp(path_matrix(a, b, z))
            assert actual == Counter({u: epsilon*c for u, c in expected.items()})
            n = len(a)
            assert component(actual, n) == Counter({u: epsilon*c for u, c in determinant(a, b).items()})
            correction = Counter()
            for site in z:
                add_to(correction, unit(a, b, site, cc), -epsilon)
            assert component(actual, n+1) == correction
            counts['full_path_identities'] += 1
    assert unit((4, 2), (1, 0), 3) == Counter({(1, 2, 2): 1, (1, 1, 3): -1})
    a, b = (20, 10), (5, 0)
    j1, j4 = (1, 6, 11, 16), (4, 9, 14, 19)
    z, w = j1 + (2,), j4 + (2,)
    x, y = lift(a, b, z)
    xx, yy = lift(a, b, w)
    validate_diagram(x, y)
    validate_diagram(xx, yy)
    f, h = determinant_permutations(board(x, y)), determinant_permutations(board(xx, yy))
    assert f == determinant(x, y) and h == determinant(xx, yy)
    assert deletion_sign(a, b, z) == deletion_sign(a, b, w)
    assert component(f, 2) == component(h, 2) and component(f, 3) == component(h, 3)
    assert f != h
    target = (2, 5, 9, 9)
    assert (f.get(target, 0), h.get(target, 0)) == (-1, 0)
    survivor_words = []
    for perm in permutations(range(len(x))):
        labels = tuple(x[i]-y[j] for i, j in enumerate(perm))
        if all(label in (0, 2, 5, 9) for label in labels):
            survivor_words.append(tuple(j+1 for j in perm))
    assert survivor_words == [(2, 1, 5, 4, 3, 7, 6)]
    assert all(xx[0]-column not in (0, 2, 5, 9) for column in yy)
    print('PATHS', dict(counts))
    print('FIRST-CORRECTION CONTROL: degrees 2 and 3 agree; '
          'coefficient h_2*h_5*h_9^2 = (-1, 0); both 25-cell diagrams validated')


def compositions(total):
    if not total:
        yield ()
    else:
        for first in range(1, total+1):
            for rest in compositions(total-first):
                yield (first,) + rest


def profile_betas(rows, gaps):
    b = [0]*len(rows)
    a = [0]*len(rows)
    a[-1] = rows[-1]
    for i in range(len(rows)-2, -1, -1):
        b[i] = a[i+1] - gaps[i]
        a[i] = b[i] + rows[i]
    return tuple(a), tuple(b)


def check_arbitrary_mates():
    classes = defaultdict(list)
    n_diagrams = 0
    for area in range(1, 10):
        for rows in compositions(area):
            gap_ranges = [range(min(x, y)) for x, y in zip(rows, rows[1:])]
            for gaps in product(*gap_ranges):
                a, b = profile_betas(rows, gaps)
                assert validate_diagram(a, b) == rows
                poly = determinant(a, b)
                minimum = min(poly, key=lambda u: sum(j*j for j in u))
                assert minimum == tuple(sorted(rows)) and poly[minimum] == 1
                assert max(map(len, poly)) == len(rows)
                corner = derivative(poly, a[0])
                assert corner
                least = min(corner, key=lambda u: sum(j*j for j in u))
                recovered = (0,)*(len(rows)-1-len(least)) + least
                assert recovered == tuple(sorted(gaps))
                classes[tuple(sorted(poly.items()))].append((a, b))
                n_diagrams += 1
    checked = nonrotation_controls = 0
    for members in classes.values():
        for a, b in members:
            reflection = (tuple(a[0]-y for y in reversed(b)),
                          tuple(a[0]-x for x in reversed(a)))
            if a[-1] >= b[0]:
                assert all(mate in ((a, b), reflection) for mate in members)
                checked += 1
            elif any(mate not in ((a, b), reflection) for mate in members):
                nonrotation_controls += 1
    assert checked and nonrotation_controls
    print('ARBITRARY-MATE CHECK: all connected diagrams through 9 cells =', n_diagrams,
          '; nonnegative-board sources =', checked,
          '; sources with nonrotation mates outside domain =', nonrotation_controls)


def check_periods():
    calls = failures_outside_bound = 0
    for length in range(2, 11):
        for bits in product((0, 1), repeat=length):
            periods = [p for p in range(1, length)
                       if all(bits[j] == bits[j+p] for j in range(length-p))]
            for p, q in combinations(periods, 2):
                from math import gcd
                d = gcd(p, q)
                conclusion = all(bits[j] == bits[j+d] for j in range(length-d))
                if p+q <= length:
                    assert conclusion
                    calls += 1
                elif not conclusion:
                    failures_outside_bound += 1
    assert calls and failures_outside_bound
    print('FINITE-WORD CHECK:', calls, 'period pairs within length bound;',
          failures_outside_bound, 'counterexamples outside the sum bound')


if __name__ == '__main__':
    check_cofactors()
    check_dilation()
    check_paths_and_failure()
    check_arbitrary_mates()
    check_periods()
    print('ALL PASS')
