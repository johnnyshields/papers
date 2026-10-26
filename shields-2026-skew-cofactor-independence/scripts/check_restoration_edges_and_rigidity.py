#!/usr/bin/env python3
r"""Paper sections `sec:boundary` (Boundary coefficients and dense rigidity), `sec:restoration` (Common beta
entries and first variations), `sec:dilation` (Integral dilation) and `sec:full-equality` (Restoration and
full equality).  Target labels: `eq:profile`, `eq:rotation-condition`, `eq:cofactor-degree`,
`prop:path-expansion`, `lem:endpoint-normalization`, `eq:all-edges`, `eq:offgrid-space`,
`cor:nullity-increment`, `ex:dilation-ray`, `thm:dilation`, `cor:independent-restorations`,
`prop:symmetric-unit-kernel`.

What the other scripts leave open, asserted here in exact arithmetic (standard library and `Fraction`; the
determinants and units are the ones of `check_cofactor_dilation`, imported, which expand over genuine
permutations in `determinant_permutations`):

  (A) the profile conditions and the rotation map on beta lists, the cofactor degree formula, and the
      rotation-fixing condition, on every connected diagram through 9 cells;
  (B) cores: the endpoint counting function is at least one strictly between 0 and N, the zero-free core of a
      connected diagram is connected, and every restoration C[Z] is connected of area |C| with row count
      k + |Z| and residual core C;
  (C) `lem:endpoint-normalization` on every connected zero-free core, dense or not, through span 11: the
      solution space of all edge equations on the endpoint-extended word is exactly the odd residue
      functions modulo the endpoint modulus, with the dimension count, and the quadratic Q_lambda vanishes
      exactly on the odd reflections with the midpoint forced to zero;
  (D) `ex:dilation-ray` for t up to 9 with its explicit basis, `cor:nullity-increment` at modulus one for
      t up to 6, and the strict containment in the concluding remarks;
  (E) `cor:independent-restorations` as a census: for every dense core with K(C) = 0 through 12 cells, and
      for the doubles of the nonsymmetric ones of modulus one, every connected mate of every C[Z] is C[Z] or
      its rotation, against the complete table of connected diagrams of that area.
"""
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import gcd

import check_cofactor_dilation as K

SQ = lambda m: sum(j * j for j in m)                                   # noqa: E731


def rank_fraction(rows, ncols):
    m = [[Fraction(x) for x in r] for r in rows]
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        r += 1
    return r


def connected_core(a, b):
    n = len(a)
    return (len(b) == n and all(a[i] > a[i + 1] and b[i] > b[i + 1] for i in range(n - 1))
            and all(a[i] > b[i] for i in range(n)) and all(a[i + 1] >= b[i] for i in range(n - 1)))


def rotate(a, b):
    return tuple(a[0] - y for y in reversed(b)), tuple(a[0] - x for x in reversed(a))


def normalize_pair(a, b):
    t = b[-1]
    return tuple(x - t for x in a), tuple(y - t for y in b)


def profile_diagrams(max_area):
    for area in range(1, max_area + 1):
        for rows in K.compositions(area):
            for gaps in product(*[range(min(x, y)) for x, y in zip(rows, rows[1:])]):
                a, b = K.profile_betas(rows, gaps)
                yield rows, gaps, a, b


def check_profiles_and_cores():
    n_d = n_core = n_rest = n_rot = 0
    for rows, gaps, a, b in profile_diagrams(9):
        n = len(rows)
        # eq:profile and its inverse
        assert all(rows[i] == a[i] - b[i] > 0 for i in range(n))
        assert all(gaps[i] == a[i + 1] - b[i] and 0 <= gaps[i] < min(rows[i], rows[i + 1]) for i in range(n - 1))
        # rotation on beta lists reverses both profile words and fixes the function
        ra, rb = rotate(a, b)
        rr = K.validate_diagram(ra, rb)
        assert rr == rows[::-1] and tuple(ra[i + 1] - rb[i] for i in range(n - 1)) == gaps[::-1]
        poly = K.determinant(a, b)
        assert K.determinant(ra, rb) == poly
        assert rotate(ra, rb) == (a, b)
        # eq:rotation-condition  <=>  the translation class is fixed
        fixed = all(a[i] + b[n - 1 - i] == a[0] for i in range(n))
        assert fixed == ((ra, rb) == (a, b)) == (rows == rows[::-1] and gaps == gaps[::-1])
        n_rot += fixed
        # lemma on readings: row count, square-minimal monomial, corner label and cofactor
        assert max(len(m) for m in poly) == n and max(j for m in poly for j in m) == a[0]
        # eq:cofactor-degree for dense boards only (all labels positive)
        if a[-1] > b[0] and n >= 2:
            cofs = K.cofactors(a, b)
            area = sum(a) - sum(b)
            for i in range(n):
                for j in range(n):
                    degs = {sum(m) for m in cofs[i][j]}
                    assert degs == {area - (a[i] - b[j])}, (a, b, i, j)
        # the endpoint counting function and the zero-free core
        for x2 in range(1, 2 * a[0]):                                   # x = x2 / 2, strictly between 0 and N
            if x2 % 2 == 0 and x2 // 2 in set(a) | set(b):
                continue
            xs = Fraction(x2, 2)
            assert sum(v > xs for v in a) - sum(v > xs for v in b) >= 1 or xs >= a[0]
        Z = set(a) & set(b)
        A = tuple(v for v in a if v not in Z)
        B = tuple(v for v in b if v not in Z)
        assert len(A) == len(B) == n - len(Z) >= 1
        assert connected_core(A, B), (a, b, A, B)
        assert not set(A) & set(B)
        n_d += 1
        n_core += 1
    # restorations of every connected zero-free normalized core
    for N in range(2, 10):
        for k in range(1, 5):
            for As in combinations(range(1, N), k - 1):
                for Bs in combinations(range(1, N), k - 1):
                    if set(As) & set(Bs):
                        continue
                    A = (N,) + tuple(sorted(As, reverse=True))
                    B = tuple(sorted(Bs, reverse=True)) + (0,)
                    if not connected_core(A, B):
                        continue
                    area = sum(A) - sum(B)
                    omega = tuple(z for z in range(1, N) if z not in A and z not in B)
                    for r in range(len(omega) + 1):
                        for Zs in combinations(omega, r):
                            x = tuple(sorted(A + Zs, reverse=True))
                            y = tuple(sorted(B + Zs, reverse=True))
                            rows = K.validate_diagram(x, y)
                            assert len(rows) == k + r and sum(x) - sum(y) == area
                            assert tuple(v for v in x if v not in Zs) == A
                            n_rest += 1
    print("PASS (A) eq:profile, rotation on beta lists, eq:rotation-condition (%d symmetric of %d diagrams),"
          " readings, eq:cofactor-degree" % (n_rot, n_d))
    print("PASS (B) endpoint counting function >= 1, connected residual core (%d diagrams), %d restorations "
          "connected of area |C|, rows k + |Z|" % (n_core, n_rest))


def odd_function_dim(g, N):
    fixed = sum((2 * r - N) % g == 0 for r in range(g))
    assert (g - fixed) % 2 == 0
    return (g - fixed) // 2


def check_edge_normalization():
    n_cores = n_nondense = 0
    for N in range(3, 12):
        for k in range(2, 5):
            for As in combinations(range(1, N), k - 1):
                for Bs in combinations(range(1, N), k - 1):
                    if set(As) & set(Bs):
                        continue
                    A = (N,) + tuple(sorted(As, reverse=True))
                    B = tuple(sorted(Bs, reverse=True)) + (0,)
                    if not connected_core(A, B):
                        continue
                    g = 0
                    for x in A:
                        g = gcd(g, N - x)
                    for y in B:
                        g = gcd(g, y)
                    assert g > 0 and g < N
                    # unknown word lam_1 .. lam_{N-1}; the edge equations of eq:all-edges
                    eqs = []
                    for a in A:
                        for b in B:
                            if a > b:
                                for z in range(b + 1, a):
                                    row = [0] * (N - 1)
                                    row[z - 1] += 1
                                    row[a + b - z - 1] += 1
                                    eqs.append(row)
                    dim = (N - 1) - rank_fraction(eqs, N - 1)
                    assert dim == odd_function_dim(g, N), (A, B, g, dim)
                    # every residue function restricts to a solution (the reverse direction)
                    for r in range(g):
                        phi = {r: 1, (N - r) % g: -1} if r != (N - r) % g else None
                        if phi is None:
                            continue
                        lam = [phi.get(z % g, 0) for z in range(1, N)]
                        assert all(sum(c * v for c, v in zip(row, lam)) == 0 for row in eqs)
                    # and every solution is a residue function: periodic mod g
                    nullrows = eqs
                    for z in range(1, N - g):
                        row = [0] * (N - 1)
                        row[z - 1], row[z + g - 1] = 1, -1
                        assert rank_fraction(nullrows + [row], N - 1) == rank_fraction(nullrows, N - 1), (A, B, z)
                    n_cores += 1
                    n_nondense += not (A[-1] > B[0])
    assert n_cores > 100 and n_nondense > 20
    # the quadratic Q_lambda: monomials h_{a-z} h_{z-b}, vanishing iff odd about the midpoint
    n_q = 0
    for width in range(2, 13):                                          # a - b
        zs = range(1, width)
        monos = {}
        cols = []
        for z in zs:
            m = tuple(sorted((width - z, z)))
            cols.append(m)
        distinct = sorted(set(cols))
        mat = [[1 if cols[c] == m else 0 for c in range(len(cols))] for m in distinct]
        kernel = len(cols) - rank_fraction(mat, len(cols))
        assert kernel == (width - 1) - len(distinct)
        # kernel equals {lam_z + lam_{width - z} = 0, midpoint 0}
        expected = (width - 1) // 2
        assert kernel == expected, (width, kernel)
        n_q += 1
    print("PASS (C) lem:endpoint-normalization on %d connected zero-free cores (%d not dense): edge-equation "
          "solution space = odd residue functions mod g, periodic, dimension (g - fixed)/2; Q_lambda kernel for "
          "widths 2..12" % (n_cores, n_nondense))


def kernel_dim(a, b):
    sites = K.available(a, b)
    if not sites:
        return 0
    cofs = K.cofactors(a, b)
    units = [K.unit(a, b, z, cofs) for z in sites]
    return len(sites) - K.rank(units)


def check_dilation_examples():
    A, B = (4, 2), (1, 0)
    assert not K.symmetric(A, B) and K.modulus(A, B) == 1 and K.available(A, B) == (3,)
    assert K.unit(A, B, 3) == Counter({(1, 2, 2): 1, (1, 1, 3): -1})
    for t in range(1, 10):
        tA, tB = tuple(t * x for x in A), tuple(t * y for y in B)
        cofs = K.cofactors(tA, tB)
        assert K.rank([c for row in cofs for c in row]) == 4              # cofactors of every dilate independent
        sites = K.available(tA, tB)
        units = [K.unit(tA, tB, z, cofs) for z in sites]
        nullity = len(sites) - K.rank(units)
        assert nullity == (t - 1) // 2, (t, nullity)
        basis = []
        for r in range(1, t):
            if 2 * r < t:
                vec = {z: int(z % t == r) - int(z % t == t - r) for z in sites}
                assert all(vec[z] == 0 for z in sites if z % t == 0)
                total = Counter()
                for z, w in vec.items():
                    K.add_to(total, units[sites.index(z)], w)
                assert not total
                basis.append(vec)
        assert len(basis) == (t - 1) // 2
    # the strict containment of the concluding remarks
    a, b = (4, 3), (1, 0)
    assert K.symmetric(a, b)
    aa, bb = (8, 6), (2, 0)
    g, t = K.modulus(a, b), 2
    f = lambda q, M: sum((2 * r - M) % q == 0 for r in range(q))          # noqa: E731
    assert ((t - 1) * g - f(t * g, t * 4) + f(g, 4)) // 2 == 0           # A_off(2C) = 0
    expected = Counter({(1, 5, 6): 1, (1, 4, 7): -1})
    assert K.unit(aa, bb, 1) == expected == K.unit(aa, bb, 7)
    assert kernel_dim(aa, bb) > 0 == kernel_dim(a, b)
    # cor:nullity-increment at modulus one, nonsymmetric dense cores of orders 2 and 3
    n_inc = 0
    for a, b in K.dense_boards(8, 3):
        if K.symmetric(a, b) or K.modulus(a, b) != 1:
            continue
        base = kernel_dim(a, b)
        for t in range(2, 7):
            tn = kernel_dim(tuple(t * x for x in a), tuple(t * y for y in b))
            assert tn - base == (t - 1) // 2, (a, b, t)
            n_inc += 1
    assert n_inc > 20
    print("PASS (D) ex:dilation-ray: t = 1..9 independent cofactors, nullity floor((t-1)/2), explicit basis; "
          "strict containment at A=(4,3), B=(1,0); cor:nullity-increment on %d (core, t) cases at modulus one" % n_inc)


def check_restoration_rigidity(max_area=12):
    table = defaultdict(list)
    n_diag = 0
    for rows, gaps, a, b in profile_diagrams(max_area):
        table[tuple(sorted(K.determinant(a, b).items()))].append((a, b))
        n_diag += 1
    nontrivial = sum(1 for v in table.values() if len({normalize_orbit(m) for m in v}) > 1)

    def mates_ok(A, B, Zs):
        x = tuple(sorted(A + Zs, reverse=True))
        y = tuple(sorted(B + Zs, reverse=True))
        key = tuple(sorted(K.determinant(x, y).items()))
        rot = rotate(x, y)
        mates = {normalize_pair(*m) for m in table[key]}
        assert mates == {normalize_pair(x, y), normalize_pair(*rot)}, (A, B, Zs, mates)

    n_cores = n_restor = n_double = 0
    unequal_possible = 0
    for N in range(3, max_area + 1):
        for k in range(2, 6):
            for As in combinations(range(1, N), k - 1):
                for Bs in combinations(range(1, N), k - 1):
                    A = (N,) + tuple(sorted(As, reverse=True))
                    B = tuple(sorted(Bs, reverse=True)) + (0,)
                    if len(set(A) | set(B)) < 2 * k or A[-1] <= B[0]:
                        continue                                        # dense: a_n > b_1
                    area = sum(A) - sum(B)
                    if area > max_area:
                        continue
                    kd = kernel_dim(A, B)
                    sym = K.symmetric(A, B)
                    sites = K.available(A, B)
                    if sym:
                        assert kd == len(sites) // 2
                    if kd:
                        unequal_possible += 1
                        continue
                    n_cores += 1
                    for r in range(len(sites) + 1):
                        for Zs in combinations(sites, r):
                            mates_ok(A, B, Zs)
                            n_restor += 1
                    if not sym and K.modulus(A, B) == 1 and 2 * area <= max_area:
                        A2, B2 = tuple(2 * x for x in A), tuple(2 * y for y in B)
                        assert kernel_dim(A2, B2) == 0
                        for r in range(len(K.available(A2, B2)) + 1):
                            for Zs in combinations(K.available(A2, B2), r):
                                mates_ok(A2, B2, Zs)
                                n_double += 1
    assert n_cores > 5 and n_restor > 50
    print("PASS (E) cor:independent-restorations: %d diagrams through %d cells (%d nontrivial classes); %d dense cores "
          "with K(C) = 0 (%d with K != 0 skipped), %d restorations rigid, %d restorations of doubles rigid"
          % (n_diag, max_area, nontrivial, n_cores, unequal_possible, n_restor, n_double))


def normalize_orbit(m):
    a, b = m
    return min(normalize_pair(a, b), normalize_pair(*rotate(a, b)))


def main():
    check_profiles_and_cores()
    check_edge_normalization()
    check_dilation_examples()
    check_restoration_rigidity()
    print("ALL PASS")


if __name__ == "__main__":
    main()
