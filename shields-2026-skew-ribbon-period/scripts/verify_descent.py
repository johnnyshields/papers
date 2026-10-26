r"""Paper section `sec:descent` (Strict descent and actual realization).

Targets the erosion and inflation facts the subsection on erosion, inflation and zero-free
classes consumes (`prop:core-full`): the exact area drop of erosion, inverse class transport
between a connected zero-free non-line diagram and its erosion, and the raising identity
`s_{I(U)} = h_1^r s_U(h_j -> h_{j+1} / h_1)` on the no-`-1` domain.

Erosion keeps the cells with an eastern neighbor in their original rows; one-step inflation
adds one to every row length and to every adjacent overlap-minus-one (rows built top to bottom
from the profile).  Both are implemented from those sentences on actual cell sets.  Asserted over
all connected skew diagrams up to the stated size: the area of the erosion is `|S| - r(S)`; the
erosion of a connected zero-free non-line diagram is connected and inflation of the erosion
returns `S` (and erosion of the inflation returns the erosion's source); the raising identity holds
(exact `Fraction` evaluation at two alphabets) for every `U` with no Jacobi--Trudi index `-1`,
and fails for some `U` outside that domain, which shows the domain is load-bearing.
Sampled: diagrams up to 9 cells in 4 rows and 5 columns.
"""
from fractions import Fraction

from check_regroup_mixed import skew_shapes, is_connected, translate, smul
from _schur_common import alphabet, row_intervals, determinant, schur
from check_contact_currents import beta_lists


def normalize(S):
    rows = min(x[0] for x in S)
    cols_by_row = {i: min(x[1] for x in S if x[0] == i) for i in {x[0] for x in S}}
    # translate so the southwest cell (largest row, smallest column) matches the profile convention
    c = min(x[1] - x[0] for x in S)
    lo = min(x[0] for x in S if x[1] - x[0] == c)
    return translate((-lo, -(lo + c)), S)


def erosion(S):
    return frozenset(x for x in S if (x[0], x[1] + 1) in S)


def profile(S):
    """Row lengths top to bottom and adjacent overlaps (overlap in columns)."""
    rows = sorted({x[0] for x in S})
    a, b = row_intervals(S)
    lens = [b[i] - a[i] for i in range(len(rows))]
    ovl = [max(0, min(b[i], b[i + 1]) - max(a[i], a[i + 1])) for i in range(len(rows) - 1)]
    return lens, ovl


def from_profile(lens, ovl):
    cells = set()
    a, b = 0, lens[0]
    for j in range(a, b):
        cells.add((0, j))
    for i in range(1, len(lens)):
        b = a + ovl[i - 1]
        a = b - lens[i]
        for j in range(a, b):
            cells.add((i, j))
    return normalize(frozenset(cells))


def inflate(S):
    lens, ovl = profile(S)
    return from_profile([l + 1 for l in lens], [o + 1 for o in ovl])


def has_minus_one(S):
    a, b = row_intervals(S)
    n = len(a)
    return any(b[i] - a[j] - i + j == -1 for i in range(n) for j in range(n))


def raising(U, h):
    """`h_1^r s_U(h_j -> h_{j+1} / h_1)`, `r = r(U)`."""
    a, b = row_intervals(U)
    n = len(a)
    def g(j):
        return Fraction(1) if j == 0 else (Fraction(0) if j < 0 else h(j + 1) / h(1))
    return h(1) ** n * determinant([[g(b[i] - a[j] - i + j) for j in range(n)] for i in range(n)])


def main():
    shapes = [normalize(S) for S in skew_shapes(9, 4, 5) if is_connected(S)]
    n_area = n_class = n_raise = 0
    outside_fail = False
    for S in shapes:
        rows = len({x[0] for x in S})
        E = erosion(S)
        assert len(E) == len(S) - rows                                    # exact area drop
        n_area += 1
        X, Y = beta_lists(S)
        zero_free = not (set(X) & set(Y))
        line = rows == 1 or len({x[1] for x in S}) == 1
        if zero_free and not line and E:
            assert is_connected(E)
            assert inflate(normalize(E)) == normalize(S), sorted(S)
            n_class += 1
        for h in (alphabet(21), alphabet(22)):
            lhs = schur(inflate(S), h)
            if not has_minus_one(S):
                assert lhs == raising(S, h), sorted(S)
                n_raise += 1
            elif lhs != raising(S, h):
                outside_fail = True
    print(f"erosion area drops {n_area}, inflation-of-erosion {n_class}, raising identity {n_raise}, "
          f"fails outside the no(-1) domain: {outside_fail}")
    assert n_area > 0 and n_class > 0 and n_raise > 0 and outside_fail
    print("PASS")


if __name__ == "__main__":
    main()
