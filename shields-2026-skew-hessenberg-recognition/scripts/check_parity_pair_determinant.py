"""Confirm the obstruction remark's witness equality by symbolic determinants.

The remark's two profiles must have equal skew Schur functions for the
zero-free hypothesis to be shown non-removable.  This check establishes that
by forming the Jacobi-Trudi matrix over free commuting symbols and taking its
determinant with SymPy.

`check_parity_pair_equality.py` establishes the same equality by an explicit
signed permutation sum over integer exponent multisets.  The two share no code
and no algorithm: one calls a general determinant routine on a symbolic matrix,
the other sums 720 signed terms by hand.  A defect in either would have to be
reproduced independently in the other to escape both.
"""
from itertools import permutations

from sympy import Integer, Matrix, expand, symbols

F_ROWS, F_GAPS = (4, 5, 4, 3, 2, 1), (2, 3, 2, 1, 0)
H_ROWS, H_GAPS = (1, 2, 3, 4, 4, 5), (0, 1, 2, 2, 3)

HMAX = 40
H = {0: Integer(1)}
for _k in range(1, HMAX + 1):
    H[_k] = symbols("h%d" % _k)
for _k in range(-HMAX, 0):
    H[_k] = Integer(0)


def connected(rows, gaps):
    """g_i is the overlap minus one, so 0 <= g_i < min(r_i, r_{i+1})."""
    return all(0 <= g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps))


def betas(rows, gaps):
    """Profile (r; g) to beta lists (x, y), normalized by y_n = 0."""
    n = len(rows)
    x = [0] * n
    y = [0] * n
    x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return tuple(x), tuple(y)


def schur(x, y):
    """s = det(h_{x_i - y_j}), expanded over the free h-symbols."""
    n = len(x)
    return expand(Matrix(n, n, lambda i, j: H[x[i] - y[j]]).det())


def monomial_count(poly):
    return len(poly.as_ordered_terms()) if poly != 0 else 0


def main():
    checks = 0
    assert connected(F_ROWS, F_GAPS), "F is not connected"
    assert connected(H_ROWS, H_GAPS), "H is not connected"
    assert sum(F_ROWS) == sum(H_ROWS) == 19, "areas differ"
    checks += 3

    xF, yF = betas(F_ROWS, F_GAPS)
    xH, yH = betas(H_ROWS, H_GAPS)
    sF, sH = schur(xF, yF), schur(xH, yH)

    assert expand(sF - sH) == 0, "THE WITNESS EQUALITY FAILS"
    assert monomial_count(sF) == monomial_count(sH) == 63, "unexpected monomial count"
    checks += 2

    rot = (tuple(reversed(F_ROWS)), tuple(reversed(F_GAPS)))
    assert rot != (H_ROWS, H_GAPS), "H is merely the rotation of F"
    checks += 1

    fired = 0
    for rows, gaps in (
        ((1, 2, 3, 4, 5, 5), H_GAPS),
        (H_ROWS, (0, 1, 2, 2, 2)),
        ((4, 5, 4, 3, 2, 2), F_GAPS),
    ):
        if not connected(rows, gaps):
            continue
        xB, yB = betas(rows, gaps)
        if expand(sF - schur(xB, yB)) != 0:
            fired += 1
    assert fired == 3, "a control did not fire: the comparison cannot detect a change"
    checks += fired

    print("F betas x=%s y=%s" % (xF, yF))
    print("H betas x=%s y=%s" % (xH, yH))
    print("monomials: %d and %d; equal: True; rotation of each other: False"
          % (monomial_count(sF), monomial_count(sH)))
    print("firing controls that broke the equality: %d of 3" % fired)
    print("checks: %d" % checks)
    print("ALL PASS")


if __name__ == "__main__":
    main()
