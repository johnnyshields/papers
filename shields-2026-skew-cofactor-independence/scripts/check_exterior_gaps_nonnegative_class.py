#!/usr/bin/env python3
r"""`lem:exterior-gaps`, `eq:border`, `eq:corner-coefficient`, and the steps of `thm:nonnegative-rigidity`'s
induction that are not the conclusion: asserted for EVERY connected diagram through 14 cells whose
Jacobi-Trudi matrix has no negative index (x_n >= y_1), including the boundary x_n = y_1 where genuine
units sit on the board.

For each such diagram with n >= 3 rows:
  - the maximal corner cofactor T (lists (x_2..x_n), (y_1..y_{n-1})) is connected, has n-1 rows, has
    least index x_n - y_1 >= 0 and a strictly positive diagonal;
  - the full lists have the form of `eq:border` with alpha, beta > 0 read off T and N = u_1 - v_m + alpha + beta;
  - the largest generator index of s_D with h_N set to zero is M = N - min(alpha, beta);
  - for alpha < beta its coefficient is (-1)^n s of T with the top row beta raised by alpha; for beta < alpha
    it is (-1)^n s of T with the bottom column beta lowered by beta; for alpha = beta the coefficient of h_M^2
    is nonzero;
  - `eq:corner-coefficient`: (-1)^(n-1) [h_N] s_D is the determinant on the corner lists and is nonzero,
    its minimum-square monomial (padded with zeros) reads the sorted overlap gaps.
The count of diagrams outside the hypothesis (x_n < y_1) on which the lemma's conclusions fail is reported
beside it.
"""
from collections import Counter
from itertools import product

import check_cofactor_dilation as K

CMAX = 14          # nonnegative-index diagrams
OUTSIDE_MAX = 9    # the control population


def lemma_claims_hold(a, b, poly, n):
    """The conclusions of the lemma for the lists (a, b); False if any fails."""
    N = a[0]
    u, v = a[1:], b[:-1]
    alpha, beta = a[0] - a[1], b[-2] - b[-1]
    remainder = Counter({mono: c for mono, c in poly.items() if N not in mono})
    M = max(j for mono in remainder for j in mono)
    if M != N - min(alpha, beta):
        return False
    top = K.derivative(remainder, M)
    if alpha < beta:
        ext = K.determinant((u[0] + alpha,) + u[1:], v)
        return top == Counter({w: (-1) ** n * c for w, c in ext.items()})
    if beta < alpha:
        ext = K.determinant(u, v[:-1] + (v[-1] - beta,))
        return top == Counter({w: (-1) ** n * c for w, c in ext.items()})
    return bool(K.derivative(top, M))


def main():
    n_ok = n_equal = n_top = n_bot = n_unit_boundary = 0
    outside = outside_fail = 0
    for area in range(3, CMAX + 1):
        for rows in K.compositions(area):
            n = len(rows)
            if n < 3:
                continue
            for gaps in product(*[range(min(x, y)) for x, y in zip(rows, rows[1:])]):
                a, b = K.profile_betas(rows, gaps)
                if a[-1] < b[0] and area > OUTSIDE_MAX:
                    continue
                N = a[0]
                u, v = a[1:], b[:-1]
                T_poly = K.determinant(u, v)
                poly = K.determinant(a, b)
                # eq:corner-coefficient
                corner = K.derivative(poly, N)
                assert Counter({m: (-1) ** (n - 1) * c for m, c in corner.items()}) == T_poly and T_poly
                least = min(T_poly, key=lambda w: sum(j * j for j in w))
                assert (0,) * (n - 1 - len(least)) + least == tuple(sorted(gaps))
                if a[-1] < b[0]:
                    outside += 1
                    outside_fail += not lemma_claims_hold(a, b, poly, n)
                    continue
                m = n - 1
                assert u[-1] >= v[0]                                   # least index of T is still >= 0
                assert all(u[i] - v[i] > 0 for i in range(m))          # strictly positive diagonal
                alpha, beta = a[0] - a[1], b[-2] - b[-1]
                assert alpha > 0 and beta > 0
                assert a == (u[0] + alpha,) + u and b == v + (v[-1] - beta,)          # eq:border
                assert N == u[0] - v[-1] + alpha + beta
                assert lemma_claims_hold(a, b, poly, n), ("lemma", a, b)
                n_unit_boundary += a[-1] == b[0]
                n_top += alpha < beta
                n_bot += beta < alpha
                n_equal += alpha == beta
                n_ok += 1
    assert n_ok > 100 and n_top > 10 and n_bot > 10 and n_equal > 10 and n_unit_boundary > 10
    print("%d nonnegative-index diagrams with n >= 3 through %d cells (%d with x_n = y_1): border form, corner "
          "coefficient, largest remaining index N - min(alpha, beta) and its coefficient "
          "(alpha<beta %d, beta<alpha %d, alpha=beta %d)" % (n_ok, CMAX, n_unit_boundary, n_top, n_bot, n_equal))
    print("outside the hypothesis (x_n < y_1): %d diagrams, the lemma's conclusions fail on %d" % (outside, outside_fail))
    print("ALL PASS")


if __name__ == "__main__":
    main()
