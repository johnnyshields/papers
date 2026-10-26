"""The top-deletion descent, proved rather than measured.

Under an overlap-one top seam the whole capped cofactor vector of A is the
cofactor vector of A with its top row deleted:

    C_0(A) = P_r(C(Abar)),          C_{r+d}(A) = -C_d(Abar),

with r the top row length.  This script checks the two identities exactly,
checks the index bookkeeping the proof runs on, and checks that the overlap-one
hypothesis is load-bearing -- a guard that cannot fail is not a guard.

The proof both identities admit, once `lem:cofactor-factorization` is available:

  * C_0(A) = s_A by nu^(0) = mu, and A = Abar.(r) exactly when the top seam has
    overlap one, so P_r(C(Abar)) = s_{Abar.(r)} = s_A by `eq:cofactor-schur`.
  * For j >= 0, nu^(j+1)(A) has first entry lambda_0, so lambda/nu^(j+1) has an
    empty top row and equals lambdabar/nu', where nu' agrees with
    nu^(j)(Abar) in every entry but the first: mu_0 + 1 against lambda_1.
    Overlap one is exactly mu_0 + 1 = lambda_1.  The sign is the shift of the
    column index by one.

So the hypothesis enters once, in one entry of one partition, and the descent
is a corollary of the cofactor factorization rather than a census.
"""

import sys
from collections import defaultdict

from check_cofactor_factorization_and_reconstruction import (
    cap_matrix, connected_shapes, det, h, padd, pmul, pscal,
)

SIZE_CAP = 12
ROW_CAP = 5


def cofactors(lam, mu):
    """The signed maximal cofactor vector (C_0, ..., C_n) and the shifts d_j."""
    M, a, b = cap_matrix(lam, mu)
    n = len(lam)
    cof = []
    for j in range(n + 1):
        minor = [row[:j] + row[j + 1:] for row in M]
        cof.append(pscal((-1) ** j, det(minor)))
    d = [b[0] - b[j] for j in range(n + 1)]
    return cof, d


def P(cof, d, k):
    """P_k(C) = sum_j C_j h_{k + d_j}."""
    out = {}
    for j, c in enumerate(cof):
        out = padd(out, pmul(c, h(k + d[j])))
    return out


def neg(f):
    return pscal(-1, f)


tested = overlap_one = controls = 0
by_rows = defaultdict(int)

for lam, mu in connected_shapes(SIZE_CAP, ROW_CAP):
    n = len(lam)
    if n < 2:
        continue
    tested += 1
    top_overlap = lam[1] - mu[0]
    assert top_overlap >= 1, (lam, mu)

    lam_bar, mu_bar = lam[1:], mu[1:]
    assert mu_bar[-1] == 0
    cof_A, d_A = cofactors(lam, mu)
    cof_B, d_B = cofactors(lam_bar, mu_bar)
    r = lam[0] - mu[0]

    if top_overlap == 1:
        overlap_one += 1
        by_rows[n] += 1
        # index bookkeeping: A_1 = d_1 = r, and the two grids differ by r
        A1 = lam[0] - lam[1] + 1
        assert A1 == r == d_A[1], (lam, mu, A1, r, d_A[1])
        assert [d_A[j + 1] - r for j in range(n)] == d_B, (lam, mu)
        # the two identities
        assert cof_A[0] == P(cof_B, d_B, r), ("claim 1", lam, mu)
        for j in range(n):
            assert cof_A[j + 1] == neg(cof_B[j]), ("claim 2", lam, mu, j)
        # every cofactor of A is now expressed through Abar
        assert len(cof_A) == len(cof_B) + 1
    else:
        # the hypothesis is load-bearing: claim 2 at j >= 1 must be able to fail
        bad = any(cof_A[j + 1] != neg(cof_B[j]) for j in range(n))
        if bad:
            controls += 1

assert overlap_one > 0 and controls > 0, (overlap_one, controls)
print("connected diagrams with >= 2 rows, size <= %d, rows <= %d: %d"
      % (SIZE_CAP, ROW_CAP, tested))
print("overlap-one top seam: %d, both identities exact on every one" % overlap_one)
print("  by row count:", dict(sorted(by_rows.items())))
print("top overlap >= 2: %d of %d break claim 2, so the hypothesis is load-bearing"
      % (controls, tested - overlap_one))

# j = 0 needs no hypothesis at all: nu^(1) deletes mu_0 outright.
free = 0
for lam, mu in connected_shapes(SIZE_CAP, ROW_CAP):
    if len(lam) < 2 or lam[1] - mu[0] == 1:
        continue
    cof_A, _ = cofactors(lam, mu)
    cof_B, _ = cofactors(lam[1:], mu[1:])
    assert cof_A[1] == neg(cof_B[0]), (lam, mu)
    free += 1
print("C_1(A) = -C_0(Abar) holds unconditionally: %d diagrams off the locus" % free)

print("ALL PASS")
