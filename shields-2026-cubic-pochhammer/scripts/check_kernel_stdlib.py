#!/usr/bin/env python3
"""Dependency-free integer audit of the constant-weight positivity certificate.

Uses only the Python standard library (math.comb).  The whole cubic proof
rests on one fact: every Bernstein coefficient S_{n,j} of the projective
transform is nonnegative (paper section `subsec:constant-weight-kernel`,
`lem:bernstein`).  This script confirms that fact over a wide range of m,
together with the identities that produce it:

  * the direct residue-class sum S_{n,j}, `eq:S-def`;
  * the R-expansion `eq:S-R` (for j >= 2);
  * the six-case closed form `eq:S-table`;
  * nonnegativity of every S_{n,j};
  * the projective Bernstein coefficient identity `eq:P-coeff`, an exact integer,
    equal to the direct residue-class coefficient extraction;
  * n+1 = 3m-1 = 2 or 5 (mod 6) and the positive xi^2 coefficient
    (3 S_{n,2} = 9 delta);
  * that the congruence is LOAD-BEARING and not decoration: without it S_{n,j}
    goes negative (67 times for n < 200, first S_{5,6} = -30, S_{6,6} = -15), and
    every failure sits at one of the two residues n = 3m-2 excludes.

Scope: the certificate and `eq:P-coeff`-`eq:S-R`.  J_m itself, the link from `eq:P-coeff`
back to P_m through `eq:P-def`-`eq:P-sum`, and the general inequalities of
`eq:exp-bound-1`-`eq:exp-bound-0` with their increments, are in
verify_kernel.py.

Run:  python3 check_kernel_stdlib.py [MAX_M]   (default MAX_M = 120)
"""
import sys
from math import comb


def comb2(a: int, b: int) -> int:
    return comb(a, b) if 0 <= b <= a else 0


def S_sum(n: int, j: int) -> int:
    return sum(comb(j, k) * (n - k + 1) * (2 * k + 1 - j)
               for k in range(j + 1) if k % 3 == 2)


def R(a: int, j: int) -> int:
    return sum(comb(j, k) for k in range(j + 1) if k % 3 == a % 3)


def S_from_R(n: int, j: int) -> int:
    d = n + 1 - j
    return (d * (2 * j * R(1, j - 1) + (1 - j) * R(2, j))
            + j * (j - 1) * (-2 * R(0, j - 2) + 3 * R(1, j - 1) - R(2, j)))


def three_S_table(n: int, j: int) -> int:
    d = n + 1 - j
    res = j % 6
    if res == 0:
        return d * (2 ** j - 3 * j - 1) - 3 * j * (j - 1)
    if res == 1:
        return d * (2 ** j - 2) - 3 * j * (j - 1)
    if res == 2:
        return d * (2 ** j + 3 * j - 1)
    if res == 3:
        return d * (2 ** j + 3 * j + 1) + 3 * j * (j - 1)
    if res == 4:
        return d * (2 ** j + 2) + 3 * j * (j - 1)
    return d * (2 ** j - 3 * j + 1)


def direct_projective_coefficient(n: int, j: int) -> int:
    """First equality of `eq:P-coeff`: [xi^j] P_m from residue-class extraction."""
    total = sum(
        comb(n, k) * ((k + 1) * comb2(n - k, j - k) + (2 * k - n) * comb2(n - k, j - k - 1))
        for k in range(j + 1) if k % 3 == 2
    )
    assert total % 3 == 0
    return total // 3


def check_congruence_is_load_bearing(n_max: int = 199) -> None:
    """The certificate is FALSE for general n; n+1 = 2,5 (mod 6) is what saves it.

    S_{n,j} >= 0 is the whole cubic proof, and it is not a general fact about the
    residue-class sum: dropping n = 3m-2 and sweeping every n < n_max finds genuine
    negative values, all of them at n+1 = 0 or 1 (mod 6) -- the two residues the
    paper's family cannot take.
    """
    negatives = [(n, j) for n in range(2, n_max + 1)
                 for j in range(n + 2) if S_sum(n, j) < 0]
    assert negatives, "S_{n,j} should go negative once the congruence is dropped"
    assert S_sum(5, 6) == -30 and S_sum(6, 6) == -15
    assert sorted({(n + 1) % 6 for n, _ in negatives}) == [0, 1]
    assert all((n + 1) % 6 not in (2, 5) for n, _ in negatives)
    # delta >= 2 rescues the j = 0 (mod 6) branch, and j = 6 is the only place it
    # is needed: at delta = 1 that branch is -45 at j = 6 and positive from j = 12
    assert (2 ** 6 - 3 * 6 - 1) - 3 * 6 * 5 == -45
    assert 2 * (2 ** 6 - 3 * 6 - 1) - 3 * 6 * 5 == 0
    assert all((2 ** j - 3 * j - 1) - 3 * j * (j - 1) > 0 for j in range(12, 200, 6))
    # both exponential bounds are ATTAINED at m = 3, so neither can be weakened
    assert S_sum(7, 6) == 0 and S_sum(7, 7) == 0
    print(f"PASS: the congruence n+1 = 2,5 (mod 6) is load-bearing -- "
          f"{len(negatives)} negative S_(n,j) without it (n<={n_max}), first "
          f"S_(5,6)=-30, S_(6,6)=-15; and `eq:exp-bound-1`-`eq:exp-bound-0` are attained at m=3")


def main() -> None:
    max_m = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    if max_m < 2:
        raise SystemExit("MAX_M must be at least 2")
    for m in range(2, max_m + 1):
        n = 3 * m - 2
        assert (n + 1) % 6 in (2, 5)
        for j in range(n + 2):
            s = S_sum(n, j)
            d = n + 1 - j
            if j >= 2:
                assert s == S_from_R(n, j), (m, j)          # `eq:S-R`
            assert 3 * s == three_S_table(n, j), (m, j)     # `eq:S-table`
            assert s >= 0, (m, j, s)                        # the certificate
            if j % 6 == 1:
                assert d >= 1, (m, j)                       # j = 1 (mod 6)
            if j % 6 == 0 and j > 0:
                assert d >= 2, (m, j)                       # j = 0 (mod 6), j > 0
            num = comb(n + 1, j) * s
            den = 3 * (n + 1)
            assert num % den == 0, (m, j)                   # integrality
            assert num // den == direct_projective_coefficient(n, j), (m, j)  # `eq:P-coeff`
        assert three_S_table(n, 2) == 9 * (n - 1) and S_sum(n, 2) > 0
    print(f"PASS: `eq:P-coeff`-`eq:S-R`, S_{{n,j}} >= 0, and the delta bounds for all "
          f"2 <= m <= {max_m}")
    check_congruence_is_load_bearing()
    print("ALL PASS: check_kernel_stdlib (positivity certificate, no dependencies)")


if __name__ == "__main__":
    main()
