#!/usr/bin/env python3
"""Dependency-free integer audit of the constant-weight positivity certificate.

Uses only the Python standard library (math.comb).  The whole cubic proof
rests on one fact: every Bernstein coefficient S_{n,j} of the projective
transform is nonnegative (paper section 4.1, Lemma 4.2).  This script confirms
that fact over a wide range of m, together with the identities that produce it:

  * the direct residue-class sum S_{n,j}, eq. (4.7);
  * the R-expansion eq. (4.9) (for j >= 2);
  * the six-case closed form eq. (4.8);
  * nonnegativity of every S_{n,j};
  * the projective Bernstein coefficient identity eq. (4.6), an exact integer,
    equal to the direct residue-class coefficient extraction;
  * n+1 = 3m-1 = 2 or 5 (mod 6) and the positive x^2 coefficient (3S = 9d).

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
    """First equality of eq. (4.6): [x^j] P_m from residue-class extraction."""
    total = sum(
        comb(n, k) * ((k + 1) * comb2(n - k, j - k) + (2 * k - n) * comb2(n - k, j - k - 1))
        for k in range(j + 1) if k % 3 == 2
    )
    assert total % 3 == 0
    return total // 3


def main() -> None:
    max_m = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    if max_m < 2:
        raise SystemExit("MAX_M must be at least 2")
    for m in range(2, max_m + 1):
        n = 3 * m - 2
        assert (n + 1) % 6 in (2, 5)
        for j in range(n + 2):
            s = S_sum(n, j)
            if j >= 2:
                assert s == S_from_R(n, j), (m, j)          # eq. (4.9)
            assert 3 * s == three_S_table(n, j), (m, j)     # eq. (4.8)
            assert s >= 0, (m, j, s)                        # the certificate
            num = comb(n + 1, j) * s
            den = 3 * (n + 1)
            assert num % den == 0, (m, j)                   # integrality
            assert num // den == direct_projective_coefficient(n, j), (m, j)  # eq. (4.6)
        assert three_S_table(n, 2) == 9 * (n - 1) and S_sum(n, 2) > 0
    print(f"PASS: eqs. (4.6)-(4.9) and S_{{n,j}} >= 0 for all 2 <= m <= {max_m}")
    print("ALL PASS: check_kernel_stdlib (positivity certificate, no dependencies)")


if __name__ == "__main__":
    main()
