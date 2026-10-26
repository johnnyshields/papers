"""Does the symmetric dense kernel carry a provable lower bound?

Paper section `sec:restoration` (Common beta entries and first variations).

The symmetric clause of the paper's cofactor theorem says the signed cofactors satisfy
D_ij = D_{n+1-j,n+1-i}.  If that is so, a short substitution should give

    U_z = U_{N-z}    for every available position z

on a symmetric core, and hence one relation per two-element orbit of z -> N-z, i.e.

    dim K(C) >= floor(|Omega_C| / 2).

This script tests the three steps that argument needs, exactly and over a stated window:

  (1) Omega_C is invariant under z -> N-z;
  (2) U_z = U_{N-z} as polynomials, coefficient for coefficient;
  (3) the orbit count is floor(|Omega_C|/2) in both parities, and the lower bound holds;
  (4) separately, whether the bound is TIGHT -- which is the half the bank row calls open, and
      which this script reports rather than assumes.

A fixed point z = N/2 is tracked on its own, because whether it contributes a relation is a
one-off that would move the dimension by one.

Finite evidence, corroboration only.  Nothing here is a premise for a statement in the paper; a
proof is what would license one, and the point of (2) is to test whether that proof is available.
"""

import sys
from fractions import Fraction
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_widen_containment import (  # noqa: E402
    cofactors, is_symmetric, omega, unit, rank_and_nullity, fmt,
)

WINDOW = dict(orders=(2, 3, 4), max_N=14)


def symmetric_dense_cores(n, max_N):
    """Strict A=(N=a_1>...>a_n), B=(b_1>...>b_n=0), dense (a_n>b_1), symmetric."""
    out = []
    for N in range(2, max_N + 1):
        for rest_a in combinations(range(1, N), n - 1):
            A = (N,) + tuple(sorted(rest_a, reverse=True))
            for rest_b in combinations(range(1, A[-1]), n - 1):
                B = tuple(sorted(rest_b, reverse=True)) + (0,)
                if A[-1] > B[0] and is_symmetric(A, B):
                    out.append((A, B))
    return out


def main():
    stats = dict(cores=0, positions=0, unit_pairs=0, fixed_points=0,
                 omega_invariant=0, tight=0, slack=0, nonfixed=0)
    slack_examples = []

    for n in WINDOW["orders"]:
        cores = symmetric_dense_cores(n, WINDOW["max_N"])
        print(f"order {n}: {len(cores)} symmetric dense cores, N <= {WINDOW['max_N']}")
        for A, B in cores:
            stats["cores"] += 1
            N = A[0]
            om = omega(A, B)
            stats["positions"] += len(om)

            # (1) Omega invariant under z -> N-z
            assert sorted(om) == sorted(N - z for z in om), f"Omega not invariant {A} {B}"
            stats["omega_invariant"] += 1

            D = cofactors(A, B)
            U = {z: unit(A, B, z, D) for z in om}

            # (2) U_z = U_{N-z}, coefficient for coefficient
            for z in om:
                assert U[z] == U[N - z], (
                    f"U_z != U_(N-z) at z={z} on {A} {B}:\n"
                    f"   U_z    = {fmt(U[z])}\n   U_(N-z) = {fmt(U[N-z])}")
                if 2 * z == N:
                    stats["fixed_points"] += 1
                else:
                    stats["nonfixed"] += 1
            # orbits, not positions: each two-element orbit holds TWO positions
            stats["unit_pairs"] += len(om) // 2

            # (3) the orbit count and the lower bound
            orbits = len({frozenset((z, N - z)) for z in om if 2 * z != N})
            assert orbits == len(om) // 2, (
                f"orbit count {orbits} != floor(|Omega|/2)={len(om)//2} on {A} {B}")
            _, basis = rank_and_nullity([U[z] for z in om])
            dim = len(basis)
            assert dim >= len(om) // 2, (
                f"LOWER BOUND FAILS on {A} {B}: dim K(C)={dim} < {len(om)//2}")

            # (4) is it tight?  reported, never assumed
            if dim == len(om) // 2:
                stats["tight"] += 1
            else:
                stats["slack"] += 1
                if len(slack_examples) < 5:
                    slack_examples.append((A, B, len(om), dim, len(om) // 2))

    print()
    print("RESULTS")
    print(f"  symmetric dense cores enumerated   {stats['cores']}")
    print(f"  available positions                {stats['positions']}")
    print(f"  Omega invariant under z -> N-z     {stats['omega_invariant']} of {stats['cores']}")
    print(f"  U_z = U_(N-z) verified at          {stats['positions']} positions")
    print(f"    of which non-fixed positions     {stats['nonfixed']}")
    print(f"    two-element ORBITS (positions/2)  {stats['unit_pairs']}")
    print(f"    of which fixed points z = N/2    {stats['fixed_points']}")
    print(f"  LOWER BOUND dim >= floor(|Om|/2)   holds on all {stats['cores']}")
    print(f"    tight (equality)                 {stats['tight']}")
    print(f"    strict (dim exceeds the bound)   {stats['slack']}")
    if slack_examples:
        print("  cores where the bound is NOT tight -- the upper bound is the open half:")
        for A, B, o, d, lb in slack_examples:
            print(f"      A={A} B={B}  |Omega|={o}  dim={d}  bound={lb}")

    # non-vacuity: a guard that cannot fail is not a guard
    assert stats["cores"] >= 40, stats
    assert stats["positions"] >= 200, stats
    assert stats["unit_pairs"] >= 100, stats
    assert 2 * stats["unit_pairs"] == stats["nonfixed"], (
        "orbit count and non-fixed position count disagree", stats)
    assert stats["fixed_points"] >= 1, "no fixed point z = N/2 was ever exercised"
    print("\n  non-vacuity: every sweep fired, including at least one fixed point")
    print("\nALL PASS")


if __name__ == "__main__":
    main()
