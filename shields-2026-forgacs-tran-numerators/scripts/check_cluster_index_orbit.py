#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `eq:lower-cluster-expansion`; `thm:weighted-dominance`.

The cluster enumeration turns on one identity, and it is the difference between
pinning the index `idx_0` by a constant already owned and matching it by hand
against an asymptotic.  A hand match type-checks when it is wrong, so the
identity is asserted here before it is built on.

With `omega_j = e^{(2j-1) pi i / rho}` and `alpha_j = -x_1 omega_j / sin(pi/rho)`
(`Cluster.clusterAngle`, `clusterOmega`, `clusterAlpha`):

  (C1) `alpha_0 * zeta` over the rho-th roots of UNITY `zeta` reproduces exactly
       the set `{alpha_j : j = 0..rho-1}`, elementwise, as an identity rather
       than to a tolerance.  So the principal member's slope times the roots of
       unity IS the alpha family, and no separate identification is needed.

  (C2) The two `omega`s are NOT the same and must not be conflated.  The chart
       variable rotates by rho-th roots of UNITY (`zeta^rho = 1`), because
       `(zeta v)^rho = v^rho` is what puts the rotates on one fiber.  The
       resulting slopes carry `omega_j^rho = -1`.  Both are asserted.

  (C3) The map `j |-> alpha_j` is injective on `0..rho-1`, so the enumeration is
       a bijection onto the fiber rather than a covering with collisions.

  (C4) `rho = 1` is degenerate and its degeneracy is real: `sin(pi/1) = 0`, so
       `alpha_j` divides by zero.  Lean's convention returns `0`; the check here
       is that the mathematical quantity genuinely blows up, i.e. that the
       `rho = 1` endpoint needs a physically separate producer rather than an
       instance of the `rho >= 2` one.

`mpmath` throughout at 60 digits: at `rho = 12` the angles differ by
`2 pi / 12` and the identity is exact, so what is being measured is whether the
residual sits at the precision floor rather than at a small nonzero number.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 60

I = mp.mpc(0, 1)
FLOOR = mp.mpf(10) ** (-50)


def cluster_omega(rho, j):
    return mp.exp((2 * mp.mpf(j) - 1) * mp.pi / rho * I)


def cluster_alpha(x1, rho, j):
    return -mp.mpf(x1) * cluster_omega(rho, j) / mp.sin(mp.pi / rho)


def root_of_unity(rho, k):
    return mp.exp(2 * mp.pi * I * mp.mpf(k) / rho)


# ---------------------------------------------------------------------------
# (C1) alpha_0 times the rho-th roots of unity IS the alpha family
# ---------------------------------------------------------------------------
worst = mp.mpf(0)
for rho in range(2, 13):
    for x1 in (mp.mpf(1) / 3, mp.mpf(1), mp.mpf(7) / 2):
        a0 = cluster_alpha(x1, rho, 0)
        for k in range(rho):
            lhs = a0 * root_of_unity(rho, k)
            rhs = cluster_alpha(x1, rho, k)
            worst = max(worst, abs(lhs - rhs))
assert worst < FLOOR, (
    f"alpha_0 * zeta^k != alpha_k; worst residual {mp.nstr(worst, 8)}. "
    "The enumeration cannot be pinned by the principal slope.")
print(f"PASS  (C1) alpha_0 * (rho-th roots of unity) = {{alpha_j}} elementwise, "
      f"rho = 2..12, worst residual {mp.nstr(worst, 6)} (precision floor)")

# ---------------------------------------------------------------------------
# (C2) the two omegas: chart rotates by zeta^rho = 1, slopes carry omega^rho = -1
# ---------------------------------------------------------------------------
worst_unity = mp.mpf(0)
worst_neg = mp.mpf(0)
for rho in range(2, 13):
    for k in range(rho):
        worst_unity = max(worst_unity, abs(root_of_unity(rho, k) ** rho - 1))
        worst_neg = max(worst_neg, abs(cluster_omega(rho, k) ** rho + 1))
assert worst_unity < FLOOR, f"chart rotation is not a root of unity: {worst_unity}"
assert worst_neg < FLOOR, f"clusterOmega^rho != -1: {worst_neg}"
# and they are genuinely different families
assert abs(cluster_omega(4, 1) - root_of_unity(4, 1)) > mp.mpf(1) / 10, \
    "clusterOmega coincides with a root of unity; the two would be conflatable"
print(f"PASS  (C2) chart rotations satisfy zeta^rho = 1 ({mp.nstr(worst_unity, 6)}) "
      f"while clusterOmega^rho = -1 ({mp.nstr(worst_neg, 6)}); distinct families")

# ---------------------------------------------------------------------------
# (C3) the enumeration is injective
# ---------------------------------------------------------------------------
min_sep = None
for rho in range(2, 13):
    alphas = [cluster_alpha(mp.mpf(1), rho, j) for j in range(rho)]
    for i in range(rho):
        for j in range(i + 1, rho):
            d = abs(alphas[i] - alphas[j])
            min_sep = d if min_sep is None else min(min_sep, d)
assert min_sep > mp.mpf(10) ** (-3), (
    f"the alpha family collides at some rho; min separation {mp.nstr(min_sep, 8)}")
print(f"PASS  (C3) j |-> alpha_j injective on 0..rho-1 for rho = 2..12, "
      f"minimum separation {mp.nstr(min_sep, 6)} at x_1 = 1")

# ---------------------------------------------------------------------------
# (C4) rho = 1 is genuinely degenerate, not merely awkward
# ---------------------------------------------------------------------------
assert abs(mp.sin(mp.pi / 1)) < FLOOR, "sin(pi/1) is not zero"
blowup = [abs(mp.mpf(1) / mp.sin(mp.pi / rho))
          for rho in (mp.mpf(1) + mp.mpf(10) ** (-k) for k in (3, 6, 9, 12))]
for a, b in zip(blowup, blowup[1:]):
    assert b > a * 100, f"1/sin(pi/rho) is not blowing up as rho -> 1: {a} -> {b}"
assert blowup[-1] > mp.mpf(10) ** 11, \
    f"1/sin(pi/rho) failed to exceed 1e11 near rho = 1: {mp.nstr(blowup[-1], 8)}"
print(f"PASS  (C4) alpha_j diverges as rho -> 1 (1/sin reaching "
      f"{mp.nstr(blowup[-1], 6)}), so the rho = 1 endpoint is a separate "
      f"producer and not an instance of the rho >= 2 one")

print("ALL PASS  check_cluster_index_orbit")
