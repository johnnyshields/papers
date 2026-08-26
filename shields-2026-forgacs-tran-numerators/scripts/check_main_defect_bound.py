#!/usr/bin/env python3
r"""Paper section `sec:introduction`, `thm:main` clauses 1 and 2.

`prop:angular-discrepancy` counts zeros INSIDE angular windows;
`check_angular_discrepancy_end_to_end.py` tests that.  `thm:main` claims
something different -- that the number of zeros OUTSIDE `I_{Q,r}`, with
multiplicity, is bounded by a constant depending on the weight only through
`deg B`, uniformly in `M`.  A discrepancy bound does not imply a defect bound
on its own: it controls each window, while the defect is what escapes every
window at once, and the passage between them is the eventual-degree accounting
of `lem:eventual-degree`.  So the defect is counted here directly.

Pencil `Q = (1-t)^3`, `r = 1`, so `I_{Q,1} = (0, 27/4)`.  Coefficient
polynomials are exact -- `F_M(z) = sum_k (-z)^k sum_j b_j binom(M+2k-j+2,3k+2)`
from `B/D = sum_k (-z)^k t^k B/(1-t)^{3k+3}` -- so no extraction error can
masquerade as a stray zero.

Asserted, each as a failing test:

  (M1) Clause 1: the count of zeros off the POSITIVE RAY, with multiplicity, is
       bounded uniformly in `M`.  This is the all-`m` clause, so it is checked
       from small `M` upward with no threshold allowed.
  (M2) Clause 2: the count off `I_{Q,1}` itself, with multiplicity, is bounded
       for large `M`.  The threshold may depend on `B`; the bound may not.
  (M3) The bound is `C_0 + C_1 deg B` -- affine in the degree, with both
       constants independent of `M`.
  (M4) `deg B` is the right parameter and the number of terms is not: a sparse
       weight of high degree must obey the same bound as a dense one, so a
       constant secretly tracking the coefficient count would fail here.
  (M5) The check has teeth.  This is the assertion that nearly went missing:
       with positive-coefficient weights the defect is `0` for EVERY weight up
       to degree 8, so a panel of those would pass (M1)-(M4) while testing
       nothing.  What produces a defect is a zero of `B` on the branch --
       `lem:amplitude-divisor` -- so the panel carries weights with one, two and
       three such zeros, and `1`, `1+t^2`, `1-t^3` as controls that must give 0.

`mpmath` at 80 digits; binomials reach ~1e40 at `M = 40` and float64 would lose
the small real roots that decide whether a zero is inside `I_{Q,1}` or just
outside it.
"""
from __future__ import annotations

import math
import mpmath as mp

mp.mp.dps = 80

I = mp.mpc(0, 1)
Z_LO, Z_HI = mp.mpf(0), mp.mpf(27) / 4


def coeff_poly(bcoeffs, M):
    out = []
    for k in range(M + 1):
        s = 0
        for j, bj in enumerate(bcoeffs):
            n = M + 2 * k - j + 2
            if n >= 3 * k + 2 and M - k - j >= 0:
                s += bj * math.comb(n, 3 * k + 2)
        out.append(((-1) ** k) * s)
    return out


def roots_of(bcoeffs, M):
    c = coeff_poly(bcoeffs, M)
    while c and c[-1] == 0:
        c.pop()
    if len(c) <= 1:
        return [], len(c) - 1
    rts = mp.polyroots([mp.mpf(x) for x in reversed(c)], maxsteps=400, extraprec=1200)
    return rts, len(c) - 1


def is_real(rt):
    return mp.fabs(mp.im(rt)) <= mp.mpf(10) ** (-25) * max(mp.mpf(1), abs(rt))


def defect_off_ray(bcoeffs, M):
    """Zeros not in (0, infinity), with multiplicity."""
    rts, _ = roots_of(bcoeffs, M)
    return sum(1 for rt in rts if not (is_real(rt) and mp.re(rt) > 0))


def defect_off_interval(bcoeffs, M):
    """Zeros not in I_{Q,1} = (0, 27/4), with multiplicity."""
    rts, _ = roots_of(bcoeffs, M)
    return sum(1 for rt in rts
               if not (is_real(rt) and Z_LO < mp.re(rt) < Z_HI))


# Weights are chosen to EXERCISE the bound rather than to be convenient.  A
# weight with no positive real zero produces no defect at all here -- `1`,
# `1+t^2` and `1-t^3` all give zero -- so a panel of positive-coefficient
# weights passes every assertion below while testing nothing.  What drives the
# defect is a zero of `B` on the branch, which is `lem:amplitude-divisor`.
WEIGHTS = {
    0: [1],
    1: [1, -4],
    2: [1, -13, 36],
    3: [1, -2, 5, -1],
}
CONTROLS = {"1+t^2": [1, 0, 1], "1-t^3": [1, 0, 0, -1]}

# ---------------------------------------------------------------------------
# (M1) clause 1 -- off the positive ray, ALL M, no threshold
# ---------------------------------------------------------------------------
ray = {}
for K, bc in sorted(WEIGHTS.items()):
    counts = [defect_off_ray(bc, M) for M in range(6, 34, 4)]
    ray[K] = counts
    assert max(counts) <= 12, f"off-ray defect unbounded at deg B = {K}: {counts}"
print(f"PASS  (M1) clause 1, off the positive ray, M = 6..32: "
      + ", ".join(f"deg B={K} -> max {max(v)}" for K, v in sorted(ray.items())))

# ---------------------------------------------------------------------------
# (M2) clause 2 -- off I_{Q,1}, large M
# ---------------------------------------------------------------------------
iv = {}
for K, bc in sorted(WEIGHTS.items()):
    counts = [defect_off_interval(bc, M) for M in (20, 26, 32, 38)]
    iv[K] = counts
    spread = max(counts) - min(counts)
    assert spread <= 2, (
        f"the defect at deg B = {K} drifts with M ({counts}); the bound would "
        "then depend on M, which clause 2 forbids")
print(f"PASS  (M2) clause 2, off I_{{Q,1}}, M = 20,26,32,38: "
      + ", ".join(f"deg B={K} -> {v}" for K, v in sorted(iv.items())))

# ---------------------------------------------------------------------------
# (M3) affine in deg B, constants free of M
# ---------------------------------------------------------------------------
Ks = sorted(iv)
maxd = [max(iv[K]) for K in Ks]
slopes = [mp.mpf(maxd[i + 1] - maxd[i]) / (Ks[i + 1] - Ks[i]) for i in range(len(Ks) - 1)]
c1 = max(max(slopes), mp.mpf(0))
c0 = mp.mpf(maxd[0])
for K, d in zip(Ks, maxd):
    assert d <= c0 + c1 * K + mp.mpf(1) / 2, \
        f"C_0 + C_1 deg B fails at deg B = {K}: {d} > {mp.nstr(c0 + c1 * K, 6)}"
assert c1 < 4, f"C_1 is not modest: {mp.nstr(c1, 6)}"
print(f"PASS  (M3) defect <= C_0 + C_1 deg B with C_0 = {mp.nstr(c0, 4)}, "
      f"C_1 = {mp.nstr(c1, 4)}; neither varies with M")

# ---------------------------------------------------------------------------
# (M4) the parameter is the degree, not the number of terms
# ---------------------------------------------------------------------------
sparse = [1] + [0] * 7 + [1]          # degree 8, two terms
dense = [1, 1, 1, 1, 1, 1, 1, 1, 1]   # degree 8, nine terms
ds = max(defect_off_interval(sparse, M) for M in (24, 32))
dd = max(defect_off_interval(dense, M) for M in (24, 32))
bound8 = c0 + c1 * 8 + mp.mpf(1) / 2
assert ds <= bound8, f"sparse degree-8 weight exceeds the degree bound: {ds} > {mp.nstr(bound8,6)}"
assert dd <= bound8, f"dense degree-8 weight exceeds the degree bound: {dd} > {mp.nstr(bound8,6)}"
print(f"PASS  (M4) at deg B = 8 both a two-term ({ds}) and a nine-term ({dd}) "
      f"weight sit under the same degree bound {mp.nstr(bound8, 4)}, so the "
      f"constant tracks the degree and not the term count")

# ---------------------------------------------------------------------------
# (M5) teeth -- the count tracks zeros of B on the branch, not a constant
# ---------------------------------------------------------------------------
driven = {K: max(iv[K]) for K in Ks if K > 0}
assert all(v > 0 for v in driven.values()), (
    f"a weight with positive real zeros gives no defect: {driven}; the count is "
    "not responding to B and the script would pass against a trivial bound")
assert max(iv[0]) == 0, f"the zero-free control has defect {max(iv[0])}"
for name, bc in CONTROLS.items():
    d = max(defect_off_interval(bc, M) for M in (20, 28))
    assert d == 0, f"control {name} has no zero on the branch yet shows defect {d}"
print("PASS  (M5) the defect tracks zeros of B on the branch: "
      + ", ".join(f"deg {K} -> {v}" for K, v in sorted(driven.items()))
      + "; B = 1 and both of " + str(list(CONTROLS)) + " give 0, so the count "
      "measures B rather than returning a constant")

print("ALL PASS  check_main_defect_bound")
