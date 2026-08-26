#!/usr/bin/env python3
r"""The lower endpoint's clearance bound at general `n`, and the two-zero
reduction its proof runs through.

`thm:weighted-dominance`'s lower endpoint needs

    (a_1 - a_0)/a_1  <=  (prod_k a_k)/t^n - 1                              (*)

at the critical point `t` of `eq:ab-def`, where `a_0` is the smallest zero of the
pencil, `a_1` the smallest of the rest, and `Sigma(t) = 0`.  Normalizing by
`w_k = a_k/t` turns `Sigma(t) = 0` into `sum_k 1/(w_k - 1) = -r` and turns (*)
into `2 <= prod_k w_k + w_0/w_1`.

**The proof keeps three of the `n` zeros and throws the rest away.**  Every
discarded factor `w_k` exceeds `1`, so dropping it only weakens the product; what
survives is a bound in `w_0`, `w_1` and one further `w_j`, and the whole
inequality is then a polynomial fact in the two variables `p = w_1 - 1` and
`q = w_j - 1`.  That is why no Cauchy-Schwarz and no `1 + sum <= prod(1 + .)`
appears anywhere: the constraint is used through two of its terms and the product
through two of its factors.

The checks below are aimed at the PROOF rather than at (*), because (*) alone
cannot see which hypotheses are doing work:

  (C1) the polynomial identity the Lean proof rewrites through, exactly
  (C2) `E >= 0` needs `q >= p` -- with the witness where it fails without it
  (C3) the two-zero form of the bound, swept over pencils, is what holds
  (C4) `n = 2` REFUTES (*), so three distinct indices is a real boundary
  (C5) `1 <= r` is NOT sharp -- the proof consumes it, the bound does not need it
  (C6) the slack growing with `n` is exactly the discarded factors
  (C7) the positive-combination certificate behind the SHARP bound, exactly
  (C8) the sharp `(n-2)` bound itself, over the whole admissible parametrization
  (C9) `n-2` is the LARGEST constant -- two percent more is refuted at every `n`
 (C10) and the two-zero route provably cannot reach it, which is why both exist

Companion to `check_clearance_general_n.py`, which measures (*) itself.

Lean: `ForgacsTran.EndpointCollision.two_le_sum_mul_of_le`,
`two_le_prod_add_div_of_two_terms`, `clearance_ge_relative_gap_of_r_general`,
`sub_one_mul_relative_gap_le`, `clearance_ge_sub_two_mul_relative_gap`.
"""
from __future__ import annotations

import itertools
import os
import random
import re

import mpmath as mp
import sympy as sp

mp.mp.dps = 40


# ---------------------------------------------------------------------------
# (C1) the identity the Lean proof rewrites through
# ---------------------------------------------------------------------------
# `two_le_sum_mul_of_le` proves `2*D <= (p+q)*(1 + D + 1/(1+p))` with
# `D = p + q + p*q`, by rewriting the difference as `E/(1+p)`.  If that identity
# is wrong the Lean `field_simp; ring` would fail, so this is a guard on the
# shape rather than on the arithmetic -- but it is the shape a reader checks.
p, q = sp.symbols("p q", positive=True)
D = p + q + p * q
lhs = (p + q) * (1 + D + 1 / (1 + p)) - 2 * D
E = p**3 + p**2 * q + q * (q - p) + 2 * p * q**2 + p**3 * q + p**2 * q**2
assert sp.simplify(sp.together(lhs - E / (1 + p))) == 0, (
    "the difference is not E/(1+p); the Lean rewrite `key` would not close")
print("PASS  (C1) (p+q)(1+D+1/(1+p)) - 2D = E/(1+p) exactly, with "
      "E = p^3 + p^2 q + q(q-p) + 2pq^2 + p^3 q + p^2 q^2")

# Only one term of `E` can be negative, and only when `q < p`.
neg = [t for t in E.expand().as_ordered_terms() if t.could_extract_minus_sign()]
assert len(neg) == 1 and sp.simplify(neg[0] + p * q) == 0, (
    f"expected exactly one negative term -pq in E, got {neg}")
print("PASS  (C1) exactly one term of E carries a minus sign, and it is -pq, "
      "so `q >= p` is the whole of what the sign argument needs")


# ---------------------------------------------------------------------------
# (C2) the ordering hypothesis is load-bearing
# ---------------------------------------------------------------------------
def Ev(pv, qv):
    return pv**3 + pv**2 * qv + qv * (qv - pv) + 2 * pv * qv**2 + pv**3 * qv \
        + pv**2 * qv**2


grid = [mp.mpf(k) / 100 for k in range(1, 400, 3)]
worst_ok = min(Ev(a, b) for a in grid for b in grid if b >= a)
assert worst_ok >= 0, f"E went negative on q >= p, at min {worst_ok}"
print(f"PASS  (C2) E >= 0 everywhere on 0 < p <= q; min over the grid "
      f"{mp.nstr(worst_ok, 6)}")

bad = [(Ev(a, b), a, b) for a in grid for b in grid if b < a and Ev(a, b) < 0]
assert bad, ("E stayed nonnegative on q < p, so `q >= p` would be decoration "
             "rather than a hypothesis -- the Lean statement could be widened")
v, pv, qv = min(bad)
print(f"PASS  (C2) and E < 0 somewhere on q < p -- at p = {mp.nstr(pv, 4)}, "
      f"q = {mp.nstr(qv, 4)}, E = {mp.nstr(v, 4)}.  So `a_1` must be the "
      f"SMALLEST of the zeros other than `a_0`, not merely one of them")


# ---------------------------------------------------------------------------
# the pencil, and its critical point
# ---------------------------------------------------------------------------
def sigma(a, r, t):
    return sum(t / (ak - t) for ak in a) + r


def critical_point(a, r):
    """The root of `Sigma` in `(a_0, a_1)`, by bisection.

    `Sigma -> -inf` just above `a_0` and `-> +inf` just below `a_1`, so the
    bracket is guaranteed and no starting guess can be wrong.  A Newton solver
    is what fails here: on a near-uniform pencil the root sits within `1e-9` of
    the pole and the iteration walks straight through it.
    """
    lo, hi = a[0], a[1]
    width = hi - lo
    lo = lo + width * mp.mpf("1e-30")
    hi = hi - width * mp.mpf("1e-30")
    flo = sigma(a, r, lo)
    for _ in range(400):
        mid = (lo + hi) / 2
        if flo * sigma(a, r, mid) <= 0:
            hi = mid
        else:
            lo, flo = mid, sigma(a, r, mid)
    return (lo + hi) / 2


FAMILIES = [
    # near-uniform, which is where the bound is tightest
    lambda n: [mp.mpf(1) + mp.mpf(k) / 1000 for k in range(n)],
    lambda n: [mp.mpf(1) + mp.mpf(k) / 100000 for k in range(n)],
    # a wide first gap, and a narrow one under a wide tail
    lambda n: [mp.mpf(1)] + [mp.mpf(3 + k) for k in range(n - 1)],
    lambda n: [mp.mpf(1), mp.mpf(1) + mp.mpf(1) / 1000]
              + [mp.mpf(10 * (k + 1)) for k in range(n - 2)],
    # geometric, and one repeated tail
    lambda n: [mp.mpf(2) ** k for k in range(n)],
    lambda n: [mp.mpf(1), mp.mpf(2)] + [mp.mpf(2)] * (n - 2),
]


def sweep():
    for n in range(3, 9):
        for fam in FAMILIES:
            a = fam(n)
            if a[0] >= a[1]:
                continue
            for r in (1, 2, 3):
                yield n, r, a, critical_point(a, r)


# ---------------------------------------------------------------------------
# (C3) the two-zero form is what the proof establishes
# ---------------------------------------------------------------------------
margins, cases = [], 0
for n, r, a, t in sweep():
    w = [ak / t for ak in a]
    # the proof keeps w_0, w_1 and ONE further factor; the worst such j is the
    # one that makes the retained product smallest, so take the minimum over j
    two = min(w[0] * (w[1] * w[j]) + w[0] / w[1] for j in range(2, n))
    margins.append(two - 2)
    cases += 1
    assert two >= 2 - mp.mpf("1e-25"), (
        f"the two-zero bound failed at n={n}, r={r}, a={[float(x) for x in a]}: "
        f"{mp.nstr(two, 12)} < 2")
print(f"PASS  (C3) 2 <= w_0(w_1 w_j) + w_0/w_1 at all {cases} swept "
      f"configurations, for EVERY choice of the third index j; "
      f"min margin {mp.nstr(min(margins), 6)}")


# ---------------------------------------------------------------------------
# (C4) n = 2 refutes the bound
# ---------------------------------------------------------------------------
# Three distinct indices is not an artifact of the proof.  At `n = 2` there is
# no third zero to retain and the bound is FALSE -- at `r = 1` decisively so,
# where the critical point is exactly the geometric mean and the clearance is
# exactly `0` while the relative gap is whatever the pencil's is.
refuted = 0
for a in ([1, 2], [1, mp.mpf("1.01")], [1, mp.mpf("1.5")], [1, 4]):
    a = [mp.mpf(x) for x in a]
    t = critical_point(a, 1)
    gm = mp.sqrt(a[0] * a[1])
    assert abs(t - gm) < mp.mpf("1e-25"), (
        f"at n=2, r=1 the critical point should be the geometric mean: "
        f"{mp.nstr(t, 20)} vs {mp.nstr(gm, 20)}")
    clearance = a[0] * a[1] / t**2 - 1
    gap = (a[1] - a[0]) / a[1]
    assert abs(clearance) < mp.mpf("1e-25"), (
        f"clearance should vanish identically at n=2, r=1; got {clearance}")
    assert gap > clearance, "expected the bound to fail at n = 2"
    refuted += 1
print(f"PASS  (C4) at n = 2 and r = 1 the critical point is exactly "
      f"sqrt(a_0 a_1), the clearance is exactly 0, and the bound FAILS for "
      f"every one of the {refuted} pencils tried -- so `3 <= n` is a real "
      f"boundary and not a limitation of the route")


# ---------------------------------------------------------------------------
# (C5) `1 <= r` is consumed by the proof and not needed by the bound
# ---------------------------------------------------------------------------
# The proof uses `1 <= r` once, to replace `r + S - 1` by `S`.  The bound itself
# survives far below that, so the hypothesis is a convenience of the route.  It
# costs nothing in the pencil, where `r` is a positive natural, but it must not
# be reported as the edge of the phenomenon.
below = 0
for n, r_unused, a, _ in itertools.islice(sweep(), 0, None, 3):
    for rr in (mp.mpf("0.9"), mp.mpf("0.5"), mp.mpf("0.1")):
        t = critical_point(a, rr)
        prod = mp.mpf(1)
        for x in a:
            prod *= x
        assert prod / t**n - 1 >= (a[1] - a[0]) / a[1] - mp.mpf("1e-25"), (
            f"the bound failed at r = {rr}, which would make `1 <= r` sharp "
            f"after all: n={n}, a={[float(x) for x in a]}")
        below += 1
print(f"PASS  (C5) the bound also holds at r = 0.9, 0.5 and 0.1 over "
      f"{below} configurations, so `1 <= r` is what the PROOF consumes and "
      f"not where the bound stops")


# ---------------------------------------------------------------------------
# (C6) the growing slack is the discarded factors
# ---------------------------------------------------------------------------
# The lower endpoint wants a clearance, so a bound that decayed in `n` would
# decay the retained radius with it.  It does the opposite, and the reason is
# structural rather than numerical: the full product carries `n - 3` factors the
# proof throws away, each exceeding `1`.
by_n: dict[int, list] = {}
for n, r, a, t in sweep():
    w = [ak / t for ak in a]
    full = w[0] * mp.fprod(w[1:]) + w[0] / w[1]
    two = min(w[0] * (w[1] * w[j]) + w[0] / w[1] for j in range(2, n))
    assert full >= two - mp.mpf("1e-25"), (
        "the full product came out below the retained one, so a discarded "
        f"factor was not >= 1: n={n}, a={[float(x) for x in a]}")
    by_n.setdefault(n, []).append(full - two)
worst_by_n = {n: min(v) for n, v in by_n.items()}
assert all(v >= 0 for v in worst_by_n.values())
print("PASS  (C6) the full bound never falls below the retained one; the "
      "discarded factors contribute, by n: "
      + ", ".join(f"n={n}: >= {mp.nstr(v, 4)}" for n, v in
                  sorted(worst_by_n.items())))


# ---------------------------------------------------------------------------
# (C7) the certificate behind the sharp bound
# ---------------------------------------------------------------------------
# `sub_one_mul_relative_gap_le` clears `(1+v1)(1+S)` and closes on a positive
# combination.  That it is an IDENTITY rather than an estimate is what makes the
# bound sharp: all five terms vanish together in the collapsing direction, so
# nothing lossy sits between the hypotheses and the constant.
Tv, Sv, uv, v1v, Mv = sp.symbols("T S u v1 M")
Av = 1 - uv * (1 + Sv)
cleared = (Tv - uv * (1 + Tv)) * (1 + v1v) * (1 + Sv) - (Mv - 1) * (uv + v1v) * (1 + Sv)
combo = (Av * (1 + Tv) * (1 + v1v) + (Mv - 1) * Av + (Tv * Sv - Mv**2) * (1 + v1v)
         + (Mv - 1) * (Mv - v1v * Sv) + Mv * (Mv - 1) * v1v)
assert sp.simplify(sp.expand(cleared - combo)) == 0, (
    "the cleared difference is not the stated positive combination; the Lean "
    "`hcert` ring step would not close")
print("PASS  (C7) the cleared difference equals "
      "A(1+T)(1+v1) + (m-1)A + (TS-m^2)(1+v1) + (m-1)(m-v1 S) + m(m-1)v1 "
      "exactly, at A = 1 - u(1+S)")


# ---------------------------------------------------------------------------
# the free parametrization, and a check that it is the right one
# ---------------------------------------------------------------------------
# `v_1..v_m > 0` and `r >= 1` arbitrary is the WHOLE admissible set: put
# `u = 1/(r+S)`, `w_0 = 1-u`, `w_k = 1+v_k`, and `a_k = t w_k` for any `t > 0`
# realizes it as a pencil with `Sigma(t) = 0`.  Sampling `v` directly rather
# than sampling pencils and solving is what reaches the collapsing direction,
# which is where the constant lives and where a pencil sampler does not go
# unless it is built to.
def realize(v, r, t=mp.mpf(1)):
    """The pencil `(t*w_0, t*w_1, ...)` that the data `(v, r)` describes."""
    S = sum(1 / x for x in v)
    u = 1 / (r + S)
    return [t * (1 - u)] + [t * (1 + x) for x in v]


for v, r in (([mp.mpf("0.3"), mp.mpf("1.7")], mp.mpf(1)),
             ([mp.mpf("0.01")] * 4, mp.mpf(3)),
             ([mp.mpf(5), mp.mpf(9), mp.mpf("11.5")], mp.mpf(2))):
    a = realize(v, r)
    assert abs(sigma(a, r, mp.mpf(1))) < mp.mpf("1e-30"), (
        f"the parametrization does not satisfy Sigma(t) = 0: {sigma(a, r, mp.mpf(1))}")
print("PASS  (C8) the (v, r) parametrization reconstructs a pencil with "
      "Sigma(t) = 0 to 1e-30, so sampling it samples admissible configurations")


def sharp_margin(v, r, c):
    """`(1-u)P - 1 - c*(u+v1)/(1+v1)` -- the sharp claim at constant `c`."""
    S = sum(1 / x for x in v)
    u = 1 / (r + S)
    v1 = min(v)
    P = mp.mpf(1)
    for x in v:
        P *= 1 + x
    return (1 - u) * P - 1 - c * (u + v1) / (1 + v1)


rng = random.Random(20260826)
worst = None
trials = 0
for _ in range(120000):
    m = rng.choice([2, 3, 4, 5, 6, 7, 8])
    style = rng.choice(["unif", "collapse", "spread", "wide", "twoscale"])
    if style == "unif":
        b = mp.mpf(rng.uniform(1e-4, 4))
        v = [b] * m
    elif style == "collapse":
        b = mp.mpf(10) ** rng.uniform(-8, 0.5)
        v = [b * mp.mpf(rng.uniform(1, 1.001)) for _ in range(m)]
    elif style == "spread":
        v = [mp.mpf(rng.uniform(1e-3, 30)) for _ in range(m)]
    elif style == "wide":
        v = [mp.mpf(10) ** rng.uniform(-6, 3) for _ in range(m)]
    else:
        v = [mp.mpf(rng.uniform(1e-5, 1e-4))] + \
            [mp.mpf(rng.uniform(1, 80)) for _ in range(m - 1)]
    r = mp.mpf(rng.choice([1, 1, 1, 2, 3, 7]))
    # positivity of the smallest zero is DERIVED, not assumed: `u(1+S) <= 1`
    # with `S > 0` forces `0 < w_0 < 1`, and neither Lean statement takes it as
    # a hypothesis.  Checked here at every sample rather than reasoned about.
    S_ = sum(1 / x for x in v)
    w0 = 1 - 1 / (r + S_)
    assert 0 < w0 < 1, (
        f"w_0 left (0,1) at m={m}, r={r} -- positivity of the smallest zero "
        f"would then NOT be a consequence and both theorems would need it back")
    val = sharp_margin(v, r, mp.mpf(m - 1))
    trials += 1
    assert val >= -mp.mpf("1e-25"), (
        f"the sharp (n-2) bound FAILED at m={m}, r={r}, "
        f"v={[float(x) for x in v]}: margin {val}")
    if worst is None or val < worst:
        worst = val
print(f"PASS  (C8) the sharp bound holds at all {trials} sampled configurations "
      f"over m = 2..8 and r = 1..7; min margin {mp.nstr(worst, 6)}, and "
      f"0 < w_0 < 1 at every one of them, so positivity of the smallest zero "
      f"is a consequence of the constraint rather than a hypothesis")


# ---------------------------------------------------------------------------
# (C9) `n-2` is the largest constant
# ---------------------------------------------------------------------------
# Sharpness is a DIRECTION, not a point.  Along the collapsing family the margin
# runs to zero, so nothing above `n-2` survives; inflating it by two percent is
# refuted at every `n` tried, which is the check a bound only asymptotically
# sharp would fail to produce.
refuted_n = []
for m in range(2, 9):
    ok = min(sharp_margin([e] * m, mp.mpf(1), mp.mpf(m - 1))
             for e in (mp.mpf(10) ** -k for k in range(1, 9)))
    assert ok >= -mp.mpf("1e-25"), f"the constant n-2 itself failed at m={m}"
    bad = min(sharp_margin([e] * m, mp.mpf(1), mp.mpf(m - 1) * mp.mpf("1.02"))
              for e in (mp.mpf(10) ** -k for k in range(1, 9)))
    assert bad < 0, (
        f"1.02*(n-2) survived at m={m}, so n-2 would not be the largest "
        f"constant and the Lean statement could be strengthened")
    refuted_n.append(m + 1)
print(f"PASS  (C9) n-2 holds and 1.02*(n-2) is REFUTED at every n in "
      f"{refuted_n[0]}..{refuted_n[-1]}, so n-2 is the largest constant")


# ---------------------------------------------------------------------------
# (C10) the two-zero route cannot reach the sharp constant
# ---------------------------------------------------------------------------
# Both theorems are kept, and this is why.  The reduction discards exactly the
# factors the collapsing direction lives in, so the clearance it can certify
# saturates while `(n-2)g` grows linearly.  It is not a matter of proof effort.
# The table is in the module docstring, so it is GUARDED rather than typed:
# recompute it, then parse those same rows back out of the `.lean` and assert
# the two agree.  A number nothing checks is discovered stale by whoever is
# misled by it.
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(
    os.path.dirname(HERE), "lean", "ForgacsTran", "EndpointCollision.lean")

computed_gap, computed_ret = {}, {}
for n in range(3, 8):
    eps = mp.mpf("0.5")
    a = [mp.mpf(1)] + [1 + eps] * (n - 1)
    t = critical_point(a, 1)
    w = [x / t for x in a]
    gap = (a[1] - a[0]) / a[1]
    retained = min(w[0] * w[1] * w[j] for j in range(2, n)) - 1
    prod = mp.mpf(1)
    for x in a:
        prod *= x
    assert prod / t**n - 1 >= (n - 2) * gap - mp.mpf("1e-25"), (
        f"the sharp bound failed on the collapsing family at n={n}")
    computed_gap[n] = (n - 2) * gap
    computed_ret[n] = retained

# saturation: (n-2)g grows without bound, the retained clearance does not
assert all(computed_gap[n] < computed_gap[n + 1] for n in range(3, 7))
assert computed_ret[3] > computed_gap[3], (
    "the reduction should certify the sharp constant at n = 3, where n-2 = 1")
assert all(computed_ret[n] < computed_gap[n] for n in range(4, 8)), (
    "the reduction should fall short of the sharp constant from n = 4; if it "
    "does not, the two theorems may be one theorem twice after all")

lean_src = open(LEAN, encoding="utf-8").read()
rows = {}
for label, key in (("(n-2)g", "gap"), ("retained", "ret")):
    m = re.search(rf"^\s*{re.escape(label)}\s+((?:[0-9.]+\s*)+)$", lean_src, re.M)
    assert m, (
        f"the `{label}` row is missing from EndpointCollision.lean's docstring "
        f"-- the table this check guards is not where it says it is")
    rows[key] = [float(x) for x in m.group(1).split()]

for key, computed in (("gap", computed_gap), ("ret", computed_ret)):
    assert len(rows[key]) == 5, f"expected 5 columns in the `{key}` row"
    for n, printed in zip(range(3, 8), rows[key]):
        got = float(mp.nstr(computed[n], 6))
        assert abs(printed - got) < 5e-4, (
            f"the docstring's `{key}` entry at n={n} says {printed}, the "
            f"measurement says {got:.3f} -- the table has gone stale")

print("PASS  (C10) on the collapsing family (n-2)g grows while the retained "
      "clearance saturates; they cross between n = 3 and n = 4 and never come "
      "back, so the two theorems are not one theorem twice -- and the table in "
      "EndpointCollision.lean's docstring matches the measurement to 5e-4")

print("ALL PASS  check_clearance_two_index_reduction")
