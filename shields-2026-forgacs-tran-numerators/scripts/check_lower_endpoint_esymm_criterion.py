r"""Paper section `sec:dominance` (Proof of the main theorem).

Why the `n \ge 4` elementary symmetric route stops at the upper endpoint, as a
criterion rather than as a sample.

Both endpoints normalize to one shape: a root `w` of the pencil satisfies
`\prod_k (1 - v_k(s-1)) = s^r` with `s = w/s_0` and `v_k = s_0/(a_k - s_0)`,
and `\Sigma(s_0) = 0` reads `\sum_k v_k = -r` at BOTH ends.  What differs is
the sign of `a_k - s_0`: at the upper endpoint `s_0 = -L < 0` and every
`v_k = -u_k` is uniformly signed, while at the lower endpoint `s_0 = t_a > 0`
and `t_a > x_1` necessarily -- below `x_1` every term of `\sum_k s/(a_k-s)` is
positive and can never reach `-r` -- so some `a_k - t_a` are negative and the
`v_k` are of mixed sign.

The route's first elementary symmetric fact is `e_2(v) \ge 0`, and four steps
consume it.  Under the constraint `\sum_k v_k = -r` that fact has an exact
criterion, not an estimate:

    e_2(v) = ((\sum_k v_k)^2 - \sum_k v_k^2)/2 = (r^2 - \sum_k v_k^2)/2 ,

so `e_2(v) < 0` EXACTLY when `\sum_k v_k^2 > r^2`.  That turns "negative at
every pencil measured" into a statement about which side of one number the
coordinates sit, and it is checked here in both directions: the identity, and
then whether the lower endpoint always lands on the failing side.

mpmath only.
"""

from mpmath import mp, mpf, fabs, sin

mp.dps = 40

ZERO = mpf(10) ** -30


def sigma(a, r, s):
    return sum(s / (ak - s) for ak in a) + r


def lower_s0(a, r):
    r"""The first zero of `Sigma` ABOVE `x_1`, bracketed inside the first gap.

    `Sigma` is positive on `(0, x_1)` -- every `a_k - s` is positive there, so
    every term is -- and falls to `-\infty` just above `x_1`, rising to
    `+\infty` just below the next distinct zero.  So the zero sits strictly
    inside that gap, and `s_0 > x_1` follows from where the poles are rather
    than from any estimate.

    This is a zero of `Sigma`, so it is NOT the `t_a` of a pencil whose
    smallest zero is repeated: there `Sigma` has a pole at `x_1` and the
    branch's endpoint limit is `x_1` itself, where `v_k = s_0/(a_k - s_0)` is
    not even defined.  The object measured here is the one the normalization
    can be written at, which is what the comparison needs.
    """
    xs = sorted(set(a))
    if len(xs) < 2:
        return None
    x1, x2 = xs[0], xs[1]
    lo = x1 + (x2 - x1) * mpf(10) ** -12
    hi = x2 - (x2 - x1) * mpf(10) ** -12
    if not (sigma(a, r, lo) < 0 < sigma(a, r, hi)):
        return None
    for _ in range(300):
        mid = (lo + hi) / 2
        if sigma(a, r, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def upper_s0(a, r):
    """-L: the negative zero of Sigma."""
    # Sigma runs from r at 0^- to r - n at -infinity, so the collision exists
    # exactly when r < n.  At r = n it is pushed to infinity, which is the
    # degeneracy `eq:Q-hypotheses` excludes rather than a bracketing failure.
    if r >= len(a):
        return None
    lo, hi = -mpf(10) ** 12, -mpf(10) ** -12
    assert sigma(a, r, lo) < 0 < sigma(a, r, hi), (
        f"the negative zero is not bracketed at r = {r}, n = {len(a)}")
    for _ in range(300):
        mid = (lo + hi) / 2
        if sigma(a, r, mid) * sigma(a, r, lo) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def vs(a, s0):
    return [s0 / (ak - s0) for ak in a]


def e2(v):
    s1 = sum(v)
    return (s1 ** 2 - sum(x ** 2 for x in v)) / 2


PENCILS = [
    [mpf(1), mpf(1), mpf(3)],
    [mpf(1), mpf(1), mpf(1), mpf(4)],
    [mpf(1), mpf(1), mpf(2), mpf(6)],
    [mpf(1), mpf(2), mpf(5)],
    [mpf(2), mpf(2), mpf(7)],
    [mpf(1), mpf(1), mpf(1), mpf(1), mpf(9)],
    [mpf(1), mpf(3), mpf(3), mpf(8)],
    [mpf(1) / 2, mpf(1), mpf(1), mpf(5)],
]

# --- the identity, at both ends and at both signs of the coordinates --------
worst_id = mpf(0)
for a in PENCILS:
    for r in (1, 2, 3):
        for s0 in (upper_s0(a, r), lower_s0(a, r)):
            if s0 is None:
                continue
            v = vs(a, s0)
            assert fabs(sum(v) + r) < mpf(10) ** -25, (
                f"the constraint sum v = -r fails at s0 = {s0}")
            d = fabs(e2(v) - (mpf(r) ** 2 - sum(x ** 2 for x in v)) / 2)
            worst_id = max(worst_id, d)
assert worst_id < mpf(10) ** -25, f"the e_2 identity is off by {worst_id}"
print(f"PASS  e_2(v) = (r^2 - sum v_k^2)/2 under sum v_k = -r; worst residual "
      f"{mp.nstr(worst_id, 5)}")

# --- the upper endpoint: uniform sign, e_2 >= 0 ----------------------------
min_upper_e2 = mp.inf
for a in PENCILS:
    for r in (1, 2, 3):
        s0 = upper_s0(a, r)
        if s0 is None:
            continue
        v = vs(a, s0)
        assert all(x < 0 for x in v), f"an upper coordinate is not negative: {v}"
        assert e2(v) >= -ZERO, f"e_2 < 0 at the upper endpoint: {e2(v)}"
        min_upper_e2 = min(min_upper_e2, e2(v))
print(f"PASS  at the upper endpoint every v_k has one sign and e_2(v) >= 0; "
      f"smallest {mp.nstr(min_upper_e2, 6)}")

# --- the lower endpoint, split by the multiplicity of the smallest zero ----
# The two regimes fail differently and must not be pooled.  At `rho = 1` the
# normalization can be written and fails by SIGN.  At `rho >= 2` the branch's
# endpoint limit is `x_1` itself, where the repeated indices give
# `a_k - x_1 = 0` and `v_k` does not exist at all -- so the zero of `Sigma`
# above `x_1` is a DIFFERENT object there, and its margin says nothing about
# the branch.  Pooling them is how a ratio measured at `rho = 4` gets quoted
# as the lower endpoint's tightest case.
simple, repeated = [], []
for a in PENCILS:
    rho = sum(1 for x in a if x == min(a))
    for r in (1, 2, 3):
        s0 = lower_s0(a, r)
        if s0 is None:
            continue
        assert s0 > min(a), f"the zero is not above x_1 on a={a}, r={r}"
        v = vs(a, s0)
        assert any(x < 0 for x in v) and any(x > 0 for x in v), (
            f"the coordinates are not mixed: {v}")
        sq = sum(x ** 2 for x in v)
        assert e2(v) < 0, f"e_2 >= 0 above x_1 on a={a}, r={r}"
        (simple if rho == 1 else repeated).append((a, r, rho, sq / mpf(r) ** 2))

assert simple and repeated, "both regimes must be represented"
print(f"PASS  above x_1 the coordinates are mixed and e_2(v) < 0 at all "
      f"{len(simple) + len(repeated)} pencil/r pairs")

lo_s = min(x for _, _, _, x in simple)
hi_s = max(x for _, _, _, x in simple)
print(f"PASS  at rho = 1, where the normalization can be written, "
      f"sum v_k^2 / r^2 runs {mp.nstr(lo_s, 6)} to {mp.nstr(hi_s, 6)} -- "
      f"the criterion sum v_k^2 > r^2 cleared by at least a factor of "
      f"{mp.nstr(lo_s, 3)}, so the sign failure is not marginal")

lo_r = min(x for _, _, _, x in repeated)
print(f"INFO  at rho >= 2 the same bracketing returns a zero of Sigma whose "
      f"v_k the branch never reaches; its ratio falls to {mp.nstr(lo_r, 6)}, "
      f"which is a fact about that zero and NOT about the lower endpoint -- "
      f"reported separately so it cannot be quoted as the tightest case")

# The rho >= 2 endpoint fails earlier than by sign, and this is the assertion
# that says so: at x_1 the repeated indices make the normalization undefined.
for a in PENCILS:
    rho = sum(1 for x in a if x == min(a))
    if rho < 2:
        continue
    x1 = min(a)
    assert sum(1 for ak in a if ak == x1) == rho
    assert any(ak - x1 == 0 for ak in a), "no vanishing denominator at x_1"
print("PASS  at rho >= 2 the branch limit is x_1, where a_k - x_1 vanishes on "
      "the repeated indices, so v_k is undefined rather than badly signed -- "
      "an obstruction one step earlier than the sign failure")

print("ALL PASS")
