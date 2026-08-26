"""Lower endpoint separation (thm:weighted-dominance, hypothesis `hsep`): the
quotient route to the interior count.

The normalized pencil is

    F_v(s) = prod_k (1 - s v_k) - (1 + s)^r,      sum_k v_k = -r,
             v_{i0} < -r,   v_k >= 0 for k /= i0.

`F_v` vanishes to order exactly two at s = 0 and, on the circle |1 + s| = 1, at
no other point.  So Q_v := F_v / s^2 is ZERO-FREE ON THAT CIRCLE, and the
ordinary circular argument principle applies to Q_v with no indentation.

This script checks the four facts the Lean proof rests on:

  (1)  Q_v is the polynomial with coeff i = F_v.coeff (i+2), and F_v = X^2 Q_v.
  (2)  the reference configuration v* = (-2r, r, 0, ..., 0) has
       Q_{v*}(s) = -( p(1+s) + 2 r^2 )  with  p(u) = sum_{i<=r-2} (r-1-i) u^i,
       and |p(u)| <= r(r-1)/2 < 2 r^2 on |u| <= 1, so Q_{v*} has NO root in the
       closed disc |1+s| <= 1.
  (3)  along the segment v(t) = (1-t) v + t v*, every Q_{v(t)} is zero-free on
       |1+s| = 1, so the root count in the open disc is constant in t.
  (4)  consequently Q_v has no root in |1+s| < 1, i.e. every root s /= 0 of F_v
       has |1+s| > 1.
"""

import itertools
import numpy as np

RNG = np.random.default_rng(20260826)


def F_coeffs(v, r):
    """Coefficients of F_v, ascending, as a numpy array."""
    prod = np.array([1.0])
    for vk in v:
        prod = np.convolve(prod, np.array([1.0, -vk]))
    powc = np.array([1.0])
    for _ in range(r):
        powc = np.convolve(powc, np.array([1.0, 1.0]))
    n = max(len(prod), len(powc))
    a = np.zeros(n)
    b = np.zeros(n)
    a[: len(prod)] = prod
    b[: len(powc)] = powc
    return a - b


def Q_coeffs(v, r):
    """F_v / s^2, ascending."""
    c = F_coeffs(v, r)
    assert abs(c[0]) < 1e-9, f"coeff_0 = {c[0]}"
    assert abs(c[1]) < 1e-9, f"coeff_1 = {c[1]}"
    return c[2:]


def polyval_asc(c, z):
    """Evaluate ascending-coefficient poly at z."""
    return np.polyval(c[::-1], z)


def roots_asc(c):
    trimmed = np.trim_zeros(c, "b")
    if len(trimmed) <= 1:
        return np.array([])
    return np.roots(trimmed[::-1])


def random_config(n, r, rng):
    """Admissible v: tail > 0, sum = -r, so v_{i0} < -r."""
    tail = rng.uniform(0.05, 3.0, size=n - 1)
    v = np.concatenate([[-r - tail.sum()], tail])
    assert abs(v.sum() + r) < 1e-12
    return v


def reference(n, r):
    v = np.zeros(n)
    v[0] = -2.0 * r
    v[1] = float(r)
    return v


# ---------------------------------------------------------------------------
print("(1) F_v = X^2 Q_v, and Q_v(0) = c_2 < 0")
worst_c2 = float("inf")
for n in range(2, 8):
    for r in range(1, 7):
        for _ in range(40):
            v = random_config(n, r, RNG)
            q = Q_coeffs(v, r)
            # rebuild F from Q
            f = np.concatenate([[0.0, 0.0], q])
            assert np.allclose(f, F_coeffs(v, r), atol=1e-9)
            c2 = q[0]
            assert c2 < 0, (n, r, v, c2)
            worst_c2 = min(worst_c2, -c2)
print(f"    ok; c_2 < 0 always, closest to zero: {worst_c2:.4g}")

# ---------------------------------------------------------------------------
print("(2) the reference v* = (-2r, r, 0, ..., 0)")


def p_coeffs(r):
    """p(u) = sum_{i=0}^{r-2} (r-1-i) u^i, ascending."""
    return np.array([float(r - 1 - i) for i in range(max(r - 1, 0))])


for n in range(2, 8):
    for r in range(1, 9):
        v = reference(n, r)
        q = Q_coeffs(v, r)
        # claimed closed form: Q(s) = -( p(1+s) + 2 r^2 )
        p = p_coeffs(r)
        zs = RNG.uniform(-3, 3, size=200) + 1j * RNG.uniform(-3, 3, size=200)
        claimed = -(polyval_asc(p, 1 + zs) + 2.0 * r * r)
        actual = polyval_asc(q, zs)
        assert np.allclose(claimed, actual, atol=1e-7), (n, r, np.abs(claimed - actual).max())
        # the bound: |p(u)| <= sum coeffs = r(r-1)/2  <  2 r^2  on |u| <= 1
        assert p.sum() == r * (r - 1) / 2
        assert r * (r - 1) / 2 < 2 * r * r
        # and hence no root in the CLOSED disc |1+s| <= 1
        rts = roots_asc(q)
        if len(rts):
            assert np.abs(1 + rts).min() > 1.0 + 1e-9, (n, r, rts)
print("    ok; closed form matches, sum|p| = r(r-1)/2 < 2r^2, no root in |1+s| <= 1")

# ---------------------------------------------------------------------------
print("(3) the segment keeps Q zero-free on |1+s| = 1")
theta = np.linspace(0, 2 * np.pi, 2001)
circle = -1 + np.exp(1j * theta)  # |1+s| = 1
worst = np.inf
for n in range(2, 8):
    for r in range(1, 7):
        for _ in range(15):
            v = random_config(n, r, RNG)
            vstar = reference(n, r)
            for t in np.linspace(0, 1, 21):
                vt = (1 - t) * v + t * vstar
                assert abs(vt.sum() + r) < 1e-11
                assert vt[0] < -r + 1e-12
                assert (vt[1:] >= -1e-15).all()
                q = Q_coeffs(vt, r)
                m = np.abs(polyval_asc(q, circle)).min()
                assert m > 1e-9, (n, r, t, m)
                worst = min(worst, m)
print(f"    ok; min |Q| on the circle over the whole sweep: {worst:.4g}")

# ---------------------------------------------------------------------------
print("(4) the conclusion: every root s /= 0 of F_v has |1+s| > 1")
worst_margin = np.inf
for n in range(2, 9):
    for r in range(1, 8):
        for _ in range(60):
            v = random_config(n, r, RNG)
            q = Q_coeffs(v, r)
            rts = roots_asc(q)
            if len(rts) == 0:
                continue
            m = np.abs(1 + rts).min()
            assert m > 1.0 + 1e-9, (n, r, v, rts[np.argmin(np.abs(1 + rts))])
            worst_margin = min(worst_margin, m)
# and the brief's own witness
v = np.array([-2.0, 0.5, 0.5])
q = Q_coeffs(v, 1)
assert np.allclose(q, [-1.75, 0.5], atol=1e-12), q
assert np.allclose(roots_asc(q), [3.5], atol=1e-9)
print(f"    ok; tightest |1+s| over all sampled roots: {worst_margin:.6f}")
print("    witness n=3, r=1, v=(-2,1/2,1/2): Q = s/2 - 7/4, root 3.5, |1+s| = 4.5")

# ---------------------------------------------------------------------------
print("(5) the reference the Lean proof actually uses, and its two bounds")

# ForgacsTran.ftRefTail: one more than what the higher coefficients reach at
# |sigma| <= 2.  Larger than the w = r of (2) -- Lean trades the sharp
# |p| <= r(r-1)/2 bound for a crude one it need not derive an identity for.


def ft_ref_tail(n, r):
    N = n + r + 1
    from math import comb
    return 1.0 + sum(comb(r, i + 3) * 2.0 ** (i + 1) for i in range(N))


def lean_reference(n, r):
    w = ft_ref_tail(n, r)
    v = np.zeros(n)
    v[0] = -(r + w)
    v[1] = w
    return v, w


for n in range(2, 8):
    for r in range(1, 8):
        v, w = lean_reference(n, r)
        assert abs(v.sum() + r) < 1e-6 * max(1.0, w), (n, r, v.sum())
        assert v[0] < -r and v[1] > 0 and (v[2:] >= 0).all()
        # every negative coordinate is < -1, the true normalized range
        assert v[0] < -1.0
        q = Q_coeffs(v, r)
        # the two bounds the Lean estimate runs on
        assert abs(q[0]) >= w * w - 1e-6 * w * w, (n, r, abs(q[0]), w * w)
        tail = sum(abs(q[i]) * 2.0 ** i for i in range(1, len(q)))
        assert tail <= w - 1 + 1e-9, (n, r, tail, w - 1)
        # hence no root in the closed disc |1+s| <= 1
        rts = roots_asc(q)
        if len(rts):
            assert np.abs(1 + rts).min() > 1.0 + 1e-9, (n, r, rts)
print("    ok; |Q_0| >= w^2 and the higher terms sum to at most w - 1 at |s| <= 2")

# ---------------------------------------------------------------------------
print("(6) the sweep never leaves the ONE-NEGATIVE regime")
# The consumer's separation is FALSE with two or more negative coordinates, so
# the deformation must keep exactly one.  It does, by construction: the tail is
# a convex combination of two nonnegative tails, and v_{i0} < -r is derived from
# a positive tail sum rather than assumed.
for n in range(2, 8):
    for r in range(1, 7):
        for _ in range(15):
            v = random_config(n, r, RNG)
            vstar, w = lean_reference(n, r)
            for t in np.linspace(0, 1, 21):
                vt = (1 - t) * v + t * vstar
                assert (vt < 0).sum() == 1, (n, r, t, vt)
                assert vt[0] < -r + 1e-9 and vt[0] < -1.0
                q = Q_coeffs(vt, r)
                m = np.abs(polyval_asc(q, circle)).min()
                assert m > 1e-9, (n, r, t, m)
print("    ok; exactly one negative coordinate at every point of every segment")

print()
print("ALL PASS")
