"""thm:FT-geometry, the argument cone at r >= 2 (sec:geometry, subsec:FT-geometry).

Checks the dichotomy the Lean module `ForgacsTran/FTGeometryCone.lean` runs on,
against the branch computed directly from the angle-sum equation:

  (1) the chord identities  R cos(t1 - th) = tau - x1 cos th,
                            R sin(t1 - th) = x1 sin th,
      with R = |tau e^{i th} - x1| and t1 = arg(tau e^{i th} - x1);
  (2) the angle bound  t1 > r th;
  (3) the far case  tau <= x1 cos th  =>  every w with |w| <= tau and
      |w - x1| <= R has |arg w| <= th;
  (4) the near case  x1 cos th < tau  =>  R < x1 sin(pi/r);
  (5) the conclusion: every zero of Q + z(th) t^r in the closed disk
      |t| <= tau(th) has |arg| strictly inside (0, pi/r);
  (6) the monotonicity  sin th / sin((r-1) th) <= sin(pi/(2(r-1))) <= sin(pi/r)
      on (0, pi/(2(r-1))].

mpmath only.  Every assertion fails loudly.
"""

import itertools

import mpmath as mp

mp.mp.dps = 40

TOL = mp.mpf(10) ** (-25)


def ft_angle(a, tau, th):
    """arg(tau e^{i th} - a), in (0, pi)."""
    return mp.arg(tau * mp.exp(1j * th) - a)


def angle_sum(a, tau, th):
    return mp.fsum([ft_angle(ak, tau, th) for ak in a])


def branch_tau(a, r, th):
    """Solve sum_k theta_k(tau) = r th + (n-1) pi for tau > 0, by bisection.

    The sum is strictly decreasing in tau, so the root is unique.
    """
    n = len(a)
    target = r * th + (n - 1) * mp.pi
    lo, hi = mp.mpf('1e-20'), mp.mpf(1)
    while angle_sum(a, hi, th) > target:
        hi *= 2
        assert hi < mp.mpf(10) ** 12, "branch radius did not bracket"
    while angle_sum(a, lo, th) < target:
        lo /= 2
        assert lo > mp.mpf(10) ** (-30), "branch radius did not bracket"
    for _ in range(400):
        mid = (lo + hi) / 2
        if angle_sum(a, mid, th) > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def pencil_coeffs(c, a, r, z):
    """Coefficients of Q(t) + z t^r, highest degree first; Q(t) = c prod(a_k - t)."""
    poly = [mp.mpf(c)]                      # ascending powers
    for ak in a:
        nxt = [mp.mpf(0)] * (len(poly) + 1)
        for i, co in enumerate(poly):
            nxt[i] += co * ak
            nxt[i + 1] -= co
        poly = nxt
    while len(poly) <= r:
        poly.append(mp.mpf(0))
    poly[r] += z
    return list(reversed(poly))


PENCILS = [
    ((1.0, 2.0), 1.0),
    ((1.0, 1.0), 1.0),
    ((1.0, 2.0, 3.0), 1.0),
    ((1.0, 1.0, 1.0), 2.0),
    ((0.5, 0.5, 4.0), 1.0),
    ((1.0, 1.5, 2.0, 9.0), 0.7),
    ((2.0, 2.0, 2.0, 2.0, 5.0), 1.3),
    ((0.25, 3.0, 3.0, 8.0), 2.0),
]
RS = [2, 3, 4, 5]
FRACS = [mp.mpf(f) for f in ('0.02', '0.1', '0.25', '0.4', '0.5', '0.65', '0.8', '0.93', '0.99')]

far_seen = 0
near_seen = 0
checked = 0

for (a, c), r in itertools.product(PENCILS, RS):
    a = [mp.mpf(x) for x in a]
    c = mp.mpf(c)
    n = len(a)
    x1 = min(a)
    for frac in FRACS:
        th = frac * mp.pi / r
        tau = branch_tau(a, r, th)
        z = -(c * mp.fprod([ak - tau * mp.exp(1j * th) for ak in a])) / (tau * mp.exp(1j * th)) ** r
        assert abs(mp.im(z)) < TOL * max(1, abs(z)), f"z not real: {z}"
        z = mp.re(z)
        assert z > 0, f"branch value not positive: {z}"

        # (1) the chord identities
        P = tau * mp.exp(1j * th)
        R = abs(P - x1)
        t1 = mp.arg(P - x1)
        assert abs(R * mp.cos(t1 - th) - (tau - x1 * mp.cos(th))) < TOL * max(1, tau)
        assert abs(R * mp.sin(t1 - th) - x1 * mp.sin(th)) < TOL * max(1, tau)

        # (2) the angle bound
        assert t1 > r * th, f"theta_1 = {t1} not above r*theta = {r * th}"

        # the dichotomy
        if tau <= x1 * mp.cos(th):
            far_seen += 1
            # (3) sample the lens and check every point has |arg| <= th
            for u in [mp.mpf(k) / 12 for k in range(1, 13)]:
                for v in [mp.mpf(k) * mp.pi / 8 for k in range(-8, 9)]:
                    w = u * tau * mp.exp(1j * v)
                    if abs(w - x1) <= R:
                        assert abs(mp.arg(w)) <= th + TOL, (
                            f"far case violated: arg={mp.arg(w)} th={th}")
        else:
            near_seen += 1
            # (4) the chord bound
            assert R < x1 * mp.sin(mp.pi / r), (
                f"near case violated: R={R} bound={x1 * mp.sin(mp.pi / r)}")

        # (5) the conclusion, on the actual zeros of the pencil
        roots = mp.polyroots(pencil_coeffs(c, a, r, z), maxsteps=200, extraprec=200)
        inner = [w for w in roots if abs(w) <= tau * (1 + mp.mpf('1e-18'))]
        assert len(inner) == 2, f"expected the principal pair, got {len(inner)}"
        for w in inner:
            g = abs(mp.arg(w))
            assert 0 < g < mp.pi / r, f"cone violated: |arg| = {g}, pi/r = {mp.pi / r}"
            assert abs(abs(w) - tau) < mp.mpf('1e-20') * tau
        checked += 1

assert far_seen > 0, "the far case was never exercised"
assert near_seen > 0, "the near case was never exercised"

# (6) the trigonometric monotonicity the near case runs on
for r in range(2, 13):
    m = mp.mpf(r) - 1
    cap = mp.pi / (2 * m)
    prev = None
    for k in range(1, 400):
        th = cap * mp.mpf(k) / 400
        val = mp.sin(th) / mp.sin(m * th)
        if prev is not None:
            assert val >= prev - TOL, f"ratio not monotone at r={r}, th={th}"
        prev = val
        assert val <= mp.sin(cap) + TOL, f"ratio above sin(pi/(2(r-1))) at r={r}"
    assert mp.sin(cap) <= mp.sin(mp.pi / r) + TOL, f"sin(pi/(2(r-1))) > sin(pi/r) at r={r}"

print(f"branch angles checked: {checked}  (far cases {far_seen}, near cases {near_seen})")
print("ALL PASS")
