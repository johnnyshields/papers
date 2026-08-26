"""thm:FT-geometry at the boundary values of n (sec:geometry, subsec:FT-geometry).

eq:Q-hypotheses asks only that Q be nonconstant, so n = 1 and n = 2 are in scope.
This checks the two cases the general arguments do not reach, and the one that is
out of scope, against the facts `ForgacsTran/FTGeometryBoundary.lean` runs on:

  (A) (n, r) = (1, 1) is degenerate.  g(t) = -Q(t)/t has g'(t) = Q(0)/t^2 > 0, so
      there is no positive critical point, the t_a of eq:ab-def does not exist,
      and the pencil Q + zt has degree at most one -- no conjugate pair.
  (B) (n, r) = (2, 1) and (1, 2): the pencil has degree two, so the principal pair
      IS the whole denominator and the minimum-modulus clause is vacuous.
  (C) n = 1, r >= 2: the angle sum is one angle, so theta_1 = r*theta EXACTLY --
      the strict bound theta_1 > r*theta the general argument uses is false here.
      The closed form tau(theta) = a sin(r th)/sin((r-1) th) follows, with
      tau -> r a/(r-1) at th -> 0+ (the first critical point) and tau -> 0 at
      th -> pi/r.  hcone and hmin hold at every sample.
  (D) the elementary inequality m sin(k th) <= k sin(m th) for 0 <= m <= k,
      k th <= pi, which is what bounds tau by t_a in (C).

mpmath only.  Every assertion fails loudly.
"""

import mpmath as mp

mp.mp.dps = 40

TOL = mp.mpf(10) ** (-25)


def ft_angle(a, tau, th):
    return mp.arg(tau * mp.exp(1j * th) - a)


def angle_sum(a, tau, th):
    return mp.fsum([ft_angle(ak, tau, th) for ak in a])


def branch_tau(a, r, th):
    n = len(a)
    target = r * th + (n - 1) * mp.pi
    lo, hi = mp.mpf('1e-25'), mp.mpf(1)
    while angle_sum(a, hi, th) > target:
        hi *= 2
        assert hi < mp.mpf(10) ** 12
    while angle_sum(a, lo, th) < target:
        lo /= 2
        assert lo > mp.mpf(10) ** (-35)
    for _ in range(400):
        mid = (lo + hi) / 2
        if angle_sum(a, mid, th) > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def pencil_coeffs(c, a, r, z):
    poly = [mp.mpf(c)]
    for ak in a:
        nxt = [mp.mpf(0)] * (len(poly) + 1)
        for i, co in enumerate(poly):
            nxt[i] += co * ak
            nxt[i + 1] -= co
        poly = nxt
    while len(poly) <= r:
        poly.append(mp.mpf(0))
    poly[r] += z
    co = list(reversed(poly))
    while len(co) > 1 and abs(co[0]) < mp.mpf(10) ** (-30):
        co.pop(0)
    return co


FRACS = [mp.mpf(f) for f in ('0.02', '0.15', '0.35', '0.5', '0.7', '0.9', '0.99')]

# (A) the degenerate corner
for a0 in [mp.mpf('0.5'), mp.mpf(1), mp.mpf(7)]:
    for c in [mp.mpf(1), mp.mpf(3)]:
        # g'(t) = c*a0/t^2 > 0 on (0, inf): no positive critical point
        for t in [mp.mpf(x) for x in ('0.01', '0.3', '1', '5', '90')]:
            g = lambda s: -(c * (a0 - s)) / s
            assert mp.diff(g, t) > 0, f"g' vanished at {t}"
        # and the pencil is linear, so it cannot carry a conjugate pair
        assert len(pencil_coeffs(c, [a0], 1, mp.mpf(2))) <= 2

# (B) the degree count, in both regimes
for a, r, c in [([mp.mpf(1), mp.mpf(3)], 1, mp.mpf(1)),
                ([mp.mpf(2), mp.mpf(2)], 1, mp.mpf('0.7')),
                ([mp.mpf(1)], 2, mp.mpf(1)),
                ([mp.mpf(5)], 2, mp.mpf(2))]:
    n = len(a)
    for frac in FRACS:
        th = frac * mp.pi / r
        tau = branch_tau(a, r, th)
        z = -(c * mp.fprod([ak - tau * mp.exp(1j * th) for ak in a])) / (tau * mp.exp(1j * th)) ** r
        assert abs(mp.im(z)) < TOL * max(1, abs(z))
        z = mp.re(z)
        roots = mp.polyroots(pencil_coeffs(c, a, r, z), maxsteps=200, extraprec=200)
        assert len(roots) == 2, f"expected a quadratic pencil, got degree {len(roots)}"
        for w in roots:
            assert abs(abs(w) - tau) < mp.mpf('1e-20') * tau, "a root off the branch circle"
            assert 0 < abs(mp.arg(w)) < mp.pi / r + TOL

# (C) the linear pencil at r >= 2
lin_checked = 0
for a0 in [mp.mpf(1), mp.mpf('0.25'), mp.mpf(9)]:
    for c in [mp.mpf(1), mp.mpf('1.7')]:
        for r in [2, 3, 4, 6]:
            a = [a0]
            ta = r * a0 / (mp.mpf(r) - 1)          # the only zero of E(s) = c((r-1)s - r a)
            for frac in FRACS:
                th = frac * mp.pi / r
                tau = branch_tau(a, r, th)
                # theta_1 = r*theta exactly, not merely above it
                assert abs(ft_angle(a0, tau, th) - r * th) < TOL, "theta_1 != r*theta"
                # the closed form
                closed = a0 * mp.sin(r * th) / mp.sin((r - 1) * th)
                assert abs(tau - closed) < mp.mpf('1e-20') * tau, "closed form wrong"
                # and it stays below the critical point
                assert tau <= ta + TOL, f"tau = {tau} above t_a = {ta}"
                assert (c * ((r - 1) * tau - r * a0)) <= TOL, "E(tau) positive"
                # hcone and hmin
                z = mp.re(-(c * (a0 - tau * mp.exp(1j * th))) / (tau * mp.exp(1j * th)) ** r)
                roots = mp.polyroots(pencil_coeffs(c, a, r, z), maxsteps=200, extraprec=200)
                inner = [w for w in roots if abs(w) <= tau * (1 + mp.mpf('1e-18'))]
                assert len(inner) == 2, f"minimum modulus failed: {len(inner)} inner roots"
                for w in inner:
                    assert 0 < abs(mp.arg(w)) < mp.pi / r, "cone violated"
                lin_checked += 1
            # the two endpoint limits the assembly consumes
            near = branch_tau(a, r, mp.mpf('1e-9') * mp.pi / r)
            assert abs(near - ta) < mp.mpf('1e-12') * ta, f"tau did not tend to t_a: {near} vs {ta}"
            far = branch_tau(a, r, (1 - mp.mpf('1e-9')) * mp.pi / r)
            assert far < mp.mpf('1e-7') * a0, f"tau did not collapse at the upper end: {far}"

assert lin_checked >= 100, f"too few linear-pencil samples: {lin_checked}"

# (D) the inequality that bounds tau by t_a
for m, k in [(0, 1), (1, 1), (1, 2), (2, 3), (1, 5), (3, 4), (mp.mpf('0.5'), mp.mpf('2.5'))]:
    m, k = mp.mpf(m), mp.mpf(k)
    for j in range(1, 200):
        th = mp.pi / k * mp.mpf(j) / 200 if k > 0 else mp.mpf(0)
        assert m * mp.sin(k * th) <= k * mp.sin(m * th) + TOL, (
            f"sin_scaled_le failed at m={m}, k={k}, th={th}")

print(f"linear-pencil samples: {lin_checked}")
print("ALL PASS")
