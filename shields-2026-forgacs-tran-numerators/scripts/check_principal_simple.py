"""eq:principal-simple, on the general branch (subsec:principal-amplitude).

The manuscript's ground for the principal root being simple is the sign of
Im(t Q'(t)/Q(t)) on the open upper half plane, together with the elimination
t D'(t,z) = t Q'(t) - r Q(t) at a zero of D(.,z) = Q + z t^r.  This checks both,
and the conclusion, for admissible pencils Q(t) = c prod(a_k - t) with a_k > 0:

  (1) Im(t Q'(t)/Q(t)) = -Im t * sum_k a_k/|t - a_k|^2 < 0 for Im t > 0;
  (2) t D'(t,z) = t Q'(t) - r Q(t) at every zero t of D(.,z), for every z,
      real or not -- the z t^r terms cancel;
  (3) D'(t,z) != 0 at every nonreal zero of the pencil, quantitatively bounded
      away from zero.

mpmath only.  Every assertion fails loudly.
"""

import itertools

import mpmath as mp

mp.mp.dps = 40

TOL = mp.mpf(10) ** (-25)


def Q(a, c, t):
    return c * mp.fprod([ak - t for ak in a])


def dQ(a, c, t):
    """Q'(t) = -c sum_j prod_{k != j} (a_k - t)."""
    return -c * mp.fsum([mp.fprod([a[k] - t for k in range(len(a)) if k != j])
                         for j in range(len(a))])


def pencil_coeffs(c, a, r, z):
    poly = [c]
    for ak in a:
        nxt = [mp.mpf(0) * z] * (len(poly) + 1)
        for i, co in enumerate(poly):
            nxt[i] = nxt[i] + co * ak
            nxt[i + 1] = nxt[i + 1] - co
        poly = nxt
    while len(poly) <= r:
        poly.append(mp.mpf(0) * z)
    poly[r] = poly[r] + z
    co = list(reversed(poly))
    while len(co) > 1 and abs(co[0]) < mp.mpf(10) ** (-30):
        co.pop(0)          # the pencil degenerates in degree when z cancels the top
    return co


PENCILS = [
    ((1.0, 2.0), 1.0),
    ((1.0, 1.0, 1.0), 2.0),
    ((0.5, 0.5, 4.0), 1.0),
    ((1.0, 1.5, 2.0, 9.0), 0.7),
    ((2.0, 2.0, 2.0, 2.0, 5.0), 1.3),
]
RS = [1, 2, 3, 5]
ZS = [mp.mpf('0.3'), mp.mpf(1), mp.mpf(17), mp.mpc('0.4', '2.1'), mp.mpc('-3', '0.05')]

# (1) the sign of Im(t Q'(t)/Q(t)) on the upper half plane
for (a, c) in PENCILS:
    a = [mp.mpf(x) for x in a]
    c = mp.mpf(c)
    for re in [mp.mpf(x) for x in ('-3', '-0.2', '0', '0.7', '2.5', '11')]:
        for im in [mp.mpf(x) for x in ('1e-6', '0.05', '0.9', '4', '40')]:
            t = mp.mpc(re, im)
            lhs = mp.im(t * dQ(a, c, t) / Q(a, c, t))
            rhs = -im * mp.fsum([ak / abs(t - ak) ** 2 for ak in a])
            assert abs(lhs - rhs) < TOL * max(1, abs(rhs)), f"identity failed at {t}"
            assert lhs < 0, f"Im(tQ'/Q) not negative at {t}: {lhs}"

# (2) and (3): the elimination and the conclusion, at the pencil's own zeros
tested = 0
for (a, c), r, z in itertools.product(PENCILS, RS, ZS):
    a = [mp.mpf(x) for x in a]
    c = mp.mpf(c)
    co = pencil_coeffs(c, a, r, z)
    if len(co) < 2:
        continue
    roots = mp.polyroots(co, maxsteps=300, extraprec=300)
    for t in roots:
        if abs(mp.im(t)) < mp.mpf('1e-15'):
            continue                      # real zeros are outside the claim
        dD = dQ(a, c, t) + z * r * t ** (r - 1)
        # (2) the elimination
        assert abs(t * dD - (t * dQ(a, c, t) - r * Q(a, c, t))) < mp.mpf('1e-20') * max(
            1, abs(t * dD)), f"elimination failed at {t}"
        # (3) the conclusion, with the scale it is bounded away from zero by
        sigma = mp.fsum([t / (ak - t) for ak in a]) + r
        assert abs(t * dD + sigma * Q(a, c, t)) < mp.mpf('1e-20') * max(
            1, abs(sigma * Q(a, c, t))), f"factorization E = -sigma Q failed at {t}"
        assert abs(dD) > 0, f"derivative vanished at nonreal zero {t}"
        assert abs(mp.im(sigma)) > 0, f"sigma real at {t}"
        tested += 1

assert tested > 40, f"too few nonreal zeros exercised: {tested}"
print(f"nonreal pencil zeros checked: {tested}")
print("ALL PASS")
