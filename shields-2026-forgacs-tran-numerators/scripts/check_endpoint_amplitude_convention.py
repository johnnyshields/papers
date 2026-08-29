r"""Paper section `sec:dominance` (`eq:principal-decomposition`, the amplitude at the arc endpoints).

The amplitude is a quotient whose denominator is the pencil's `t`-derivative at
the principal root.  At BOTH arc endpoints the principal pair collides, so that
derivative vanishes -- and Lean's `x / 0 = 0` then makes the formalized
amplitude evaluate to `0` there, silently, with no elaborator complaint.  The
mathematical amplitude does the opposite: it BLOWS UP.

So a Lean hypothesis of the form `W 0 = 0` at an arc endpoint is satisfied by
the division convention rather than by the mathematics, and since every
admissible pencil collides at its endpoints, such a hypothesis constrains
nothing anywhere.  This is the structural form of the `x/0` trap: the value has
the right type and is a perfectly ordinary number, and it is the wrong object.

Checked at the tree's best-conditioned witness pencil, where everything is
closed form:

    Q(t) = 1 - 4t + t^2,   r = 1,   B(t) = t^2 + 1,   tau == 1,

so the branch is the unit semicircle `gamma(theta) = e^{i theta}`.

    z(theta)      = -Q(gamma)/gamma          = 4 - 2 cos(theta)      (real)
    d_t D(gamma)  = Q'(gamma) + z            = 2i sin(theta)
    amplitude     = -B(gamma)/d_t D(gamma)   = i e^{i theta} cot(theta)

so `|W(theta)| = |cot(theta)|`, which diverges at both endpoints and vanishes at
`theta = pi/2` -- the parameter at which `B` meets the arc, at `t = i`.

Every claim is an `assert`; mpmath only, no float in the loop.
"""

import mpmath as mp

mp.mp.dps = 40


def gamma(th):
    return mp.expj(th)


def zval(th):
    g = gamma(th)
    return -(1 - 4 * g + g ** 2) / g


def dtD(th):
    # d_t D = Q'(t) + z  at t = gamma
    return (-4 + 2 * gamma(th)) + zval(th)


def amp(th):
    g = gamma(th)
    return -(g ** 2 + 1) / dtD(th)


# ---------------------------------------------------------------- closed forms
for th in [mp.mpf(k) / 17 * mp.pi for k in range(1, 17)]:
    assert abs(mp.im(zval(th))) < mp.mpf(10) ** -30, ("z not real", th)
    assert abs(zval(th) - (4 - 2 * mp.cos(th))) < mp.mpf(10) ** -30, ("z form", th)
    assert abs(dtD(th) - 2j * mp.sin(th)) < mp.mpf(10) ** -30, ("dtD form", th)
    assert abs(abs(amp(th)) - abs(mp.cot(th))) < mp.mpf(10) ** -28, ("amp modulus", th)
print("PASS  (1) z = 4 - 2cos(theta) is real, d_tD = 2i sin(theta), |W| = |cot(theta)|")

# ------------------------------------------------ the collision at the endpoint
for th in [mp.mpf(10) ** -k for k in range(2, 9)]:
    assert abs(dtD(th)) < 3 * th, ("dtD should vanish linearly", th)
print("PASS  (2) d_tD -> 0 linearly at the endpoint: the principal pair collides")

# ------------------------------------------------- the amplitude DIVERGES there
prev = mp.mpf(0)
for k in range(2, 9):
    th = mp.mpf(10) ** -k
    m = abs(amp(th))
    assert m > prev, "modulus must increase as the endpoint is approached"
    prev = m
assert prev > mp.mpf(10) ** 7, prev
print("PASS  (3) |W| increases monotonically to %.3e as theta -> 0: it DIVERGES" % float(prev))

# ------------------------------- what Lean's x/0 convention reports at theta = 0
# d_tD(0) is exactly zero, so the formalized quotient is 0/0 -> 0 by convention.
assert abs(dtD(mp.mpf(0))) == 0, dtD(mp.mpf(0))
print("PASS  (4) d_tD(0) is EXACTLY zero, so the formalized amplitude is x/0 = 0")
print("          -- while the limit above is infinite.  A hypothesis `W 0 = 0`")
print("          is therefore discharged by the convention, not by mathematics,")
print("          and constrains nothing at any admissible pencil.")

# -------------------------------------- B meets the arc, so W has a zero on it
assert abs(amp(mp.pi / 2)) < mp.mpf(10) ** -30, amp(mp.pi / 2)
assert abs(gamma(mp.pi / 2) - 1j) < mp.mpf(10) ** -30
print("PASS  (5) B vanishes ON the arc at theta = pi/2, where gamma = i")

print()
print("ALL PASS  check_endpoint_amplitude_convention")
