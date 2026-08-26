r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude).

Targets the identification of the witness pencil with the general branch of `thm:FT-geometry`:
the Lean tree defines `cubicTau` by the cubic relation `2 tau^3 cos theta - 3 tau^2 + 1 = 0`
and `ftTau a r l` by the angle-sum equation of `Forgacs2017RationalDenominator` Lemma 2, and
`cubicTau_eq_ftTau` says they agree at `a = [1,1,1]`, `r = 1`, `l = 2`.

Three things are checked, and the third is the one that corrected a wrong claim.

(1) THE ANGLE SUM.  With all three roots of `Q = (1-t)^3` at `1`, the sum is
    `3 arg(tau e^{i theta} - 1)`, and at `tau = cubicTau(theta)` it equals `theta + 2 pi`
    exactly.  Checked against the closed form `arccot(cos th/sin th - 1/(tau sin th))` rather
    than against a re-derivation of it, so the object tested is the one the Lean names.

(2) THE BRANCH ANGLE IS `(theta + 2 pi)/3`, which is `pi - (pi - theta)/3` -- the identity the
    Lean proof turns into `sin 2 psi = sin 2 psi` after the triple-angle formulas.

(3) `l = 2` IS THE LARGEST ADMISSIBLE INDEX, NOT THE ONLY ONE.  `ftBranchAt_of_arc` needs
    `l < n = 3`, so `l` is 0, 1 or 2.  A first version of the module docstring claimed `l = 2`
    was the only admissible index; it is not.  `l = 1` is admissible exactly for
    `theta < pi/2` -- the solvability range is `n theta < r theta + l pi`, i.e. `theta < pi/2`
    at `l = 1` -- and there it names a genuinely different branch, with `tau > 1` rather than
    `tau < 1`.  Since `ftAngleSum` is strictly DECREASING in `tau`, the largest index gives the
    smallest radius, which is why `l = 2` is the minimum-modulus branch `thm:FT-geometry` is
    about.  The `l = 1` solutions are exhibited here so the claim is a measurement.

`l = 0` is inadmissible at every angle, and for a reason worth recording: every branch angle
exceeds `theta` (`Forgacs2017RationalDenominator` Lemma 2(i), `lt_ftAngle` in the tree), so the
sum of three exceeds `3 theta`, which already exceeds `theta`.
"""

from mpmath import mp, mpf, fabs, pi, cos, sin, atan, findroot

mp.dps = 60

TOL = mpf(10) ** (-40)


def arccot(x):
    """`ftArccot`, the inverse cotangent onto (0, pi); Mathlib has no arccot."""
    return pi / 2 - atan(x)


def ftAngle(a, tau, th):
    return arccot(cos(th) / sin(th) - a / (tau * sin(th)))


def angle_sum(tau, th):
    """`ftAngleSum ![1,1,1] tau th` -- three equal roots, so three equal angles."""
    return 3 * ftAngle(1, tau, th)


def cubicTau(th):
    return 1 / (2 * cos((pi - th) / 3))


def cubic_relation(tau, th):
    return 2 * cos(th) * tau ** 3 - 3 * tau ** 2 + 1


# --------------------------------------------------------------------------
# (1) and (2): the branch equation holds at cubicTau, with l = 2.
# --------------------------------------------------------------------------

worst_rel, worst_sum, worst_angle = mpf(0), mpf(0), mpf(0)
for k in range(1, 600):
    th = pi * mpf(k) / mpf(600)
    t = cubicTau(th)
    assert 0 < t < 1, f"cubicTau left (0,1) at theta = {mp.nstr(th,6)}"
    worst_rel = max(worst_rel, fabs(cubic_relation(t, th)))
    worst_sum = max(worst_sum, fabs(angle_sum(t, th) - (th + 2 * pi)))
    worst_angle = max(worst_angle, fabs(ftAngle(1, t, th) - (th + 2 * pi) / 3))

print(f"PASS  the closed form satisfies the cubic branch relation to "
      f"{mp.nstr(worst_rel, 6)} on 599 interior angles")
assert worst_rel < TOL, "the closed form does not satisfy 2 tau^3 cos th - 3 tau^2 + 1 = 0"
print(f"PASS  ftAngleSum(cubicTau) = theta + 2 pi to {mp.nstr(worst_sum, 6)}, so "
      f"cubicTau = ftTau [1,1,1] 1 2")
assert worst_sum < TOL, "the angle-sum equation fails at l = 2"
print(f"PASS  the single branch angle is (theta + 2 pi)/3 to {mp.nstr(worst_angle, 6)}")
assert worst_angle < TOL, "the branch angle is not (theta + 2 pi)/3"


# --------------------------------------------------------------------------
# (3) l = 2 is the LARGEST admissible index, not the only one.
# --------------------------------------------------------------------------

print()
found_l1 = []
for k in range(1, 12):
    th = pi * mpf(k) / mpf(24)          # every one of these is below pi/2
    target = th + pi                     # l = 1
    assert 3 * th < target, "l = 1 should be admissible below pi/2"
    r = findroot(lambda x: angle_sum(x, th) - target, mpf('1.2'))
    assert fabs(angle_sum(r, th) - target) < TOL, "the l = 1 root does not solve its equation"
    assert r > 1, f"the l = 1 branch is not above 1 at theta = {mp.nstr(th,6)}"
    assert r > cubicTau(th), "the l = 1 radius is not larger than the l = 2 radius"
    found_l1.append((th, r))
print(f"      l = 1 is admissible and solvable at every one of {len(found_l1)} angles below "
      f"pi/2; e.g.")
for th, r in found_l1[:3]:
    print(f"        theta = {mp.nstr(th,6):>9s}   l=1 tau = {mp.nstr(r,10):>13s}   "
          f"l=2 tau = {mp.nstr(cubicTau(th),10)}")
print("PASS  l = 2 is the LARGEST admissible index, not the only one -- l = 1 names a real "
      "second branch below pi/2")

for k in range(13, 24):
    th = pi * mpf(k) / mpf(24)          # every one of these is above pi/2
    assert not (3 * th < th + pi), \
        f"l = 1 should be inadmissible above pi/2, but is not at {mp.nstr(th,6)}"
print("PASS  and it is inadmissible above pi/2, where l = 2 is the only one left")

for k in range(1, 24):
    th = pi * mpf(k) / mpf(24)
    assert not (3 * th < th + 0 * pi), "l = 0 should be inadmissible at every angle"
print("PASS  l = 0 is inadmissible at every angle, since every branch angle exceeds theta")

# and the ordering that makes the largest index the minimum-modulus branch
worst_mono = None
for k in range(1, 24):
    th = pi * mpf(k) / mpf(24)
    for j in range(1, 40):
        t1 = mpf(j) / mpf(20)
        t2 = t1 + mpf('0.05')
        if angle_sum(t2, th) >= angle_sum(t1, th):
            worst_mono = (th, t1, t2)
assert worst_mono is None, \
    f"ftAngleSum is not strictly decreasing in tau at {worst_mono}"
print("PASS  ftAngleSum is strictly decreasing in tau, so the largest index gives the "
      "smallest radius")

print("\nALL PASS  check_cubic_branch_bridge.py")
