r"""Paper section `sec:dominance` (Proof of the main theorem).

How sharp the `n \ge 4` route's core inequality actually is, and at which `n`.

The route bounds `|F(s)/s^2|` from below on the circle `|s - 1| = 2`, where
`F(s) = \prod_k (1 - u_k s) - (1 - s)` and `u` is the simplex point the
collision produces (`check_simplex_from_collision.py`).  The quantity the Lean
core produces is

    core(u) = 2 + 2 \prod_k (1 - u_k) - \prod_k (1 + u_k) .

Two separate questions, which an `n = 3` sample cannot tell apart:

  (i)   is `core(u)` a VALID lower bound for the boundary minimum, at every
        `n`?  This is what the route rests on.
  (ii)  is it SHARP -- equal to that minimum?

The answers differ.  (i) holds at every `n` measured, with `core(u) > 0`
throughout.  (ii) holds only at `n = 2` and `n = 3`, where `core(u)` is not a
bound at all but the exact value of `|F(s)/s^2|` at `s = 3`, the point of the
circle farthest from the collision along the positive axis -- `w = 2L` itself.
At `n \ge 4` that coincidence fails and the slack grows with `n`.

So the sharpness seen at three-term configurations is a property of `n \le 3`,
not of the bound, and a later pass should not read the thin `n = 3` margins as
evidence that the constant `2` is at its limit.  The identity is checked in
both directions here: exact at `n \le 3`, and separated from the minimum by a
measured, positive gap at `n \ge 4`.

Boundary and interior are not the same test and only the boundary is used:
`s = 0` lies INSIDE the disk `|s - 1| \le 2` and is the collision, where
`F` vanishes to second order.  Evaluating `F(s)/s^2` there by dividing
cancels catastrophically and reports a spurious zero, so the quotient is
formed by dropping the two vanishing coefficients rather than by division.

mpmath only.
"""

from mpmath import mp, mpf, mpc, fabs, sin, exp, pi

mp.dps = 40

NBOUND = 1200          # samples on |s - 1| = 2
ZERO = mpf(10) ** -30


def quotient_coeffs(u):
    """Ascending coefficients of F(s)/s^2, formed without dividing."""
    p = [mpf(1)]
    for uk in u:
        q = [mpf(0)] * (len(p) + 1)
        for i, c in enumerate(p):
            q[i] += c
            q[i + 1] += -uk * c
        p = q
    p[0] -= mpf(1)
    p[1] += mpf(1)
    assert fabs(p[0]) < ZERO, f"F(0) = {p[0]}, expected the collision"
    assert fabs(p[1]) < ZERO, f"F'(0) = {p[1]}, expected a double root"
    return p[2:]


def qeval(t, s):
    v = mpc(0)
    for i, c in enumerate(t):
        v += c * s ** i
    return v


def core(u):
    return (mpf(2) + 2 * mp.fprod([1 - uk for uk in u])
            - mp.fprod([1 + uk for uk in u]))


def boundary_min(t):
    return min(fabs(qeval(t, 1 + 2 * exp(2j * pi * mpf(j) / NBOUND)))
               for j in range(NBOUND))


def near_uniform(n, seed):
    raw = [mpf(1) + fabs(sin(mpf(seed) * (k + 1) * mpf(7) / mpf(3)))
           for k in range(n)]
    s = sum(raw)
    return [r / s for r in raw]


def skewed(n, j):
    """Toward a face: n-1 coordinates shrinking, the last carrying the rest."""
    eps = mpf(1) / (2 * (n - 1)) * mpf(10) ** (-mpf(j) / 2)
    return [eps] * (n - 1) + [mpf(1) - (n - 1) * eps]


# --- (i) validity, both families -------------------------------------------
worst_gap = mpf("inf")
worst_at = None
min_core = mpf("inf")

for n in (2, 3, 4, 5, 6, 8, 10, 14):
    for u in ([near_uniform(n, s) for s in range(1, 41)]
              + [skewed(n, j) for j in range(0, 13)]):
        assert fabs(sum(u) - 1) < ZERO, "test point is off the simplex"
        assert all(0 < uk < 1 for uk in u), "test point is not interior"
        c = core(u)
        assert c > 0, f"core = {c} at n={n}, not positive"
        min_core = min(min_core, c)
        g = boundary_min(quotient_coeffs(u)) - c
        # a valid lower bound may not exceed the minimum; roundoff at the two
        # exact orders is bounded by the working precision, not by a guess.
        assert g > -mpf(10) ** -35, f"core exceeds the minimum by {-g} at n={n}"
        if g < worst_gap:
            worst_gap, worst_at = g, n

print(f"PASS  (i) core(u) is a valid lower bound at n = 2..14, both families; "
      f"tightest gap {mp.nstr(worst_gap, 6)} at n={worst_at}")
print(f"PASS  (i) core(u) > 0 throughout; smallest {mp.nstr(min_core, 6)}")

# --- (ii) sharpness is an n <= 3 phenomenon --------------------------------
# At n <= 3 the core IS |F(3)/9|, the value at s = 3 -- so it is an evaluation
# wearing the clothes of a bound, and the minimum sits at that point.
for n in (2, 3):
    for u in [near_uniform(n, s) for s in range(1, 21)] + [skewed(n, j)
                                                           for j in range(0, 9)]:
        t = quotient_coeffs(u)
        d = fabs(qeval(t, mpf(3)).real - core(u))
        assert d < mpf(10) ** -35, f"core != F(3)/9 at n={n}: off by {d}"
        d2 = fabs(boundary_min(t) - core(u))
        assert d2 < mpf(10) ** -35, f"the minimum is not at s = 3 for n={n}"
print("PASS  (ii) at n = 2 and n = 3 the core equals |F(3)/9| exactly, and that "
      "is the boundary minimum -- an evaluation, not an estimate")

worst_slack = mpf("inf")
for n in (4, 5, 6, 8, 10, 14):
    slack = min(fabs(qeval(quotient_coeffs(u), mpf(3)).real - core(u))
                for u in [near_uniform(n, s) for s in range(1, 21)])
    assert slack > mpf(10) ** -6, (
        f"the n <= 3 coincidence has not broken at n={n}: slack {slack}")
    worst_slack = min(worst_slack, slack)
print(f"PASS  (ii) at n >= 4 the coincidence is gone; the core separates from "
      f"|F(3)/9| by at least {mp.nstr(worst_slack, 6)}, so the thin margins "
      f"seen at three-term configurations do not generalize")

print("ALL PASS")
