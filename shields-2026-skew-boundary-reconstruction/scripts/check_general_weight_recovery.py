"""Paper section `sec:reconstruction`.  Target labels: `prop:stable-cofactor`, `eq:scalar-recovery`, `def:convex-weight`.

Does the scalar recovery really need the square weight?

The manuscript says, just before prop:stable-cofactor, that the square weight
"is what makes S_j a difference of squares and (eq:scalar-recovery) solvable;
for a general admissible weight the two scalars do not determine the pair."

The data are Delta = rho - z > 0 and S = omega(rho) - omega(z), with
rho = z + Delta.  So

    S(z) = omega(z + Delta) - omega(z) = sum_{k=z+1}^{z+Delta} dOmega(k),

a sum of Delta consecutive increments.  def:convex-weight requires dOmega to be
STRICTLY INCREASING, so S(z) is strictly increasing in z for every fixed
Delta >= 1.  Hence z, and with it rho, is uniquely recoverable from (Delta, S)
for EVERY admissible weight -- not only the square one.  What the square weight
uniquely supplies is the closed form (eq:scalar-recovery); a general weight
gives determination by strict monotonicity instead of by formula.

This script exhibits that, exhaustively, for four admissible weights, one of
which is not a polynomial.  It also confirms the negative control: a weight
with non-strict increments does collide, which is exactly the hypothesis
def:convex-weight rules out.
"""

from fractions import Fraction

ZMAX = 40
DMAX = 20


def increments_ok(omega, kmax):
    """def:convex-weight: omega(0)=0, increments strictly increasing and > 0."""
    if omega(0) != 0:
        return False
    inc = [omega(k) - omega(k - 1) for k in range(1, kmax + 1)]
    return all(i > 0 for i in inc) and all(b > a for a, b in zip(inc, inc[1:]))


WEIGHTS = {
    "square  omega(k)=k^2": lambda k: k * k,
    "cube    omega(k)=k^3": lambda k: k ** 3,
    "exp     omega(k)=2^k-1": lambda k: 2 ** k - 1,
    "ragged  omega(k)=k^2+k^3/7": lambda k: Fraction(7 * k * k + k ** 3, 7),
}

NEGATIVE_CONTROL = ("linear  omega(k)=k  (increments NOT strictly increasing)", lambda k: k)

print("Admissibility check against def:convex-weight (k <= %d):" % (ZMAX + DMAX))
for name, w in WEIGHTS.items():
    ok = increments_ok(w, ZMAX + DMAX)
    print("  %-26s admissible=%s" % (name, ok))
    assert ok, name
name, w = NEGATIVE_CONTROL
print("  %-26s admissible=%s  (control)" % (name, increments_ok(w, ZMAX + DMAX)))
assert not increments_ok(w, ZMAX + DMAX)

print()
print("Recovery of z from (Delta, S) by strict monotonicity:")
for name, w in WEIGHTS.items():
    collisions = 0
    checked = 0
    for Delta in range(1, DMAX + 1):
        seen = {}
        for z in range(0, ZMAX + 1):
            S = w(z + Delta) - w(z)
            checked += 1
            if S in seen:
                collisions += 1
            seen[S] = z
        # strict monotonicity of S in z, for this Delta
        vals = [w(z + Delta) - w(z) for z in range(0, ZMAX + 1)]
        assert all(b > a for a, b in zip(vals, vals[1:])), (name, Delta)
    print("  %-26s pairs=%d  collisions=%d  -> z is uniquely recoverable"
          % (name, checked, collisions))
    assert collisions == 0, name

print()
print("Negative control (a weight def:convex-weight excludes):")
name, w = NEGATIVE_CONTROL
seen = {}
collisions = 0
for z in range(0, ZMAX + 1):
    S = w(z + 3) - w(z)
    if S in seen:
        collisions += 1
    seen[S] = z
print("  %-26s Delta=3 collisions=%d  -> z NOT recoverable" % (name, collisions))
assert collisions > 0

print()
print("Cross-check: the square-weight closed form eq:scalar-recovery agrees")
sq = WEIGHTS["square  omega(k)=k^2"]
for Delta in range(1, DMAX + 1):
    for z in range(0, ZMAX + 1):
        rho = z + Delta
        S = sq(rho) - sq(z)
        assert Fraction(Delta * Delta + S, 2 * Delta) == rho, (Delta, z)
print("  rho = (Delta + S/Delta)/2 reproduces rho on all %d pairs"
      % (DMAX * (ZMAX + 1)))

print()
print("VERDICT: determination holds for every admissible weight;")
print("         the square weight supplies the CLOSED FORM, not the uniqueness.")
print("ALL PASS")
