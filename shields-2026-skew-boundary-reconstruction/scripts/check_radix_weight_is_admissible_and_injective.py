"""A radix weight is admissible in the paper's own sense and separates monomials outright.

WHY.  `def:convex-weight` admits any omega with omega(0)=0 and strictly increasing positive increments,
and the paper takes omega(k)=k^2 as "the principal example".  Two of the paper's recorded false
stronger statements are square-weight coincidences rather than facts about the method: the
coordinatewise collapse failure -h_3^2 + h_4h_1^2 (equal square weight 18 on two distinct monomials)
and the higher-stratum equal-weight collisions.  The radix weight

    omega_B(0) = 0,   omega_B(k) = B^k   (k >= 1),   B > max(n, 2)

is admissible, so every theorem of `sec:geometry` through `sec:conclusion` holds for it verbatim -- and because every
exponent of a monomial of an n x n Jacobi-Trudi determinant is at most n < B, the weight
nu_B(prod h_j^{e_j}) = sum_j e_j B^j is the base-B numeral with digits e_j and is therefore INJECTIVE
on those monomials.  So "same weight, different monomial" cannot occur for that choice.

WHAT IS CHECKED
  (1) omega_B is admissible per `def:convex-weight` for every B >= 3: omega(0)=0, increments strictly
      increasing, increments positive.  B = 2 FAILS (the first two increments tie), so the bound is
      load-bearing and not decoration.
  (2) nu_B is injective on every monomial with all exponents < B, and B = n collides -- both bounds
      tested to failure.
  (3) Over the monomials of an n x n Jacobi-Trudi determinant (exponent multisets of n parts drawn
      from 0..K), the square weight has many collisions and nu_B has none.
  (4) The paper's own `subsec:weight-scope` witness: h_3^2 and h_4h_1^2 share square weight 18 and are
      separated by nu_B.

WHAT IT DOES NOT BUY, and this travels with it: injectivity removes WEIGHT TIES, not EMPTY SUPPORTS.
A cofactor with no surviving matching stays zero under every weight, so no reweighting repairs a
statement whose failure is an absence rather than a coincidence.
"""
from itertools import combinations_with_replacement


def omega_sq(k):
    return k * k


def omega_radix(k, B):
    return 0 if k == 0 else B ** k


def admissible(om):
    """`def:convex-weight`: omega(0)=0, increments strictly increasing and positive."""
    if om(0) != 0:
        return False
    d = [om(k) - om(k - 1) for k in range(1, 12)]
    return all(x > 0 for x in d) and all(d[i] < d[i + 1] for i in range(len(d) - 1))


assert not admissible(lambda k: omega_radix(k, 2)), "B=2 must fail strict convexity"
for B in (3, 5, 7, 17):
    assert admissible(lambda k, B=B: omega_radix(k, B)), ("not admissible", B)
assert admissible(omega_sq)

# (2)+(3): monomials of an n x n JT determinant are multisets of n indices; exponents are at most n.
for n, K in ((3, 5), (4, 6), (5, 6)):
    B = max(n, 2) + 1
    mons = list(combinations_with_replacement(range(0, K + 1), n))
    sq, rx = {}, {}
    for m in mons:
        key = tuple(sorted((j for j in m if j > 0), reverse=True))     # h_0 = 1 drops out
        sq.setdefault(sum(omega_sq(j) for j in key), set()).add(key)
        rx.setdefault(sum(omega_radix(j, B) for j in key), set()).add(key)
    distinct = len({tuple(sorted((j for j in m if j > 0), reverse=True)) for m in mons})
    sq_coll = sum(len(v) - 1 for v in sq.values())
    rx_coll = sum(len(v) - 1 for v in rx.values())
    assert rx_coll == 0, (n, "radix collided", rx_coll)
    print("n=%d  distinct monomials %4d   square-weight collisions %3d   radix (B=%d) collisions %d"
          % (n, distinct, sq_coll, B, rx_coll))

# B = n collides: exponent n reaches the radix base and carries.
B = 4
assert sum(omega_radix(j, B) for j in (1,) * 4) == sum(omega_radix(j, B) for j in (2,)), \
    "the B=n carry should collide"

# (4) the paper's `subsec:weight-scope` witness.
a, b = (3, 3), (4, 1, 1)
assert sum(omega_sq(j) for j in a) == sum(omega_sq(j) for j in b) == 18
for B in (7, 17):
    wa = sum(omega_radix(j, B) for j in a)
    wb = sum(omega_radix(j, B) for j in b)
    assert wa != wb, (B, wa, wb)
    print("h_3^2 vs h_4h_1^2:  square 18 = 18   radix B=%-2d %d != %d" % (B, wa, wb))

print("PASS")
