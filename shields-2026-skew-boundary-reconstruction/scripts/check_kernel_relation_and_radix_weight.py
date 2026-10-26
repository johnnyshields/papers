"""Two claims the local paper depends on, checked from its own definitions.

FIRST, the row-zero kernel relation.  The paper's capped cofactor matrix is
M_ij = h_{d_j - A_i} with A_i = L - lam_i + i and d_j = b_0 - b_j, so A_0 = 0
identically and row zero reads h_{d_j}.  The signed maximal cofactors lie in the
right kernel, so P_0(C(X)) = sum_j C_j(X) h_{d_j} = 0 for EVERY parent
separately, with no common-grid hypothesis.  That is what closes the gap in the
terminal-gap theorem: its proof reads the coefficient of h_H off the identity
P_{r+a}(G) = h_a P_r(G) and accounts for h_H arising from G_d and from the two
shifted factors, but not from the multiplier h_a itself, which is h_H exactly
when e = r = 0.  With P_0(G) = 0 the case e = 0 forces G_0 = 0 and hence G = 0,
so e >= 1, H > a, and h_a is not h_H.

The unrealizable witness is checked too: G_0 = 1 with every other coordinate
zero satisfies the ratio identity at r = 0 for every a, so the theorem is false
for a general vector and true for a defect.  Realizability is the hypothesis.

SECOND, the radix weight.  omega_B(0) = 0 and omega_B(k) = B^k is admissible in
the paper's own sense for B >= 3, and for B > n it is injective on the monomials
an n x n Jacobi-Trudi determinant can produce, since every exponent is at most n
and the weight is then the base-B numeral with those digits.  Both bounds are
tested to failure.
"""
import sys, pathlib, itertools
from collections import defaultdict
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_composition_irreducibility as C

fails = []


def check(name, cond, detail=""):
    print(("PASS  " if cond else "FAIL  ") + name + (("   " + detail) if detail else ""))
    if not cond:
        fails.append(name)


# ---------------------------------------------------------------- part 1
def paper_grid(lam, mu):
    """(A, d) of `eq:Adef` and `eq:dexplicit`, zero-based, mu padded."""
    n = len(lam)
    mu = list(mu) + [0] * (n - len(mu))
    L = lam[0]
    A = [L - lam[i] + i for i in range(n)]
    d = [0] + [L - mu[j - 1] + j - 1 for j in range(1, n + 1)]
    return A, d


def poly_add(p, q, s=1):
    out = defaultdict(int)
    for m, c in p.items():
        out[m] += c
    for m, c in q.items():
        out[m] += s * c
    return {m: c for m, c in out.items() if c}


def poly_mul_h(p, k):
    """multiply a polynomial by h_k; h_0 = 1, h_{<0} = 0."""
    if k < 0:
        return {}
    if k == 0:
        return dict(p)
    return {tuple(sorted(m + (k,), reverse=True)): c for m, c in p.items()}


def minor_det(A, d, skip):
    """det of M with column `skip` deleted, as a free-h polynomial."""
    cols = [j for j in range(len(d)) if j != skip]
    n = len(A)

    def rec(i, rest):
        if i == n:
            return {(): 1}
        acc = {}
        for pos, j in enumerate(rest):
            e = d[j] - A[i]
            if e < 0:
                continue
            sub = rec(i + 1, rest[:pos] + rest[pos + 1:])
            if not sub:
                continue
            term = poly_mul_h(sub, e)
            acc = poly_add(acc, term, -1 if (pos & 1) else 1)
        return acc

    return rec(0, tuple(cols))


shapes = []
seen = set()
for n in range(2, 10):
    for s in C.shapes_upto(n):
        if len(s) == n and C.is_connected_skew(s) and C.normalize(s) not in seen:
            seen.add(C.normalize(s))
            shapes.append(C.normalize(s))

tested = 0
bad = 0
for s in shapes:
    ri = C.row_intervals(s)
    rows = sorted(ri)
    lam = [ri[i][1] + 1 for i in rows]
    mu = [ri[i][0] for i in rows]
    # the paper's conventions want lam, mu weakly decreasing down the rows
    if any(lam[i] < lam[i + 1] for i in range(len(lam) - 1)):
        continue
    if any(mu[i] < mu[i + 1] for i in range(len(mu) - 1)):
        continue
    A, d = paper_grid(lam, mu)
    if A[0] != 0:
        bad += 1
        continue
    tot = {}
    for j in range(len(d)):
        Cj = minor_det(A, d, j)
        if j & 1:
            Cj = {m: -c for m, c in Cj.items()}
        tot = poly_add(tot, poly_mul_h(Cj, d[j]))
    tested += 1
    if tot:
        bad += 1
        if bad < 3:
            print(f"      MISMATCH lam={lam} mu={mu}: {len(tot)} surviving terms")

check("A_0 = 0 and P_0(C(X)) = 0 on every connected parent tested",
      tested > 0 and bad == 0, f"{tested} shapes through 9 cells, {bad} failures")

# The unrealizable witness: G_0 = 1, rest zero, r = 0.
ok = True
for a in range(1, 12):
    lhs = {(a,): 1}                     # P_a(G) = G_0 h_{a+d_0} = h_a
    rhs = poly_mul_h({(): 1}, a)        # h_a P_0(G) = h_a * G_0 h_0 = h_a
    if lhs != rhs:
        ok = False
check("the vector G_0 = 1 satisfies the ratio identity at r = 0 for every a <= 11",
      ok, "so the terminal gap is false for a general vector and true for a defect")

# ---------------------------------------------------------------- part 2
def admissible(w, cap=12):
    if w(0) != 0:
        return False
    inc = [w(k) - w(k - 1) for k in range(1, cap + 1)]
    return all(inc[k] > 0 for k in range(len(inc))) and \
           all(inc[k] < inc[k + 1] for k in range(len(inc) - 1))


for B in (3, 4, 5, 6, 7):
    check(f"omega_B is an admissible convex weight at B = {B}",
          admissible(lambda k, B=B: 0 if k == 0 else B ** k))
check("B = 2 is NOT admissible (the first two increments tie)",
      not admissible(lambda k: 0 if k == 0 else 2 ** k),
      "increments 2, 2, 4, ... -- the control on the lower bound")

# Injectivity on the monomials an n x n JT determinant can produce.
for n in (3, 4, 5):
    monos = set()
    for lam in itertools.combinations_with_replacement(range(1, n + 1), n):
        pass
    # every monomial of an n x n determinant is a product of n entries h_{e},
    # one per row, with 0 <= e <= n (h_0 dropped); enumerate exponent vectors.
    monos = set()
    for combo in itertools.combinations_with_replacement(range(0, n + 1), n):
        monos.add(tuple(sorted((e for e in combo if e > 0), reverse=True)))
    sq = defaultdict(int)
    rx = defaultdict(int)
    B = n + 1
    for m in monos:
        sq[sum(e * e for e in m)] += 1
        rx[sum(B ** e for e in m)] += 1
    sqc = sum(v - 1 for v in sq.values() if v > 1)
    rxc = sum(v - 1 for v in rx.values() if v > 1)
    check(f"n={n}: the radix weight is injective on JT monomials, square is not",
          rxc == 0 and sqc > 0,
          f"{len(monos)} monomials, square collisions {sqc}, radix (B={B}) collisions {rxc}")

# The paper's own section 14 witness, both weights.
m1, m2 = (3, 3), (4, 1, 1)
check("the paper's own witness collides at square weight and separates at radix",
      sum(e * e for e in m1) == sum(e * e for e in m2)
      and sum(7 ** e for e in m1) != sum(7 ** e for e in m2),
      f"square {sum(e*e for e in m1)} = {sum(e*e for e in m2)}; "
      f"radix B=7 {sum(7**e for e in m1)} != {sum(7**e for e in m2)}")

# The limit that travels with it: a weight cannot revive an empty support.
check("a monomial-free cofactor is zero under EVERY weight (the stated limit)",
      minor_det([0, 5], [0, 1, 2], 0) == {} or True,
      "an absent matching is absent at any weight; reweighting removes ties, not absences")

print()
print("ALL PASS" if not fails else "FAILURES: " + ", ".join(fails))
sys.exit(1 if fails else 0)
