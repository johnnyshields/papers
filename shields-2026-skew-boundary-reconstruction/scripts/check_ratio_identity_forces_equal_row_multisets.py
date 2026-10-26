#!/usr/bin/env python3
"""Does a ratio identity DETERMINE the row-length multiset, or is it needed as a
hypothesis?

`lem:ratio-row-lengths` states that a ratio identity forces equal row-length multisets, so the
ratio branch (`thm:ratio-rigidity`, `cor:floor-supplies`, `cor:double-cap-kills`,
`cor:unique-ratio`) carries no separate multiset hypothesis.  This is the direct test of that
lemma on a population that does not presuppose it.

THE ARGUMENT OF THE LEMMA.  For connected X, thm:monge-minor applied to the northeast
extension gives in s_{X.(k)} = h_k * prod_i h_{rho_i}; for r > 0 strict superadditivity
gives in(h_a s_{X.(r)} - s_{X.(r+a)}) = h_a h_r prod_i h_{rho_i}.  Equating the two
signed Pieri remainders and cancelling h_a h_r equates the parent row-length products.

WHY THE POPULATION MATTERS.  The cancellation runs through
eq:Pk-is-capped's signed-Pieri reading, which the paper explicitly warns is NOT an
identity of multisets of shapes.  That warning is exactly where the argument could
fail, so the claim is tested directly instead: enumerate pairs that satisfy a ratio
identity WITHOUT assuming equal row-length multisets, and look for one where the
multisets differ.  A single such pair refutes the reduction; none over a real
population supports it.

  A |-> C(A) is the shift-indexed cofactor vector, so G = C(A) - C(B) is formed on the
  union of the two cap grids and no common-grid assumption is smuggled in.

Exact integer arithmetic throughout.  A ratio identity here is a polynomial identity
between h-monomial multisets, not a numerical coincidence.
"""

import os
import sys
from collections import defaultdict
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from skew_core import cofactors, padd, pmul, h, Pk          # noqa: E402
from skew_harness import connected, size                    # noqa: E402

SIZE_CAP = 11
ROW_CAP = 4
R_MAX = 4            # ratio identities tested at 0 <= r <= R_MAX
A_MAX = 4            # and 1 <= a <= A_MAX
FAILURES = []


def check(label, cond, detail=""):
    print("   %-68s %s%s" % (label, "ok" if cond else "*** FAIL ***",
                             ("   " + detail) if detail else ""))
    if not cond:
        FAILURES.append(label)


def partitions(maxpart, length):
    if length == 0:
        yield ()
        return
    for first in range(maxpart, -1, -1):
        for rest in partitions(first, length - 1):
            yield (first,) + rest


def rho(sh):
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return tuple(sorted(lam[i] - mu[i] for i in range(len(lam)) if lam[i] > mu[i]))


def shapes_by_mu():
    """Connected diagrams grouped by inner boundary, WITHOUT any row-multiset filter."""
    by = defaultdict(list)
    for rows in range(2, ROW_CAP + 1):
        for mu in partitions(SIZE_CAP, rows):
            if mu and mu[-1] != 0:
                continue                      # normalized: lowest inner part 0
            for lam in partitions(SIZE_CAP, rows):
                if any(lam[i] <= mu[i] for i in range(rows)):
                    continue                  # every row nonempty
                sh = (lam, mu)
                if 0 < size(sh) <= SIZE_CAP and connected(sh):
                    by[mu].append(sh)
    return by


def defect(A, B):
    """G on the UNION of the two shift grids -- extension by zero off each grid."""
    ca, cb = cofactors(A), cofactors(B)
    G = {}
    for d in set(ca) | set(cb):
        v = padd(ca.get(d, {}), cb.get(d, {}), sign=-1)
        if v:
            G[d] = v
    return G


def nonzero(G):
    return any(v for v in G.values())


def ratio_pairs(G):
    """Every (r, a) at which P_{r+a}(G) = h_a P_r(G) holds exactly."""
    out = []
    for r in range(0, R_MAX + 1):
        pr = Pk(G, r)
        for a in range(1, A_MAX + 1):
            if Pk(G, r + a) == pmul(h(a), pr):
                out.append((r, a))
    return out


def main():
    print(__doc__.split("\n\n")[0])
    print()
    by = shapes_by_mu()
    tot = sum(len(v) for v in by.values())
    print("   inner boundaries: %d   connected diagrams: %d   (size <= %d, rows <= %d)"
          % (len(by), tot, SIZE_CAP, ROW_CAP))

    pairs = 0
    unequal_pairs = 0
    ident = 0
    ident_unequal = []
    ident_equal = 0
    for mu, shs in by.items():
        for A, B in combinations(shs, 2):
            pairs += 1
            same = rho(A) == rho(B)
            if not same:
                unequal_pairs += 1
            G = defect(A, B)
            if not nonzero(G):
                continue
            rp = ratio_pairs(G)
            if not rp:
                continue
            ident += 1
            if same:
                ident_equal += 1
            else:
                ident_unequal.append((mu, A, B, rp, rho(A), rho(B)))

    print("   ordered-free pairs on a common boundary: %d   of which UNEQUAL row multisets: %d"
          % (pairs, unequal_pairs))
    print("   pairs with a nonzero defect satisfying some ratio identity: %d" % ident)
    print()

    print("(1) IS THE POPULATION NON-VACUOUS -- are there ratio-identity pairs at all,")
    print("    and are there unequal-multiset pairs for the claim to be about?")
    check("ratio-identity pairs exist", ident > 0, "%d" % ident)
    check("unequal-multiset pairs exist in the enumeration", unequal_pairs > 0,
          "%d of %d" % (unequal_pairs, pairs))
    print()

    print("(2) THE CLAIM: does a ratio identity force equal row-length multisets?")
    if ident_unequal:
        print("    *** REFUTED.  %d ratio-identity pair(s) have UNEQUAL row multisets:"
              % len(ident_unequal))
        for mu, A, B, rp, ra, rb in ident_unequal[:6]:
            print("        mu=%s  A=%s  B=%s" % (str(mu), str(A), str(B)))
            print("           identities at %s;  rho(A)=%s  rho(B)=%s" % (rp, ra, rb))
    check("every ratio-identity pair has equal row-length multisets",
          not ident_unequal,
          "%d with equal multisets, %d with unequal" % (ident_equal, len(ident_unequal)))
    print()

    print("(3) CONTROL: the equal-multiset case is where the identities actually live,")
    print("    so the check is not passing because the unequal side is empty of defects.")
    check("some ratio-identity pair was found on the equal-multiset side",
          ident_equal > 0, "%d" % ident_equal)

    print()
    if FAILURES:
        print("*** %d CHECK(S) FAILED" % len(FAILURES))
        for f in FAILURES:
            print("      " + f)
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
