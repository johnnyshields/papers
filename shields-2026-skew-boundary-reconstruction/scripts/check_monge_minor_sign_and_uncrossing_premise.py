#!/usr/bin/env python3
"""Two statements that deliver more than they claim (items c and d).

(c) `lem:feasible-uncrossing` states: for A < A' and d < d', if the CROSSED entries
    h_{d'-A} and h_{d-A'} are both nonzero then the ALIGNED entries h_{d-A} and
    h_{d'-A'} are also nonzero.  The first premise is never used.  h_k != 0 means
    k >= 0, so h_{d-A'} != 0 gives d >= A'; with A < A' that gives d - A > 0, and with
    d' > d it gives d' - A' > 0.  Both conclusions follow from the SECOND premise alone,
    and h_{d'-A} >= 0 is free from d' > d >= A' > A rather than assumed.  Checked here
    exhaustively over a box rather than argued once.

(d) `thm:monge-minor` states that a feasible increasing matching is the unique
    minimum-omega-weight term, so the minor is nonzero and its omega-initial monomial
    has coefficient +-1.  The coefficient is +1: the selected rows and columns are both
    in increasing order, so the increasing matching IS the identity permutation of the
    selected index sets and carries sign +1, and uniqueness of the minimum-weight term
    means nothing cancels it.  The sign the reader meets lives in eq:cofactor's (-1)^j,
    not here.  Also tested: whether an INFEASIBLE increasing matching forces the minor
    to vanish, which is the `iff` half of the same item.

Exact integer arithmetic; det_h expands over all permutations, so the initial monomial
and its coefficient are read off the true polynomial.
"""

import os
import sys
from itertools import combinations, product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from skew_core import det_h                                # noqa: E402

FAILURES = []


def check(label, cond, detail=""):
    print("   %-66s %s%s" % (label, "ok" if cond else "*** FAIL ***",
                             ("   " + detail) if detail else ""))
    if not cond:
        FAILURES.append(label)


def wt2(mono):
    """Square weight of an h-monomial, the paper's principal example."""
    return sum(k * k for k in mono)


def initial(poly):
    """(monomial, coefficient) of the unique minimum-square-weight term, or None
    if the minimum is attained more than once."""
    if not poly:
        return None
    best = min(wt2(m) for m in poly)
    tied = [m for m in poly if wt2(m) == best]
    if len(tied) != 1:
        return ("TIE", len(tied))
    m = tied[0]
    return (m, poly[m])


def main():
    print(__doc__.split("\n\n")[0])
    print()

    # ---------------- (c) the redundant premise ----------------
    print("(c) lem:feasible-uncrossing -- is the FIRST premise used?")
    N = 14
    tested = premise2_only = 0
    bad = []
    only_first = 0
    for A, Ap, d, dp in product(range(N), repeat=4):
        if not (A < Ap and d < dp):
            continue
        tested += 1
        crossed = (dp - A >= 0) and (d - Ap >= 0)
        aligned = (d - A >= 0) and (dp - Ap >= 0)
        if crossed and not aligned:
            bad.append((A, Ap, d, dp))
        # the claim: premise 2 ALONE implies the conclusion
        if (d - Ap >= 0):
            premise2_only += 1
            if not aligned:
                bad.append(('p2', A, Ap, d, dp))
        # and premise 1 alone does NOT
        if (dp - A >= 0) and not (d - Ap >= 0) and not aligned:
            only_first += 1
    check("the lemma as stated holds", not bad, "%d (A,A',d,d') quadruples" % tested)
    check("premise 2 ALONE implies both conclusions", not bad,
          "%d quadruples satisfy premise 2" % premise2_only)
    check("premise 1 alone does NOT suffice, so the two are not interchangeable",
          only_first > 0, "%d quadruples where premise 1 holds and the conclusion fails"
          % only_first)
    print()

    # ---------------- (d) the sign, and the iff ----------------
    print("(d) thm:monge-minor -- is the initial coefficient +1, and does infeasibility")
    print("    force the minor to vanish?")
    plus1 = minus1 = ties = 0
    feas_zero = []
    infeas_nonzero = []
    nfeas = ninfeas = 0
    # staircase (h_{d_j - A_i}) with increasing A and increasing d; take square submatrices
    for n in (2, 3, 4):
        for A in combinations(range(0, 9), n):
            for d in combinations(range(0, 11), n):
                ent = [[dj - ai for dj in d] for ai in A]
                poly = det_h(ent)
                # the increasing matching pairs row i with column i
                feasible = all(ent[i][i] >= 0 for i in range(n))
                if feasible:
                    nfeas += 1
                    if not poly:
                        feas_zero.append((A, d))
                        continue
                    ini = initial(poly)
                    if ini and ini[0] == "TIE":
                        ties += 1
                    elif ini:
                        if ini[1] == 1:
                            plus1 += 1
                        elif ini[1] == -1:
                            minus1 += 1
                else:
                    ninfeas += 1
                    if poly:
                        infeas_nonzero.append((A, d))
    check("a feasible increasing matching gives a NONZERO minor", not feas_zero,
          "%d feasible submatrices" % nfeas)
    check("its minimum-square-weight term is unique (no tie)", ties == 0,
          "%d ties" % ties)
    check("and that term's coefficient is +1, never -1", minus1 == 0,
          "+1 on %d, -1 on %d" % (plus1, minus1))
    check("the +1 test is not vacuous", plus1 > 0)
    print()
    print("    the `iff` half, reported rather than asserted:")
    check("an INFEASIBLE increasing matching forces the minor to vanish",
          not infeas_nonzero,
          "%d infeasible submatrices, %d of them with a nonzero minor"
          % (ninfeas, len(infeas_nonzero)))
    if infeas_nonzero:
        print("       counterexamples to the iff (so the statement's `if` is not an `iff`):")
        for A, d in infeas_nonzero[:4]:
            print("          A=%s d=%s" % (str(A), str(d)))

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
