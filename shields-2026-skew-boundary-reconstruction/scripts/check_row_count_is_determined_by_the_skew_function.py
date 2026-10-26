#!/usr/bin/env python3
"""Is the row count `n` redundant in `thm:boundary-reconstruction` and
`cor:two-positive-extensions`?

Both statements open "Fix an inner boundary \\(\\mu\\) and a number \\(n\\) of nonempty
rows."  The question is whether `n` is already determined by the data the maps observe,
so that fixing it restricts the domain for nothing.

THE ARGUMENT THE PAPER ALREADY CARRIES.  The increasing matching of the ordinary
Jacobi-Trudi matrix has monomial prod_i h_{lam_i - mu_i}, and by `thm:monge-minor` it
is the unique leading one.  Since h_0 = 1, the number of factors of subscript >= 1 is
exactly the number of nonempty rows, and a polynomial determines its own leading
monomial -- so s_X determines n.  For the corollary the observed functions are
s_{X.(a)} and s_{X.(b)}, whose row-length multisets are {a} u rho(X) with a >= 1, each
determining n + 1 and hence n.

WHY THE READING MATTERS, and it is the whole reason this is checked rather than
asserted.  `connected` forbids an empty row, so if mu is read as a PADDED TUPLE of
length n then n = len(mu) and fixing it is redundant trivially -- dropping it would be
cosmetic, not a strengthening.  The domain only varies if mu is read as an inner
FERRERS SHAPE, trailing zeros insignificant: then lam may have len(mu) rows, or
len(mu) + 1 with mu padded by a zero, and both diagrams have the same inner boundary.
This holds the Ferrers shape fixed and lets lam's length vary, which is the reading
under which `n` is a genuine restriction.

(1) Over a fixed inner Ferrers shape, do connected diagrams of different row counts
    exist at all?
(2) Does s_X determine the row count, over every pair in the enlarged domain?
(3) Is X |-> (s_X, s_Xbar) injective over the enlarged domain?
(4) Is X |-> (s_{X.(a)}, s_{X.(b)}) injective over the enlarged domain?
(5) The step the argument rests on: rho(X.(m)) = {m} u rho(X) as multisets.

Exact integer arithmetic throughout: `s_poly` returns the signed h-monomial multiset,
so an equality here is a polynomial identity rather than a numerical coincidence.
"""

import sys
from collections import defaultdict

from functools import lru_cache

from skew_core import s_poly as _s_poly
from skew_harness import connected, size

SIZE_CAP = 12
MU_PARTS = 4          # inner Ferrers shapes of up to this many (positive) parts
FAILURES = []


@lru_cache(maxsize=None)
def s_poly(sh):
    """Memoized: every diagram is evaluated once per shape, and the extensions
    X.(a) recur across the (a, b) pairs."""
    return _s_poly(sh)


def check(label, cond, detail=""):
    print("   %-70s %s%s" % (label, "ok" if cond else "*** FAIL ***",
                             ("   " + detail) if detail else ""))
    if not cond:
        FAILURES.append(label)


def ferrers(maxpart, maxparts):
    """Partitions with POSITIVE parts only -- an inner Ferrers shape, no padding."""
    def rec(cap, left):
        yield ()
        if left == 0:
            return
        for p in range(min(cap, maxpart), 0, -1):
            for rest in rec(p, left - 1):
                yield (p,) + rest
    seen = set()
    for t in rec(maxpart, maxparts):
        if t not in seen:
            seen.add(t)
            yield t


def row_lengths(sh):
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return tuple(lam[i] - mu[i] for i in range(len(lam)))


def nrows(sh):
    return sum(1 for r in row_lengths(sh) if r > 0)


def first_row_deleted(sh):
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    if len(lam) <= 1:
        return ((), ())
    return (tuple(lam[1:]), tuple(mu[1:]))


def extend(sh, m):
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return ((m + lam[0] - 1,) + tuple(lam), (lam[0] - 1,) + tuple(mu))


@lru_cache(maxsize=None)
def skey(sh):
    return tuple(sorted(s_poly(sh).items()))


def key(poly):
    return tuple(sorted(poly.items()))


def diagrams_over(mu_shape):
    """Connected lam/mu for this inner Ferrers shape, at len(mu) AND len(mu)+1 rows.

    Row lengths are chosen positive and the resulting lam checked weakly decreasing,
    which is far cheaper than enumerating lam against mu.
    """
    out = []
    for extra in (0, 1):
        mu = tuple(mu_shape) + (0,) * extra
        n = len(mu)
        if n == 0:
            continue

        def rec(i, rows, used):
            if i == n:
                lam = tuple(mu[j] + rows[j] for j in range(n))
                if all(lam[j] >= lam[j + 1] for j in range(n - 1)):
                    sh = (lam, mu)
                    if connected(sh) and 0 < size(sh) <= SIZE_CAP:
                        out.append(sh)
                return
            for r in range(1, SIZE_CAP - used + 1):
                rec(i + 1, rows + [r], used + r)

        rec(0, [], 0)
    return out


def main():
    print(__doc__.split("\n\n")[0])
    print()
    by_mu = {}
    for mu_shape in ferrers(SIZE_CAP, MU_PARTS):
        ds = diagrams_over(mu_shape)
        if ds:
            by_mu[mu_shape] = ds
    tot = sum(len(v) for v in by_mu.values())
    print("   inner Ferrers shapes: %d   connected diagrams: %d   (size <= %d, mu parts <= %d)"
          % (len(by_mu), tot, SIZE_CAP, MU_PARTS))
    print()

    # ---- (1) is the enlarged domain actually larger? ----
    mixed = {m: v for m, v in by_mu.items() if len({nrows(s) for s in v}) > 1}
    print("(1) IS THE WIDENING NON-VACUOUS?")
    check("some inner boundary carries diagrams of two different row counts",
          bool(mixed), "%d of %d shapes do" % (len(mixed), len(by_mu)))
    if mixed:
        m0 = sorted(mixed)[len(mixed) // 2]
        print("      e.g. mu = %s carries row counts %s"
              % (str(m0), sorted({nrows(s) for s in mixed[m0]})))
    print()

    # ---- (2) does s_X determine n? ----
    print("(2) DOES s_X DETERMINE n?")
    coll = 0
    tested = 0
    for mu, shapes in by_mu.items():
        buckets = defaultdict(set)
        for sh in shapes:
            buckets[skey(sh)].add(nrows(sh))
        for k, ns in buckets.items():
            tested += 1
            if len(ns) > 1:
                coll += 1
                print("      *** one function, row counts %s, over mu = %s"
                      % (sorted(ns), str(mu)))
    check("no skew Schur function is shared by two row counts", coll == 0,
          "%d distinct functions" % tested)
    check("not vacuous", tested > 0)
    print()

    # ---- (3) and (4) injectivity with n dropped ----
    print("(3) IS X |-> (s_X, s_Xbar) INJECTIVE WITH n DROPPED?")
    bad = 0
    for mu, shapes in by_mu.items():
        seen = {}
        for sh in shapes:
            k = (skey(sh), skey(first_row_deleted(sh)))
            if k in seen and seen[k] != sh:
                bad += 1
                print("      *** %s and %s collide over mu = %s"
                      % (str(seen[k]), str(sh), str(mu)))
            seen[k] = sh
    check("injective on the enlarged domain", bad == 0, "%d diagrams" % tot)
    print()

    print("(4) IS X |-> (s_{X.(a)}, s_{X.(b)}) INJECTIVE WITH n DROPPED?")
    for (a, b) in [(1, 2), (1, 3), (2, 3)]:
        bad = 0
        for mu, shapes in by_mu.items():
            seen = {}
            for sh in shapes:
                k = (skey(extend(sh, a)), skey(extend(sh, b)))
                if k in seen and seen[k] != sh:
                    bad += 1
                    print("      *** a=%d b=%d: %s and %s collide over mu = %s"
                          % (a, b, str(seen[k]), str(sh), str(mu)))
                seen[k] = sh
        check("(a, b) = (%d, %d): injective on the enlarged domain" % (a, b), bad == 0)
    print()

    # ---- (5) the multiset step ----
    print("(5) rho(X.(m)) = {m} u rho(X)?")
    bad = 0
    n5 = 0
    for mu, shapes in by_mu.items():
        for sh in shapes[:25]:
            for m in (1, 2, 3):
                n5 += 1
                got = sorted(r for r in row_lengths(extend(sh, m)) if r > 0)
                want = sorted([m] + [r for r in row_lengths(sh) if r > 0])
                if got != want:
                    bad += 1
    check("holds as multisets", bad == 0, "%d instances" % n5)

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
