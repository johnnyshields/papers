r"""Paper section `sec:geometry` (Strict-Monge geometry of cofactor actions).  Target labels:
`lem:grid-order`, `lem:diagonal-feasible`, `lem:valuation-laws`, `lem:strict-monge`,
`lem:feasible-uncrossing`, `thm:monge-minor`, `prop:cofactor-initial`, `lem:distinguished`,
`prop:action-recurrence`, `prop:initial-energy`, `def:convex-weight`.

Everything the paper states for an ARBITRARY admissible convex weight is asserted here at four of them
-- square, cubic, radix B = 7 and the rational k^2 + k^3/7 -- not at the square weight alone, over every
connected diagram up to SIZE_CAP cells and ROW_CAP rows and over a box of staircase submatrices.  Objects
come from `_census_common` (cofactors by Laplace expansion of the capped matrix of `eq:capmatrix`) and
`skew_core.det_h` (full permutation expansion, used for the minors of `thm:monge-minor`, so the initial
monomial and its coefficient are read off the true polynomial).  Exact integer / `Fraction` arithmetic.

  * lem:valuation-laws    weight of a product, of a sum, and equality when the minima differ, on pairs
                          of cofactors and on sums built to cancel at the lower level;
  * lem:strict-monge      over the full box of admissible quadruples, with the strictness shown tight by
                          the boundary case where a hypothesis fails;
  * thm:monge-minor       the increasing matching is the unique minimum-weight term of every feasible
                          square submatrix, its coefficient is +1, and infeasible means zero;
  * prop:cofactor-initial the initial face of every capped cofactor is the single monomial the paper
                          prints, with coefficient (-1)^j, and the weight formula follows;
  * prop:action-recurrence the increment formula, strict increase in A_j, and the square-weight collapse
                          to 2 A_j (d_{j+1} - d_j);
  * prop:initial-energy   sigma_0 is the sum of omega of the row lengths, hence equal across equal
                          row-length multisets.
"""
import itertools
import sys
from collections import defaultdict

from _census_common import (
    WEIGHTS, SQ, admissible, cofvec, det_h, gen_shapes, grid, h, init_face, neg, padd, pmul, rows,
    wmon, wpoly,
)

SIZE_CAP = 10
ROW_CAP = 5
BOX = 14


def main():
    for nm, om in WEIGHTS.items():
        assert admissible(om), nm
    # the definition has teeth: the linear weight and a weight with a tie are not admissible
    assert not admissible(lambda k: k)
    assert not admissible(lambda k: 0 if k == 0 else 2 ** k)
    assert not admissible(lambda k: -k * k)

    # ---------------------------------------------------------------- lem:strict-monge
    n_sm = 0
    for nm, om in WEIGHTS.items():
        for A, Ap, d, dp in itertools.product(range(0, 9), repeat=4):
            if not (A < Ap and d < dp):
                continue
            if min(d - A, dp - Ap, dp - A, d - Ap) < 0:
                continue
            assert om(d - A) + om(dp - Ap) < om(dp - A) + om(d - Ap), (nm, A, Ap, d, dp)
            n_sm += 1
    # tightness: for the linear weight the inequality is an equality, so strictness is the hypothesis
    for A, Ap, d, dp in itertools.product(range(0, 7), repeat=4):
        if A < Ap and d < dp and min(d - A, dp - Ap, dp - A, d - Ap) >= 0:
            assert (d - A) + (dp - Ap) == (dp - A) + (d - Ap)
    print("lem:strict-monge: %d (weight, A, A', d, d') cases strict; equality for the linear weight" % n_sm)

    # ---------------------------------------------------------------- thm:monge-minor
    n_feas = n_infeas = 0
    for nm, om in WEIGHTS.items():
        for n in (2, 3, 4):
            for A in itertools.combinations(range(0, 8), n):
                for d in itertools.combinations(range(0, 10), n):
                    ent = [[dj - ai for dj in d] for ai in A]
                    poly = det_h(ent)
                    feasible = all(ent[i][i] >= 0 for i in range(n))
                    if feasible:
                        assert poly, ("feasible minor must be nonzero", nm, A, d)
                        w, fc = init_face(poly, om)
                        assert len(fc) == 1, ("unique minimum-weight term", nm, A, d, fc)
                        (mon, c), = fc.items()
                        assert c == 1, ("coefficient +1", nm, A, d)
                        want = tuple(sorted((ent[i][i] for i in range(n) if ent[i][i] > 0), reverse=True))
                        assert mon == want, ("the increasing matching", nm, A, d)
                        n_feas += 1
                    else:
                        assert not poly, ("infeasible must vanish", nm, A, d)
                        n_infeas += 1
    print("thm:monge-minor: %d feasible minors (unique initial monomial, coefficient +1, the increasing"
          % n_feas)
    print("    matching) and %d infeasible minors (all zero), at four weights" % n_infeas)

    shapes = gen_shapes(SIZE_CAP, ROW_CAP)
    print("connected diagrams, size <= %d, rows <= %d : %d" % (SIZE_CAP, ROW_CAP, len(shapes)))

    # ---------------------------------------------------------------- lem:valuation-laws
    n_vl = n_cancel = 0
    pool = []
    for sh in shapes[::7]:
        pool.extend(f for f in cofvec(sh) if f)
    pool = pool[:400]
    for nm, om in WEIGHTS.items():
        for f in pool[:60]:
            for g in pool[:60]:
                assert wpoly(pmul(f, g), om) == wpoly(f, om) + wpoly(g, om), ("product", nm)
                s = padd(f, g)
                if s:
                    assert wpoly(s, om) >= min(wpoly(f, om), wpoly(g, om)), ("sum", nm)
                    if wpoly(f, om) != wpoly(g, om):
                        assert wpoly(s, om) == min(wpoly(f, om), wpoly(g, om)), ("equality", nm)
                    n_vl += 1
                # equal minima may cancel: f + (-f) = 0 and f - g with a shared leading term drops
                if f is g:
                    assert not padd(f, neg(g))
                    n_cancel += 1
        # the strict inequality is attained: cancellation at the lower level raises the weight
        f = {(2, 1): 1, (3,): 1}
        g = {(2, 1): -1, (4,): 1}
        w = wpoly(padd(f, g), om)
        assert w > min(wpoly(f, om), wpoly(g, om)) and not padd(f, g).get((2, 1)), (nm,)
    print("lem:valuation-laws: product additive, sum bounded below and exact when minima differ, on %d" % n_vl)
    print("    sums of capped cofactors at four weights; strict inequality attained by a cancelling pair")

    # ---------------------------------------------------------------- prop:cofactor-initial & co.
    n_ci = n_ar = n_ie = 0
    by_mult = defaultdict(list)
    for sh in shapes:
        lam, mu = sh
        n = len(lam)
        A, d = grid(sh)
        vec = cofvec(sh)
        rho = rows(sh)
        o = [lam[i + 1] - mu[i] for i in range(n - 1)]
        assert A[0] == 0 and d[0] == 0
        assert all(A[i] < A[i + 1] for i in range(n - 1)) and all(d[j] < d[j + 1] for j in range(n)), sh
        assert all(A[i] <= d[i] for i in range(n)), ("lem:diagonal-feasible", sh)
        assert all(A[i + 1] - A[i] == lam[i] - lam[i + 1] + 1 for i in range(n - 1))
        assert d[1] == lam[0] - mu[0] and all(d[j + 1] - d[j] == mu[j - 1] - mu[j] + 1 for j in range(1, n))
        for nm, om in WEIGHTS.items():
            sig = []
            for j in range(n + 1):
                assert vec[j], ("C_j != 0", sh, j)
                want_mon = tuple(sorted(
                    [d[i] - A[i] for i in range(j) if d[i] - A[i] > 0]
                    + [d[i + 1] - A[i] for i in range(j, n) if d[i + 1] - A[i] > 0], reverse=True))
                w, fc = init_face(vec[j], om)
                assert fc == {want_mon: (-1) ** j}, ("eq:cofactor-initial", nm, sh, j, fc)
                wformula = (sum(om(d[i] - A[i]) for i in range(j))
                            + sum(om(d[i + 1] - A[i]) for i in range(j, n)))
                assert w == wformula, ("eq:cofactor-val", nm, sh, j)
                # lem:distinguished: d_{i+1} - A_i = rho_i and d_i - A_i = o_{i-1} - 1
                Q = tuple(sorted([o[i - 1] - 1 for i in range(1, j) if o[i - 1] - 1 > 0]
                                 + [rho[i] for i in range(j, n)], reverse=True))
                assert Q == want_mon, ("eq:Qj", nm, sh, j)
                n_ci += 1
                sig.append(w + om(d[j]))
            # prop:action-recurrence
            for j in range(n):
                lhs = sig[j + 1] - sig[j]
                rhs = (om(d[j] - A[j]) - om(d[j + 1] - A[j]) + om(d[j + 1]) - om(d[j]))
                assert lhs == rhs, ("increment", nm, sh, j)
                if nm == "square":
                    assert lhs == 2 * A[j] * (d[j + 1] - d[j]), ("square collapse", sh, j)
                n_ar += 1
            # prop:initial-energy
            assert sig[0] == sum(om(r) for r in rho), ("eq:initial-energy", nm, sh)
            n_ie += 1
        by_mult[tuple(sorted(rho))].append(sh)
    # equal multisets give equal sigma_0 at every weight, across different diagrams
    n_eq = 0
    for mult, mem in by_mult.items():
        if len(mem) < 2:
            continue
        for nm, om in WEIGHTS.items():
            vals = {wpoly(cofvec(s)[0], om) for s in mem}
            assert len(vals) == 1, ("equal multisets, equal sigma_0", nm, mult)
        n_eq += len(mem)
    # strict increase of the recurrence in A_j, for fixed d_j < d_{j+1}, over the feasible range
    n_inc = 0
    for nm, om in WEIGHTS.items():
        for dj in range(0, 8):
            for dj1 in range(dj + 1, 11):
                vals = [(om(dj - Aj) - om(dj1 - Aj) + om(dj1) - om(dj)) for Aj in range(0, dj + 1)]
                assert all(b > a for a, b in zip(vals, vals[1:])), (nm, dj, dj1)
                n_inc += 1
    print("prop:cofactor-initial / lem:distinguished: %d (diagram, column, weight) initial faces equal the printed" % n_ci)
    print("    monomial with coefficient (-1)^j, and the weight formula holds")
    print("prop:action-recurrence: %d increments equal the displayed formula (square: 2 A_j (d_{j+1}-d_j));" % n_ar)
    print("    strictly increasing in A_j on %d (weight, d_j, d_{j+1}) cells" % n_inc)
    print("prop:initial-energy: %d (diagram, weight) cases; %d diagrams in equal-multiset groups agree" % (n_ie, n_eq))
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
