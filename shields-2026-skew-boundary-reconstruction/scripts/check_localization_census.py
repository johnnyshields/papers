r"""Paper section `sec:localization` (First-split localization and cap-fixed rigidity).  Target labels:
`eq:common-row-relation`, `prop:synchronization`, `cor:first-split-anchor`, `lem:tropical-balancing`,
`lem:tail-increase`, `thm:no-backflow`, `lem:marching`, `thm:cap-fixed-rigidity`,
`lem:equality-normalizes-cap`, `thm:equal-pair-rigidity`, `prop:monomial-prefix`,
`cor:boundary-separation`, `ex:actual-equal-chain`.

One census, run at four admissible convex weights (square, cubic, radix B=7, and a rational one), over
every pair of distinct connected diagrams with a common inner boundary, a common number of rows and a
common top row (hence a common cap grid), up to SIZE_CAP cells and ROW_CAP rows.  Every object is rebuilt
from the paper's definitions by `_census_common`: the cofactors are full permutation expansions of the
capped matrix, so each assertion is a polynomial identity, not a numerical coincidence.

The cap-fixed population is deliberately NOT pre-filtered on equal row-length multisets: the theorem
states that its floor antecedent supplies them, so the census asserts that the antecedent never holds on
a pair with unequal multisets.  Pairs failing the antecedent are the other branch and carry no
conclusion; one of them is exhibited as the control that shows the antecedent load-bearing.
"""
import sys
from collections import Counter, defaultdict

from _census_common import (
    WEIGHTS, SQ, Pair, admissible, argmin, buckets, cofvec, cofvec_reference, extend, gen_shapes, grid, h,
    init_face, neg, padd, pmul, rows, s_poly, sub, wpoly, Pk,
)

SIZE_CAP = 11
ROW_CAP = 5
# The deep pass keeps only pairs with equal row-length multisets (the broad pass above has just asserted
# that the floor antecedent never holds on any other pair) and reaches first changed rows v = 3 and 4,
# where the marching chain has several steps to take.
DEEP_SIZE_CAP = 13
DEEP_ROW_CAP = 6


def mono_times_h(m, k):
    """The monomial m * h_k (h_0 = 1)."""
    return tuple(sorted(m + ((k,) if k > 0 else ()), reverse=True))


def run(SIZE_CAP, ROW_CAP, deep):
    for name, om in WEIGHTS.items():
        assert admissible(om), name

    shapes = gen_shapes(SIZE_CAP, ROW_CAP)
    # the memoized determinant against full permutation expansion, on every diagram it can afford
    n_ref = 0
    for sh in shapes:
        if len(sh[0]) <= 5 and sum(rows(sh)) <= 9:
            assert cofvec(sh) == cofvec_reference(sh), sh
            n_ref += 1
    assert n_ref > 100
    pairs = []
    keyf = ((lambda s: (s[1], s[0][0], len(s[0]), tuple(sorted(rows(s)))))
            if deep else (lambda s: (s[1], s[0][0], len(s[0]))))
    for key, mem in sorted(buckets(shapes, keyf).items()):
        for a in range(len(mem)):
            for b in range(a + 1, len(mem)):
                pairs.append(Pair(mem[a], mem[b]))
    print("connected diagrams, size <= %d, rows <= %d : %d" % (SIZE_CAP, ROW_CAP, len(shapes)))
    print("cap-fixed pairs (common mu, rows, top row)  : %d" % len(pairs))

    n_eq_multiset = 0
    n_relation = 0
    antecedent = defaultdict(int)       # (weight, v) -> count
    other_branch = defaultdict(int)
    control_witness = None
    n_equal = 0
    n_marching = 0
    n_backflow = 0
    equal_pairs = []

    for P in pairs:
        n, d, v, q, G = P.n, P.d, P.v, P.q, P.G
        assert v >= 1                                   # a common top row forces A_0 = 0 on both
        assert any(G)                                   # distinct diagrams have distinct cofactor vectors
        # eq:common-row-relation, and eq:P0-vanishes for each parent separately
        for i in range(v):
            tot = {}
            for j in range(n + 1):
                if G[j] and d[j] - P.AX[i] >= 0:
                    tot = padd(tot, pmul(G[j], h(d[j] - P.AX[i])))
            assert not tot, ("common-row relation", P.X, P.Y, i)
        assert not Pk(P.CX, d, 0) and not Pk(P.CY, d, 0), (P.X, P.Y)
        n_relation += 1

        same_multiset = sorted(rows(P.X)) == sorted(rows(P.Y))
        n_eq_multiset += same_multiset
        for wname, om in WEIGHTS.items():
            al = P.alpha(om)
            pos = [j for j in range(1, n + 1) if al[j] is not None]
            assert pos, (P.X, P.Y)
            m_plus = min(al[j] for j in pos)

            if same_multiset:
                # prop:synchronization
                sx, sy = P.sigma("X", om), P.sigma("Y", om)
                for j in range(v + 1):
                    assert sx[j] == sy[j], ("synchronization", P.X, P.Y, wname, j)
                assert sx[q] != sy[q], ("first split", P.X, P.Y, wname)
                lhs = (sx[q] > sy[q]) - (sx[q] < sy[q])
                rhs = (P.AX[v] > P.AY[v]) - (P.AX[v] < P.AY[v])
                assert lhs == rhs, ("direction of the split", P.X, P.Y, wname)
                # cor:first-split-anchor
                assert al[q] is not None and al[q] == min(sx[q], sy[q]), ("anchor", P.X, P.Y, wname)
                # lem:tropical-balancing
                mins = []
                for i in range(v):
                    Fi = P.F(i, om, al)
                    assert Fi, (P.X, P.Y, i)
                    mn, M = argmin(Fi)
                    assert len(M) >= 2, ("tropical balancing", P.X, P.Y, wname, i, M)
                    mins.append(M)
                    assert max(M) <= q, ("eq:R-upper", P.X, P.Y, wname, i, M)
                # lem:marching
                for i in range(v - 1):
                    assert max(mins[i + 1]) > max(mins[i]), ("marching", P.X, P.Y, wname, i)
                    assert min(mins[i + 1]) >= max(mins[i]), ("interlacing", P.X, P.Y, wname, i)
                    n_marching += 1
                # lem:tail-increase, on each parent, and thm:no-backflow
                for which, sg, A in (("X", sx, P.AX), ("Y", sy, P.AY)):
                    for i in range(v):
                        def Fpar(j, sg=sg, i=i):
                            assert d[j] >= A[i]
                            return sg[j] + om(d[j] - A[i]) - om(d[j])
                        for k in range(q, n):
                            assert Fpar(k + 1) > Fpar(k), ("tail increase", P.X, P.Y, wname, which, i, k)
                for i in range(v):
                    Fi = P.F(i, om, al)
                    for l in range(q + 1, n + 1):
                        if l in Fi:
                            assert Fi[l] > Fi[q], ("no-backflow", P.X, P.Y, wname, i, l)
                            n_backflow += 1
                            if wname == "square":
                                assert Fi[l] - Fi[q] >= (l - q) * (l + q - 2 * i - 1), \
                                    ("no-backflow margin", P.X, P.Y, i, l)

            # thm:cap-fixed-rigidity: no multiset hypothesis, only the floor antecedent
            holds = al[0] is None or al[0] > m_plus
            if holds:
                antecedent[(wname, v)] += 1
                assert same_multiset, ("the floor must supply equal multisets", P.X, P.Y, wname)
                for i in range(v):
                    mn, M = argmin(P.F(i, om, al))
                    assert M == [i + 1, i + 2], ("adjacent chain", P.X, P.Y, wname, i, M)
                T0 = [j for j in pos if al[j] == m_plus]
                assert T0 == [1, 2], ("floor set", P.X, P.Y, wname, T0)
                for j in range(1, v + 2):
                    assert al[j] is not None, ("support prefix", P.X, P.Y, wname, j)
                assert al[1] == al[2], (P.X, P.Y, wname)
                for j in range(2, v + 1):
                    assert al[j] < al[j + 1], ("prefix profile", P.X, P.Y, wname, j)
                for j in range(v + 2, n + 1):
                    if al[j] is not None:
                        assert al[j] > al[v + 1], ("tail", P.X, P.Y, wname, j)
                for i in range(v):             # the exact adjacent recurrence
                    assert al[i + 2] - al[i + 1] == (om(d[i + 2]) - om(d[i + 2] - P.AX[i])
                                                     - om(d[i + 1]) + om(d[i + 1] - P.AX[i])), \
                        ("adjacent recurrence", P.X, P.Y, wname, i)
                assert len(pos) >= v + 1                     # m >= v + 1 positive supported shifts
                if al[0] is None:
                    if wname == "square":
                        equal_pairs.append(P)
            else:
                other_branch[wname] += 1
                if wname == "square" and same_multiset and al[0] == m_plus:
                    mn, M = argmin(P.F(0, om, al)) if v >= 1 else (None, None)
                    T0 = [j for j in pos if al[j] == m_plus]
                    if M != [1, 2] or T0 != [1, 2]:
                        control_witness = control_witness or (P.X, P.Y, M, T0)

    print("pairs on which the common-row relation and P_0 = 0 were checked: %d" % n_relation)
    print("pairs with equal row-length multisets                          : %d" % n_eq_multiset)
    print("marching steps / no-backflow comparisons                       : %d / %d"
          % (n_marching, n_backflow))
    for wname in WEIGHTS:
        by_v = {v: c for (w, v), c in sorted(antecedent.items()) if w == wname}
        print("  %-8s floor antecedent holds by first changed row: %s   other branch: %d"
              % (wname, by_v, other_branch[wname]))
        assert by_v, wname
    if deep:
        # the chain is exercised past the first two steps, not only at the first split
        for wname in WEIGHTS:
            assert max(v for (w, v) in antecedent if w == wname) >= 3, wname
    else:
        # the antecedent is load-bearing: on alpha_0 = m_+ the chain can fail
        assert control_witness is not None
        print("control (alpha_0 = m_+, equal multisets, chain fails): %s vs %s, M_0 = %s, T_0^+ = %s"
              % control_witness)

    # ---- thm:equal-pair-rigidity and what it adds, on the actual equal pairs
    n_equal = len(equal_pairs)
    assert n_equal > 0
    for P in equal_pairs:
        n, d, v, q, G = P.n, P.d, P.v, P.q, P.G
        assert not G[0], (P.X, P.Y)                       # G_0 = s_X - s_Y
        faces = {}
        for wname, om in WEIGHTS.items():
            al = P.alpha(om)
            assert al[0] is None
            pos = [j for j in range(1, n + 1) if al[j] is not None]
            for i in range(v):
                assert argmin(P.F(i, om, al))[1] == [i + 1, i + 2], (P.X, P.Y, wname, i)
            assert [j for j in pos if al[j] == min(al[k] for k in pos)] == [1, 2]
            # prop:monomial-prefix: single monomials with unit coefficients, independent of omega
            for j in range(1, q + 1):
                w, fc = init_face(G[j], om)
                assert len(fc) == 1, ("single monomial", P.X, P.Y, wname, j, fc)
                (mon, c), = fc.items()
                assert c in (1, -1)
                faces.setdefault(j, (mon, c))
                assert faces[j] == (mon, c), ("omega-independence", P.X, P.Y, wname, j)
        eps = [faces[j][1] for j in range(1, q + 1)]
        mons = [faces[j][0] for j in range(1, q + 1)]
        for j in range(1, q):
            assert eps[j - 1] == -eps[j], ("alternating signs", P.X, P.Y, j)
            lhs = mono_times_h(mons[j - 1], d[j] - P.AX[j - 1])
            rhs = mono_times_h(mons[j], d[j + 1] - P.AX[j - 1])
            assert lhs == rhs, ("eq:monomial-prefix-exchange", P.X, P.Y, j)
        # cor:boundary-separation: eq:cap-leading-monomial and eq:ratio-leading-monomial
        for wname, om in WEIGHTS.items():
            for a in range(1, 7):
                Pa = Pk(G, d, a)
                assert Pa, ("P_a(G) != 0", P.X, P.Y, a)
                w, fc = init_face(Pa, om)
                want = {mono_times_h(mons[0], a + d[1]): eps[0]}
                assert fc == want, ("eq:cap-leading-monomial", P.X, P.Y, wname, a)
            for r in range(1, 5):
                for a in range(1, 5):
                    diff = sub(Pk(G, d, r + a), pmul(h(a), Pk(G, d, r)))
                    w, fc = init_face(diff, om)
                    want = {mono_times_h(mono_times_h(mons[0], a), r + d[1]): -eps[0]}
                    assert fc == want, ("eq:ratio-leading-monomial", P.X, P.Y, wname, r, a)
    print("actual equal pairs (G_0 = 0) with a common cap grid: %d; chain, single-monomial prefix,"
          % n_equal)
    print("  exchange identity and both leading-monomial formulas hold at all four weights")

    if deep:
        return
    # ---- lem:equality-normalizes-cap, over every connected diagram and every equal pair
    by_s = defaultdict(list)
    for sh in shapes:
        f = cofvec(sh)[0]
        lam, mu = sh
        n = len(lam)
        H = lam[0] - mu[n - 1] + n - 1
        assert max(max(m, default=0) for m in f) == H, ("eq:largest-index", sh)
        for t in (1, 2, 3):                             # the translation term is exercised
            lam_t = tuple(x + t for x in lam)
            mu_t = tuple(x + t for x in mu)
            f_t = s_poly((lam_t, mu_t))
            assert f_t == f
            assert max(max(m, default=0) for m in f_t) == lam_t[0] - mu_t[n - 1] + n - 1
        by_s[tuple(sorted(f.items()))].append(sh)
    n_classes = n_pairs_eq = 0
    smallest = None
    for cls in by_s.values():
        if len(cls) < 2:
            continue
        n_classes += 1
        for a in range(len(cls)):
            for b in range(a + 1, len(cls)):
                X, Y = cls[a], cls[b]
                assert sorted(rows(X)) == sorted(rows(Y)) and len(X[0]) == len(Y[0]), (X, Y)
                n_pairs_eq += 1
                if X[1] == Y[1]:
                    assert X[0][0] == Y[0][0], ("(ii) lambda_0 = kappa_0", X, Y)
                    sz = sum(rows(X))
                    if smallest is None or sz < smallest[0]:
                        smallest = (sz, [(X, Y)])
                    elif sz == smallest[0]:
                        smallest[1].append((X, Y))
    print("skew-equivalent classes with >= 2 diagrams: %d, %d equal pairs (any inner boundaries):"
          % (n_classes, n_pairs_eq))
    print("  row-length multisets and row counts agree on every one; lambda_0 = kappa_0 whenever mu is common")
    # ex:actual-equal-chain is a smallest instance of the theorem (common inner boundary)
    X0 = ((4, 4, 4, 2), (3, 2, 1, 0))
    Y0 = ((4, 4, 3, 3), (3, 2, 1, 0))
    assert smallest[0] == 8 and ((X0, Y0) in smallest[1] or (Y0, X0) in smallest[1]), smallest
    print("  smallest equal pair on a common inner boundary has %d cells: %s" % (smallest[0], smallest[1]))


def main():
    run(SIZE_CAP, ROW_CAP, deep=False)
    print("--- deep pass: equal row-length multisets, size <= %d, rows <= %d" % (DEEP_SIZE_CAP, DEEP_ROW_CAP))
    run(DEEP_SIZE_CAP, DEEP_ROW_CAP, deep=True)
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
