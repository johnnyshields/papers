r"""Paper section `sec:full-rigidity` (Ratio identities and full adjacent-edge rigidity) and `sec:two-cap`
(Two-cap exclusion).  Target labels: `lem:ratio-row-lengths`, `eq:bounded-generator`, `thm:terminal-gap`,
`prop:top-terminal`, `cor:cap-fixing`, `thm:ratio-rigidity`, `eq:virtual-gap-general`, `eq:square-gap`,
`lem:laplace-equivalence`, `thm:floor`, `thm:two-cap`, `cor:floor-supplies`, `cor:double-cap-kills`,
`cor:unique-ratio`.

The ratio locus is enumerated, not sampled.  The ratio identity at (r, a),
P_{r+a}(G) = h_a P_r(G), is the equality T(A, r, a) = T(B, r, a) of the one-diagram quantity
T(X, r, a) = P_{r+a}(C(X)) - h_a P_r(C(X)), so the pairs on the locus are exactly the collisions of T over
the whole population of connected diagrams: every inner boundary, every row count, every top row.  Nothing
is filtered on equal row-length multisets, a common cap grid or a common inner boundary before the
conclusions are asserted, so the lemma that supplies the multisets and the corollary that supplies the grid
are tested rather than presupposed.  All objects come from `_census_common`, which rebuilds the cofactors
from the capped matrix by permutation expansion.  Exact integer arithmetic throughout.

  * lem:ratio-row-lengths   equal row-length multisets on EVERY ratio pair, with no common inner boundary;
  * cor:double-cap-kills    no pair of distinct diagrams carries two ratio identities at one base r;
  * cor:unique-ratio        on a common inner boundary no pair carries two identities at all;
  * prop:top-terminal       over every common-mu, equal-row-count pair with different top rows;
  * cor:cap-fixing, eq:bounded-generator, thm:terminal-gap, thm:ratio-rigidity, the gap formulas,
    thm:floor and cor:floor-supplies on every common-mu ratio pair, at four admissible weights;
  * lem:laplace-equivalence on every cap-fixed pair, ratio identity or not;
  * thm:two-cap             both hypotheses shown load-bearing by a formal vector outside the class.
"""
import sys
from collections import defaultdict

from _census_common import (
    WEIGHTS, SQ, Pair, admissible, argmin, cofvec, cofvec_reference, deg, extend, gen_shapes, grid, h, init_face, neg,
    padd, pmul, Pk, rows, sub, wpoly, det_h,
)

SIZE_CAP = 13
ROW_CAP = 6
TOP_SIZE_CAP = 10
TOP_ROW_CAP = 4
R_RANGE = range(0, 6)
A_RANGE = range(1, 6)


def T(sh, r, a):
    vec = cofvec(sh)
    _, d = grid(sh)
    return sub(Pk(vec, d, r + a), pmul(h(a), Pk(vec, d, r)))


def key(poly):
    return tuple(sorted(poly.items()))


def poly_det(M):
    """Laplace expansion of a square matrix of h-polynomials."""
    n = len(M)
    if n == 1:
        return M[0][0]
    out = {}
    for j in range(n):
        if not M[0][j]:
            continue
        minor = [row[:j] + row[j + 1:] for row in M[1:]]
        term = pmul(M[0][j], poly_det(minor))
        out = padd(out, term if j % 2 == 0 else neg(term))
    return out


def main():
    for nm, om in WEIGHTS.items():
        assert admissible(om), nm

    shapes = gen_shapes(SIZE_CAP, ROW_CAP)
    n_ref = 0
    for sh in shapes:
        if len(sh[0]) <= 5 and sum(rows(sh)) <= 9:
            assert cofvec(sh) == cofvec_reference(sh), sh
            n_ref += 1
    assert n_ref > 100
    print("connected diagrams, size <= %d, rows <= %d : %d" % (SIZE_CAP, ROW_CAP, len(shapes)))

    # ------------------------------------------------ the locus, as T-collisions
    ids = defaultdict(set)              # unordered pair -> {(r, a)}
    for r in R_RANGE:
        for a in A_RANGE:
            bk = defaultdict(list)
            for sh in shapes:
                bk[key(T(sh, r, a))].append(sh)
            for mem in bk.values():
                for i in range(len(mem)):
                    for j in range(i + 1, len(mem)):
                        ids[(mem[i], mem[j])].add((r, a))
    print("ratio pairs over (r, a) in [0,%d] x [1,%d]: %d distinct pairs, %d (pair, r, a) identities"
          % (max(R_RANGE), max(A_RANGE), len(ids), sum(len(v) for v in ids.values())))
    assert ids

    # ------------------------------------------------ lem:ratio-row-lengths, cor:double-cap-kills
    mu_differs = 0
    for (X, Y), rav in ids.items():
        assert X != Y
        assert sorted(rows(X)) == sorted(rows(Y)), ("lem:ratio-row-lengths", X, Y)
        assert len(X[0]) == len(Y[0])
        mu_differs += X[1] != Y[1]
        by_r = defaultdict(int)
        for r, a in rav:
            by_r[r] += 1
        assert all(c == 1 for c in by_r.values()), ("cor:double-cap-kills", X, Y, sorted(rav))
        if X[1] == Y[1]:
            assert len(rav) == 1, ("cor:unique-ratio", X, Y, sorted(rav))
    print("every ratio pair has equal row-length multisets and row counts; %d have different inner boundaries"
          % mu_differs)
    print("no pair carries two identities at one base r; no common-mu pair carries two identities at all")

    # ------------------------------------------------ prop:top-terminal
    small = gen_shapes(TOP_SIZE_CAP, TOP_ROW_CAP)
    bk = defaultdict(list)
    for sh in small:
        bk[(sh[1], len(sh[0]))].append(sh)
    n_top = 0
    for mem in bk.values():
        for i in range(len(mem)):
            for j in range(len(mem)):
                A, B = mem[i], mem[j]
                if A[0][0] < B[0][0]:
                    dA, dB = grid(A)[1], grid(B)[1]
                    assert dB[-1] > dA[-1] and dB[-1] > max(dA), ("unique largest shift", A, B)
                    theta = B[0][0] - A[0][0]
                    assert [x for x in dB[1:]] == [x + theta for x in dA[1:]], ("shift by theta", A, B)
                    CB = cofvec(B)
                    assert CB[-1], ("terminal cofactor nonzero", B)
                    assert dB[-1] not in dA                      # so the defect there is C_n(B) alone
                    n_top += 1
    print("prop:top-terminal: %d ordered pairs with common mu, equal row count, different top rows" % n_top)
    assert n_top > 0

    # ------------------------------------------------ the common-mu ratio pairs
    n_pairs = 0
    top_differs = 0
    by_v = defaultdict(int)
    pairs = []
    for (X, Y), rav in sorted(ids.items()):
        if X[1] != Y[1]:
            continue
        (r, a), = rav
        # cor:cap-fixing
        assert X[0][0] == Y[0][0], ("cor:cap-fixing", X, Y)
        # eq:bounded-generator
        AX, dX = grid(X)
        AY, dY = grid(Y)
        assert dX == dY
        D = max(dX)
        for sh in (X, Y):
            for f in cofvec(sh):
                for m in f:
                    assert all(e <= D for e in m), ("eq:bounded-generator", sh, m)
        P = Pair(X, Y)
        G = P.G
        supp = [j for j in range(P.n + 1) if G[j]]
        e = max(P.d[j] for j in supp)
        assert e + r + a <= D, ("thm:terminal-gap", X, Y, e, r, a, D)
        assert e < D
        pairs.append((P, r, a))
        by_v[P.v] += 1
        n_pairs += 1
    print("common-mu ratio pairs: %d, by first changed row %s" % (n_pairs, dict(sorted(by_v.items()))))
    assert n_pairs > 0

    # ------------------------------------------------ thm:ratio-rigidity and the gap formulas
    for nm, om in WEIGHTS.items():
        for x in range(1, 15):
            for y in range(1, 15):
                assert om(x + y) > om(x) + om(y), ("superadditivity", nm, x, y)
    n_checked = 0
    for P, r, a in pairs:
        n, d, v, G = P.n, P.d, P.v, P.G
        gamma = a if r == 0 else r
        # the virtual-row paragraphs
        if r > 0:
            for nm, om in WEIGHTS.items():
                for j in range(n + 1):
                    Q = sub(h(r + a + d[j]), pmul(h(a), h(r + d[j])))
                    w, fc = init_face(Q, om)
                    assert fc == {tuple(sorted((a, r + d[j]), reverse=True)): -1}, ("initial form of Q_j", nm, j)
                    assert w == om(a) + om(r + d[j])
        for nm, om in WEIGHTS.items():
            al = P.alpha(om)
            pos = [j for j in range(1, n + 1) if al[j] is not None]
            m_plus = min(al[j] for j in pos)
            # F_{-1}(j) = alpha_j + omega(d_j + gamma) - omega(d_j) on the support
            Fv = {j: al[j] + om(d[j] + gamma) - om(d[j]) for j in range(n + 1) if al[j] is not None}
            assert argmin(Fv)[1] == [0, 1], ("eq:virtual-edge", P.X, P.Y, nm, argmin(Fv))
            for i in range(v):
                assert argmin(P.F(i, om, al))[1] == [i + 1, i + 2], ("eq:full-edge-chain", P.X, P.Y, nm, i)
            T0 = [j for j in pos if al[j] == m_plus]
            assert T0 == [1, 2], ("eq:universal-floor-set", P.X, P.Y, nm)
            assert al[0] is not None and al[0] > m_plus, ("eq:automatic-floor-antecedent", P.X, P.Y, nm)
            gap = om(d[1] + gamma) - om(d[1]) - om(gamma) + om(0)
            assert al[0] - al[1] == gap > 0, ("eq:virtual-gap-general", P.X, P.Y, nm)
            if nm == "square":
                assert al[0] - m_plus == 2 * gamma * d[1], ("eq:square-gap", P.X, P.Y)
            for j in range(1, v + 2):
                assert al[j] is not None
            assert al[1] == al[2]
            for j in range(2, v + 1):
                assert al[j] < al[j + 1]
            for j in range(v + 2, n + 1):
                if al[j] is not None:
                    assert al[j] > al[v + 1]
            n_checked += 1
            if nm == "square":
                # eq:floor-input and G_0 != 0 (cor:floor-supplies)
                assert G[0]
                for j in range(n + 1):
                    if G[j]:
                        assert al[0] - al[j] <= 2 * gamma * d[j], ("eq:floor-input", P.X, P.Y, j)
                # lem:laplace-equivalence and thm:floor
                J0 = {}
                for j in T0:
                    J0 = padd(J0, pmul(h(d[j]), init_face(G[j], om)[1]))
                assert not J0 and al[0] > m_plus
                leftmost = min(d[j] for j in pos)
                assert leftmost == d[1] and d[1] in [d[j] for j in T0], ("thm:floor", P.X, P.Y)
                # the two-cap relations of the paper: cap-shift identity on this defect
                for k in (r + 1, r + 2, r + 3):
                    Phi = lambda j, k=k: wpoly(G[j], SQ) + (k + d[j]) ** 2 if G[j] else None
                    for j in range(n + 1):
                        if Phi(j) is not None:
                            assert Phi(j) == al[j] + 2 * k * d[j] + k * k, ("eq:Phi", P.X, P.Y, j, k)
    print("thm:ratio-rigidity, eq:virtual-gap-general, thm:floor, cor:floor-supplies: %d (pair, weight) checks"
          % n_checked)

    # ------------------------------------------------ lem:laplace-equivalence on every cap-fixed pair
    cap_fixed = 0
    both = [0, 0]
    bkc = defaultdict(list)
    for sh in gen_shapes(10, 5):
        bkc[(sh[1], sh[0][0], len(sh[0]))].append(sh)
    for mem in bkc.values():
        for i in range(len(mem)):
            for j in range(i + 1, len(mem)):
                P = Pair(mem[i], mem[j])
                al = P.alpha(SQ)
                pos = [k for k in range(1, P.n + 1) if al[k] is not None]
                m_plus = min(al[k] for k in pos)
                if al[0] is not None:
                    assert al[0] >= m_plus, ("lem:laplace-equivalence", mem[i], mem[j])
                J0 = {}
                for k in pos:
                    if al[k] == m_plus:
                        J0 = padd(J0, pmul(h(P.d[k]), init_face(P.G[k], SQ)[1]))
                strictly = al[0] is None or al[0] > m_plus
                assert (not J0) == strictly, ("eq:J0-equivalence", mem[i], mem[j])
                both[strictly] += 1
                cap_fixed += 1
    print("lem:laplace-equivalence: %d cap-fixed pairs, J_0 = 0 on %d (alpha_0 > m_+) and J_0 != 0 on %d"
          % (cap_fixed, both[1], both[0]))
    assert both[0] > 0 and both[1] > 0

    # ------------------------------------------------ thm:two-cap: both hypotheses load-bearing
    # A formal vector G on the grid {0,1,2,3} satisfying two ratio caps exists; it must violate a
    # hypothesis of the theorem.  Build it as the generalized cross product of the three relation vectors.
    def cross(vecs, ncols):
        out = []
        for c in range(ncols):
            cols = [t for t in range(ncols) if t != c]
            minor = [[row[t] for t in cols] for row in vecs]
            f = poly_det(minor)
            out.append(f if c % 2 == 0 else neg(f))
        return out

    d = [0, 1, 2, 3]
    witnesses = 0
    for (r, a, b) in ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 1, 2), (1, 1, 3), (2, 1, 2), (2, 2, 3)):
        gamma = a if r == 0 else r
        rel0 = [h(dj) for dj in d]
        rel_a = [sub(h(r + a + dj), pmul(h(a), h(r + dj))) for dj in d]
        rel_b = [sub(h(r + b + dj), pmul(h(b), h(r + dj))) for dj in d]
        G = cross([rel0, rel_a, rel_b], 4)
        for rel in (rel0, rel_a, rel_b):                       # G is orthogonal to all three
            tot = {}
            for dj, g, c in zip(d, G, rel):
                tot = padd(tot, pmul(g, c))
            assert not tot
        # ... so both caps hold: P_{r+k}(G) = h_k P_r(G) for k = a, b, and P_0(G) = 0
        for k in (a, b):
            lhs = {}
            rhs_inner = {}
            for dj, g in zip(d, G):
                lhs = padd(lhs, pmul(g, h(r + k + dj)))
                rhs_inner = padd(rhs_inner, pmul(g, h(r + dj)))
            assert lhs == pmul(h(k), rhs_inner)
        if not G[0] or not any(G):
            continue
        al = [None if not g else wpoly(g, SQ) + dj * dj for g, dj in zip(G, d)]
        violated = [j for j in range(4) if al[j] is not None and al[0] - al[j] > 2 * gamma * d[j]]
        assert violated, ("a two-cap formal vector must violate eq:floor-input", r, a, b, al)
        witnesses += 1
    assert witnesses > 0
    print("thm:two-cap: %d formal vectors with G_0 != 0 satisfy two ratio caps and violate eq:floor-input"
          % witnesses)
    # the other hypothesis: G_0 = 0 with both caps and the floor input trivially true
    r, a, b = 0, 1, 2
    d5 = [0, 1, 2, 3, 4]
    rel0 = [h(dj) for dj in d5]
    rel_a = [h(a + dj) for dj in d5]
    rel_b = [h(b + dj) for dj in d5]
    # G supported off column 0: kernel of the three relations on columns 1..4
    G = [{}] + cross([[rel0[j] for j in range(1, 5)], [rel_a[j] for j in range(1, 5)],
                      [rel_b[j] for j in range(1, 5)]], 4)
    assert any(G) and not G[0]
    for k in (0, a, b):
        tot = {}
        for dj, g in zip(d5, G):
            tot = padd(tot, pmul(g, h(k + dj)))
        assert not tot
    print("thm:two-cap: with G_0 = 0 two caps coexist on a nonzero formal vector, so G_0 != 0 is load-bearing")
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
