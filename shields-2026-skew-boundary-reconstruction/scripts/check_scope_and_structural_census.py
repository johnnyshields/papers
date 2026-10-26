r"""Paper sections `sec:scope` (Scope and remaining questions), `app:structural` (Structural consequences of
the Strict-Monge geometry) and the staircase identity of `sec:application`.  Target labels:
`prop:elbow`, `subsec:weight-scope`, `eq:radix-weight`, `subsec:floor-margin`,
`subsec:fingerprint-not-classification`, `prop:caterpillar`, `thm:first-split-majorization`,
`rem:higher-strata`, `prop:cap-fixed-comparability`, `rem:which-floor`, `thm:abstract-monge`,
`rem:abstract-family`.

  * prop:elbow         the cross-product vector satisfies both relations, at every (x, y, z, r, a) in a
                       box, with the printed numbers at (1, 2, 3, 1, 1) and both sides of x = 0;
  * subsec:weight-scope the printed collision, the weights 686 and 2415, injectivity of the radix weight
                       on the union of ALL monomials of ALL capped cofactors of n-row diagrams at B = n+1
                       and its failure at B = n, and the three-term Plucker relation of the staircase
                       minors with the three products pairwise distinct;
  * subsec:floor-margin and subsec:fingerprint-not-classification the explicit defect coordinates, the
                       row-length multiset, the grid, the actions and the k-fold dilation;
  * prop:caterpillar   M_ik M_jl = M_il M_jk as monomials and the weight strict inequality, on every
                       feasible staircase in a box, at four weights;
  * thm:first-split-majorization over every cap-fixed pair with equal row-length multisets, in the strict
                       dominance order, with the peel-multiset bookkeeping of the proof;
  * prop:cap-fixed-comparability over every single non-top transfer pair, at every cap-grid shift;
  * rem:higher-strata, and the moving-cap witness: the printed polynomials and the incomparability;
  * rem:which-floor    the two floor functionals on every cap-fixed pair;
  * thm:abstract-monge a strictly Monge cost with integer coefficients over Z[t], NOT the Jacobi-Trudi
                       entries, with every clause of the theorem asserted wherever its hypotheses hold, and
                       rem:abstract-family: the paper's scaled-row pair has no split.

Exact integer / `Fraction` arithmetic throughout.
"""
import itertools
import sys
from collections import Counter, defaultdict

from _census_common import (
    CU, RG, RX, SQ, WEIGHTS, Pair, admissible, argmin, cofvec, det_dp, det_h, extend, gen_shapes, grid, h,
    init_face, neg, padd, pmul, rows, sub, wmon, wpoly, Pk, connected,
)

# ---------------------------------------------------------------- helpers


def dominates(a, b):
    """a majorizes b: equal sums, every partial sum of the decreasing arrangement at least as large."""
    a, b = sorted(a, reverse=True), sorted(b, reverse=True)
    n = max(len(a), len(b))
    a, b = a + [0] * (n - len(a)), b + [0] * (n - len(b))
    if sum(a) != sum(b):
        return False
    sa = sb = 0
    for x, y in zip(a, b):
        sa += x
        sb += y
        if sa < sb:
            return False
    return True


def peel(A, d, j):
    n = len(A)
    return [d[i if i < j else i + 1] - A[i] for i in range(n)]


def cross3(u, w):
    """Cross product of two vectors of three h-polynomials."""
    def m(a, b):
        return pmul(a, b)
    return [sub(m(u[1], w[2]), m(u[2], w[1])), sub(m(u[2], w[0]), m(u[0], w[2])),
            sub(m(u[0], w[1]), m(u[1], w[0]))]


def main():
    for nm, om in WEIGHTS.items():
        assert admissible(om), nm

    # ------------------------------------------------------------ prop:elbow
    n_cone = 0
    for x, y, z in itertools.combinations(range(0, 7), 3):
        for r in range(0, 5):
            for a in range(1, 5):
                Y = {d: sub(h(r + a + d), pmul(h(a), h(r + d))) for d in (x, y, z)}
                G = cross3([h(x), h(y), h(z)], [Y[x], Y[y], Y[z]])
                Gd = dict(zip((x, y, z), G))
                P0 = {}
                ratio = {}
                for d in (x, y, z):
                    P0 = padd(P0, pmul(h(d), Gd[d]))
                    ratio = padd(ratio, pmul(Y[d], Gd[d]))
                assert not P0 and not ratio, ("both relations", x, y, z, r, a)
                lhs = Pk(list(Gd.values()), list(Gd.keys()), r + a)
                assert lhs == pmul(h(a), Pk(list(Gd.values()), list(Gd.keys()), r)), ("ratio identity", x, y, z, r, a)
                if not all(G):
                    continue
                al = {d: wpoly(Gd[d], SQ) + d * d for d in (x, y, z)}
                gamma = a if r == 0 else r
                assert al[y] == al[z] and al[x] - al[y] == 2 * gamma * (y - x), (x, y, z, r, a, al)
                m_plus = min(al[y], al[z])
                T0 = [d for d in (y, z) if al[d] == m_plus]
                if x > 0:
                    leftmost = x                      # the leftmost positive supported shift
                    assert leftmost not in T0 and al[x] > m_plus, ("failure of the conclusion", x, y, z, r, a)
                else:
                    assert min(d for d in (y, z) if Gd[d]) == y and y in T0 and T0 == [y, z]
                n_cone += 1
    # the printed instance
    x, y, z, r, a = 1, 2, 3, 1, 1
    Y = {d: sub(h(r + a + d), pmul(h(a), h(r + d))) for d in (x, y, z)}
    G = dict(zip((x, y, z), cross3([h(x), h(y), h(z)], [Y[x], Y[y], Y[z]])))
    assert tuple(wpoly(G[d], SQ) + d * d for d in (x, y, z)) == (20, 18, 18)
    # J_0 = 0 there: the weight-m_+ part of P_0 over T_0^+ vanishes
    J0 = {}
    for d in (y, z):
        J0 = padd(J0, pmul(h(d), init_face(G[d], SQ)[1]))
    assert not J0
    print("prop:elbow: %d cone points with both relations exact, alpha_y = alpha_z, the square gap, and the" % n_cone)
    print("    failure of the conclusion for x > 0 and its validity at x = 0; printed (20, 18, 18) and J_0 = 0")

    # ------------------------------------------------------------ subsec:weight-scope
    G0 = {(3, 3): -1, (4, 1, 1): 1}
    assert wmon((3, 3), SQ) == wmon((4, 1, 1), SQ) == 18
    q_image = sum(c * 1 for m, c in G0.items())
    assert q_image == 0                                      # h_j -> q^{j^2}: both monomials map to q^18
    om7 = lambda k: 0 if k == 0 else 7 ** k
    assert (wmon((3, 3), om7), wmon((4, 1, 1), om7)) == (686, 2415)
    for B in (3, 4, 5, 7, 11):
        o = lambda k, B=B: 0 if k == 0 else B ** k
        inc = [o(k) - o(k - 1) for k in range(1, 9)]
        assert inc[0] == B and all(inc[k] == B ** (k + 1) - B ** k for k in range(1, 8)) and admissible(o)
    assert not admissible(lambda k: 0 if k == 0 else 2 ** k)
    n_mono = 0
    for n in (2, 3, 4, 5):
        mons = set()
        for sh in gen_shapes(10 if n <= 4 else 9, n):
            if len(sh[0]) != n:
                continue
            for f in cofvec(sh):
                for m in f:
                    assert len(m) <= n and all(e <= max(grid(sh)[1]) for e in m), (sh, m)
                    mons.add(m)
        B = n + 1
        o = lambda k, B=B: 0 if k == 0 else B ** k
        w = defaultdict(set)
        for m in mons:
            w[wmon(m, o)].add(m)
        assert all(len(v) == 1 for v in w.values()), ("radix injective on cofactor monomials", n)
        # exponent of a generator h_j in a monomial is at most n, which is what the base must exceed
        assert max(c for m in mons for c in Counter(m).values()) <= n
        # the square weight does collide on these very monomials
        ws = defaultdict(set)
        for m in mons:
            ws[wmon(m, SQ)].add(m)
        assert any(len(v) > 1 for v in ws.values()), n
        # at B = n an exponent equal to n carries: n copies of h_1 weigh as one h_2
        o2 = lambda k, B=n: 0 if k == 0 else B ** k
        assert wmon((1,) * n, o2) == wmon((2,), o2)
        n_mono += len(mons)
    print("subsec:weight-scope: collision h_3^2 / h_4 h_1^2 at square weight 18, radix weights 686 and 2415;")
    print("    radix B = n+1 injective on all %d monomials of the capped cofactors of n-row diagrams (n = 2..5)," % n_mono)
    print("    square weight collides on them; B = 2 inadmissible; base-n carry shown")

    # the Plucker relation of the staircase minors and caterpillar identity
    n_cat = n_pl = 0
    distinct_products = 0
    for m in (2, 3, 4):
        for A in itertools.combinations(range(0, 8), m):
            for d in itertools.combinations(range(0, 10), m + 2):
                if not all(A[t] <= d[t] for t in range(m)):
                    continue
                cols = range(m + 2)
                Pm = {}
                for i, j in itertools.combinations(cols, 2):
                    cs = [c for c in cols if c not in (i, j)]
                    Pm[(i, j)] = det_dp([[d[c] - A[r] for c in cs] for r in range(m)])
                    assert Pm[(i, j)], ("every maximal minor nonzero under A_t <= d_t", A, d, i, j)
                for i, j, k, l in itertools.combinations(cols, 4):
                    for nm, om in WEIGHTS.items():
                        ini = {p: init_face(Pm[p], om) for p in Pm}
                        mon = {p: next(iter(ini[p][1])) for p in ini}
                        assert all(len(ini[p][1]) == 1 for p in ini)
                        prod = lambda p, q_: tuple(sorted(mon[p] + mon[q_], reverse=True))
                        assert prod((i, k), (j, l)) == prod((i, l), (j, k)), ("monomial identity", nm, A, d, i, j, k, l)
                        w = lambda p: ini[p][0]
                        assert w((i, k)) + w((j, l)) == w((i, l)) + w((j, k)) < w((i, j)) + w((k, l)), \
                            ("weights", nm, A, d, i, j, k, l)
                        n_cat += 1
                    lhs = pmul(Pm[(i, j)], Pm[(k, l)])
                    mid = pmul(Pm[(i, k)], Pm[(j, l)])
                    rhs = pmul(Pm[(i, l)], Pm[(j, k)])
                    assert padd(padd(lhs, neg(mid)), rhs) == {}, ("three-term Plucker relation", A, d, i, j, k, l)
                    n_pl += 1
                    if len({tuple(sorted(f.items())) for f in (lhs, mid, rhs)}) == 3:
                        distinct_products += 1
    assert distinct_products > 0
    # the feasibility hypothesis is needed: strictly increasing A and d alone can kill every minor
    kill = 0
    for A in itertools.combinations(range(0, 12), 3):
        for d in itertools.combinations(range(0, 6), 5):
            if all(A[t] <= d[t] for t in range(3)):
                continue
            for i, j in itertools.combinations(range(5), 2):
                cs = [c for c in range(5) if c not in (i, j)]
                if not det_dp([[d[c] - A[r] for c in cs] for r in range(3)]):
                    kill += 1
                    break
    assert kill > 0
    print("prop:caterpillar: monomial identity and weight inequality on %d (staircase, 4-subset, weight) cases;" % n_cat)
    print("    Plucker relation on %d quadruples, the three products pairwise distinct on %d; the feasibility" % (n_pl, distinct_products))
    print("    hypothesis is necessary (%d infeasible staircases with a vanishing minor)" % kill)

    # ------------------------------------------------------------ subsec:floor-margin, subsec:fingerprint-not-classification
    A_, B_ = ((4, 4, 2), (1, 1, 0)), ((4, 3, 3), (1, 1, 0))
    assert connected(A_) and connected(B_) and sorted(rows(A_)) == sorted(rows(B_)) == [2, 3, 3]
    P = Pair(A_, B_)
    assert P.d == [0, 3, 4, 6]
    want = {1: sub({(5,): 1}, {(4, 1): 1}),
            2: padd(sub({(2, 2): 1}, {(3, 1): 1}), {(4,): 1}),
            3: sub({(1, 1): 1}, {(2,): 2})}
    for j in (1, 2, 3):
        assert P.G[j] == want[j], ("defect coordinate", j)
    G0 = {}
    for j, (c) in ((1, 3), (2, 4), (3, 6)):
        G0 = padd(G0, neg(pmul(h(c), want[j])))
    assert P.G[0] == G0, "G_0 = -h_3 G_1 - h_4 G_2 - h_6 G_3"
    assert P.alpha(SQ) == [24, 26, 24, 38]
    for k in range(1, 9):
        mk = (3 * k - 2, 2 * k - 1, 0)
        Ak = ((6 * k - 2, 5 * k - 1, 2 * k), mk)
        Bk = ((6 * k - 2, 4 * k - 1, 3 * k), mk)
        assert connected(Ak) and connected(Bk) and sorted(rows(Ak)) == sorted(rows(Bk))
        Pk_ = Pair(Ak, Bk)
        assert Pk_.d == [0, 3 * k, 4 * k, 6 * k]
        assert [grid(Ak)[0], grid(Bk)[0]] == [[0, k, 4 * k], [0, 2 * k, 3 * k]]
        for j in range(4):
            dil = {tuple(sorted((k * e for e in m), reverse=True)): c for m, c in P.G[j].items()}
            assert Pk_.G[j] == dil, ("defect is the dilation h_j -> h_{kj}", k, j)
        al = Pk_.alpha(SQ)
        assert al == [k * k * c for c in (24, 26, 24, 38)]
        m_plus = min(al[1:])
        assert al[0] == m_plus and [Pk_.d[j] for j in range(1, 4) if al[j] == m_plus] == [4 * k]
        assert min(Pk_.d[j] for j in range(1, 4) if Pk_.G[j]) == 3 * k
        assert al[1] - m_plus == 2 * k * k                       # the leftmost positive action exceeds the floor by 2k^2
    X_, Y_ = ((7, 5, 4), (4, 2, 0)), ((7, 6, 3), (4, 2, 0))
    PF = Pair(X_, Y_)
    assert PF.d == [0, 3, 6, 9] and sorted(rows(X_)) == sorted(rows(Y_))
    assert PF.alpha(SQ) == [52, 46, 46, None]
    assert PF.v == 1 and 52 > 46
    assert sub(cofvec(X_)[0], cofvec(Y_)[0]) == {(7, 3): 1, (6, 4): -1}
    for nm, om in WEIGHTS.items():
        al = PF.alpha(om)
        mp = min(al[1:3])
        assert al[0] > mp and argmin(PF.F(0, om, al))[1] == [1, 2]
    print("subsec:floor-margin: explicit G_0..G_3, alpha = (24,26,24,38), the dilation h_j -> h_{kj} for k <= 8,")
    print("    alpha = k^2 (24,26,24,38), leftmost positive action above the floor by 2k^2; fingerprint pair")
    print("    alpha = (52,46,46,inf) with the antecedent and the chain at four weights, s_X - s_Y = h_3h_7 - h_4h_6")

    # ------------------------------------------------------------ thm:first-split-majorization
    SIZE, ROWS = 12, 6
    shapes = gen_shapes(SIZE, ROWS)
    bk = defaultdict(list)
    for s in shapes:
        bk[(s[1], s[0][0], len(s[0]), tuple(sorted(rows(s))))].append(s)
    n_maj = 0
    for mem in bk.values():
        for i in range(len(mem)):
            for j in range(i + 1, len(mem)):
                X, Y = mem[i], mem[j]
                AX, d = grid(X)
                AY, _ = grid(Y)
                n = len(AX)
                v = next(t for t in range(n) if AX[t] != AY[t])
                q = v + 1
                if AX[v] < AY[v]:
                    X, Y, AX, AY = Y, X, AY, AX
                # peel at column 0 is the row-length multiset; one entry changes per step
                assert sorted(peel(AX, d, 0)) == sorted(rows(X))
                for t in range(n):                       # passing from column t to t + 1 lowers row t only
                    a0, a1 = peel(AX, d, t), peel(AX, d, t + 1)
                    assert [i for i in range(n) if a0[i] != a1[i]] == [t] and a0[t] - a1[t] == d[t + 1] - d[t]
                cX, cY = Counter(peel(AX, d, v)), Counter(peel(AY, d, v))
                assert cX == cY, ("peel multisets coincide at column v", X, Y)
                x_, y_ = d[v + 1] - AX[v], d[v + 1] - AY[v]
                assert y_ > x_ and d[v] - AX[v] >= 0
                Delta = d[v + 1] - d[v]
                piA, piB = peel(AX, d, q), peel(AY, d, q)
                W = Counter(peel(AX, d, v))
                W[x_] -= 1
                W[y_] -= 1
                assert all(c >= 0 for c in W.values())
                assert Counter(piA) == W + Counter([y_, x_ - Delta]) and Counter(piB) == W + Counter([x_, y_ - Delta])
                assert sum(piA) == sum(piB) and len(piA) == len(piB)
                assert dominates(piA, piB) and not dominates(piB, piA), ("strict majorization", X, Y)
                n_maj += 1
    print("thm:first-split-majorization: %d cap-fixed pairs with equal multisets (size <= %d, rows <= %d),"
          % (n_maj, SIZE, ROWS))
    print("    peel multisets coincide at column v, split as printed, strict dominance in the stated direction")

    # ------------------------------------------------------------ prop:cap-fixed-comparability
    sh2 = gen_shapes(13, 6)
    byk = defaultdict(list)
    for s in sh2:
        byk[(s[1], s[0][0], len(s[0]))].append(s)
    n_cmp = n_incomparable_other = 0
    for mem in byk.values():
        for i in range(len(mem)):
            for j in range(i + 1, len(mem)):
                X, Y = mem[i], mem[j]
                dl = [t for t in range(len(X[0])) if X[0][t] != Y[0][t]]
                if len(dl) != 2 or dl[0] < 1:
                    continue
                r_, s_ = dl
                th = X[0][r_] - Y[0][r_]
                if th == 0 or X[0][s_] - Y[0][s_] != -th:
                    continue
                AX, d = grid(X)
                AY, dy = grid(Y)
                assert d == dy
                for j_ in range(len(AX) + 1):
                    assert dominates(peel(AX, d, j_), peel(AY, d, j_)) or dominates(peel(AY, d, j_), peel(AX, d, j_)), \
                        ("comparable at every shift", X, Y, j_)
                    # and the transfer changes exactly two entries
                    diff = [t for t in range(len(AX)) if peel(AX, d, j_)[t] != peel(AY, d, j_)[t]]
                    assert len(diff) <= 2
                n_cmp += 1
    # the moving-cap witness: not comparable
    Aw, Bw = ((6, 6, 4, 1), (2, 0, 0, 0)), ((8, 4, 4, 1), (2, 0, 0, 0))
    assert connected(Aw) and connected(Bw) and sum(rows(Aw)) == sum(rows(Bw)) == 15
    Aa, da = grid(Aw)
    Ab, db = grid(Bw)
    assert 9 in da and 9 in db
    CA9, CB9 = cofvec(Aw)[da.index(9)], cofvec(Bw)[db.index(9)]
    assert CA9 == sub({(3, 3): 1}, {(6,): 1}), CA9
    assert CB9 == padd(padd({(4, 1, 1): 1}, {(5, 1): -2}), {(6,): 1}), CB9
    assert sorted(init_face(CA9, SQ)[1]) == [(3, 3)] and sorted(init_face(CB9, SQ)[1]) == [(4, 1, 1)]
    assert not dominates((3, 3), (4, 1, 1)) and not dominates((4, 1, 1), (3, 3))
    assert wmon((3, 3), SQ) == wmon((4, 1, 1), SQ) and Aw[0][0] != Bw[0][0]
    print("prop:cap-fixed-comparability: %d single non-top transfer pairs, peel multisets comparable at every" % n_cmp)
    print("    shift; moving-cap witness C_9(A) = h_3^2 - h_6, C_9(B) = h_4 h_1^2 - 2 h_5 h_1 + h_6 with (3,3), (4,1,1)")
    print("    incomparable at equal square weight 18")

    # ------------------------------------------------------------ rem:higher-strata
    mu = (12, 10, 6, 6, 4, 0)
    lam = (15, 15, 14, 10, 10, 5)
    kap = (15, 15, 14, 11, 8, 6)
    Xh, Yh = (lam, mu), (kap, mu)
    assert connected(Xh) and connected(Yh) and sorted(rows(Xh)) == sorted(rows(Yh))
    Ph = Pair(Xh, Yh)
    assert Ph.d == [0, 3, 6, 11, 12, 15, 20] and Ph.v == 3
    g6 = Ph.G[6]
    w6 = wpoly(g6, SQ)
    stratum = {m: c for m, c in g6.items() if wmon(m, SQ) == 43}
    assert stratum == {(5, 4, 1, 1): 1, (5, 3, 3): -1}, stratum
    assert not dominates((5, 4, 1, 1), (5, 3, 3, 0)) and not dominates((5, 3, 3, 0), (5, 4, 1, 1))
    assert sum((5, 4, 1, 1)) == sum((5, 3, 3)) == 11
    print("rem:higher-strata: v = 3, grid (0,3,6,11,12,15,20); the square-weight 43 stratum of G_6 is")
    print("    h_1^2 h_4 h_5 - h_3^2 h_5 with incomparable index multisets")

    # ------------------------------------------------------------ rem:which-floor
    n_wf = 0
    for mem in byk.values():
        for i in range(len(mem)):
            for j in range(i + 1, len(mem)):
                Pp = Pair(mem[i], mem[j])
                al = Pp.alpha(SQ)
                pos = [t for t in range(1, Pp.n + 1) if al[t] is not None]
                m_plus = min(al[t] for t in pos)
                if al[0] is None or al[0] > m_plus:
                    continue
                assert al[0] == m_plus, ("lem:laplace-equivalence: alpha_0 >= m_+", mem[i], mem[j])
                for r_ in range(1, 6):
                    Phi = lambda t, r_=r_: al[t] + 2 * r_ * Pp.d[t] + r_ * r_
                    for t in pos:
                        assert Phi(t) - Phi(0) == (al[t] - al[0]) + 2 * r_ * Pp.d[t] > 0
                    n_wf += 1
    print("rem:which-floor: alpha_0 = m_+ branch, Phi_r(d) - Phi_r(0) = (alpha_d - alpha_0) + 2 r d > 0 at every")
    print("    positive shift, %d (pair, r) cases" % n_wf)

    # ------------------------------------------------------------ thm:abstract-monge, rem:abstract-family
    # A strictly Monge cost c(A, d) = (d - A)^2 + (d - A)^3 on the Ferrers support d >= A, with integer
    # unit coefficients u(A, d) = 1 + ((A * d) mod 3) over Z[t]: NOT a Jacobi-Trudi entry.  A polynomial
    # in t is {exponent: coefficient}.
    def c_cost(A, d):
        return (d - A) ** 2 + (d - A) ** 3

    UNIT = [lambda A, d: 1 + ((A * d) % 3)]

    def entry(A, d):
        if d < A:
            return {}
        return {c_cost(A, d): UNIT[0](A, d)}

    def tmul(f, g):
        out = defaultdict(int)
        for a, ca in f.items():
            for b, cb in g.items():
                out[a + b] += ca * cb
        return {k: v for k, v in out.items() if v}

    def tadd(f, g, s=1):
        out = defaultdict(int, f)
        for k, v in g.items():
            out[k] += s * v
        return {k: v for k, v in out.items() if v}

    def tdet(rowsA, cols, As):
        """Determinant of (m(A_i, d_c))_{i, c in cols}: Laplace expansion along the last row, memoized
        on the surviving column set."""
        n = len(As)
        memo = {(): {0: 1}}

        def go(cs):
            if cs in memo:
                return memo[cs]
            r = len(cs)
            out = {}
            for pos, c in enumerate(cs):
                e = entry(As[r - 1], cols[c])
                if not e:
                    continue
                sub_d = go(cs[:pos] + cs[pos + 1:])
                if not sub_d:
                    continue
                out = tadd(out, tmul(sub_d, e), -1 if (r - 1 + pos) % 2 else 1)
            memo[cs] = out
            return out

        return go(tuple(range(n)))

    def nu(f):
        return min(f) if f else None

    def cofs(As, d):
        n = len(As)
        out = []
        for j in range(n + 1):
            cols = [d[c] for c in range(n + 1) if c != j]
            f = tdet(None, cols, As)
            out.append(f if j % 2 == 0 else {k: -v for k, v in f.items()})
        return out

    # the Monge inequality for the cost, on the supported box
    for A, Ap, d, dp in itertools.product(range(0, 8), repeat=4):
        if A < Ap and d < dp and min(d - A, dp - Ap, dp - A, d - Ap) >= 0:
            assert c_cost(A, d) + c_cost(Ap, dp) < c_cost(A, dp) + c_cost(Ap, d)
    n_abs = n_chain = n_split_only = 0
    maxv = 0
    for ufun in (lambda A, d: 1 + ((A * d) % 3), lambda A, d: 1):
        UNIT[0] = ufun
        for n in (3, 4, 5):
            top = {3: 9, 4: 8, 5: 8}[n]
            for d in itertools.combinations(range(0, top), n + 1):
                # one grid in two: the common first parameter and a shared prefix
                seqs = [As for As in itertools.combinations(range(0, top), n) if all(As[t] <= d[t] for t in range(n))]
                cache = {}
                for As in seqs:
                    cache[As] = cofs(list(As), d)
                for As, Bs in itertools.combinations(seqs, 2):
                    if As[0] != Bs[0]:
                        continue
                    v = next(t for t in range(n) if As[t] != Bs[t])
                    if v < 1:
                        continue
                    CA, CB = cache[As], cache[Bs]
                    sA = [nu(CA[j]) + c_cost(As[0], d[j]) if d[j] >= As[0] else None for j in range(n + 1)]
                    sB = [nu(CB[j]) + c_cost(Bs[0], d[j]) if d[j] >= Bs[0] else None for j in range(n + 1)]
                    if None in sA or None in sB or any(f == {} for f in CA + CB):
                        continue
                    if sA[0] != sB[0]:
                        continue
                    G = [tadd(CA[j], CB[j], -1) for j in range(n + 1)]
                    alpha = [None if not G[j] else nu(G[j]) + c_cost(As[0], d[j]) for j in range(n + 1)]
                    q = v + 1
                    # (i) the first forced split is at column v + 1
                    for j in range(v + 1):
                        assert sA[j] == sB[j], ("(i) synchronized", As, Bs, d, j)
                    assert sA[q] != sB[q], ("(i) split", As, Bs, d)
                    assert alpha[q] is not None and alpha[q] == min(sA[q], sB[q])
                    n_abs += 1
                    pos = [j for j in range(1, n + 1) if alpha[j] is not None]
                    m_plus = min(alpha[j] for j in pos)
                    # (ii) no-backflow in every common-prefix row
                    mins = []
                    ok = True
                    for i in range(v):
                        F = {}
                        for j in range(n + 1):
                            if alpha[j] is None or d[j] < As[i]:
                                continue
                            F[j] = alpha[j] + c_cost(As[i], d[j]) - c_cost(As[0], d[j])
                        mn = min(F.values())
                        M = sorted(j for j in F if F[j] == mn)
                        assert len(M) >= 2, ("tropical balancing", As, Bs, d, i, M)
                        for l in range(q + 1, n + 1):
                            if l in F:
                                assert F[l] > F[q], ("(ii) no-backflow", As, Bs, d, i, l)
                        mins.append(M)
                    for i in range(v - 1):
                        assert max(mins[i + 1]) > max(mins[i]) and min(mins[i + 1]) >= max(mins[i]), \
                            ("(iii) marching and interlacing", As, Bs, d, i)
                    if alpha[0] is None or alpha[0] > m_plus:
                        for i in range(v):
                            assert mins[i] == [i + 1, i + 2], ("(iv) adjacent chain", As, Bs, d, i, mins[i])
                        n_chain += 1
                        maxv = max(maxv, v)
                    else:
                        n_split_only += 1
    assert n_abs > 0 and n_chain > 0
    print("thm:abstract-monge: Z[t] with cost (d-A)^2 + (d-A)^3, unit coefficients 1 + (A d mod 3) and all-ones: %d pairs with"
          % n_abs)
    print("    sigma_0 = sigma_0' satisfy (i)-(iii); %d of them have alpha_0 > m_+ and satisfy (iv) (first changed"
          % n_chain)
    print("    row up to %d); %d are on the other branch" % (maxv, n_split_only))
    assert maxv >= 2

    # rem:abstract-family: the paper's scaled-row pair has no split, and does not come from one family
    def tmat(M):
        n = len(M)
        out = []
        for j in range(n + 1):
            cols = [c for c in range(n + 1) if c != j]
            tot = {}
            for perm in itertools.permutations(range(n)):
                term = {0: 1}
                for i, p in enumerate(perm):
                    term = tmul(term, M[i][cols[p]])
                    if not term:
                        break
                if not term:
                    continue
                inv = sum(perm[a] > perm[b] for a in range(n) for b in range(a + 1, n))
                tot = tadd(tot, term, -1 if inv % 2 else 1)
            out.append(tot if j % 2 == 0 else {k: -v for k, v in tot.items()})
        return out

    M = [[{0: 1}, {0: 1}, {0: 1}], [{3: 1}, {2: 1}, {1: 1}]]
    Nn = [[{0: 1}, {0: 1}, {0: 1}], [{3: 2}, {2: 2}, {1: 2}]]
    CM, CN = tmat(M), tmat(Nn)
    assert all(CN[j] == {k: 2 * v for k, v in CM[j].items()} for j in range(3)), "C(N) = 2 C(M)"
    assert all(nu(CN[j]) == nu(CM[j]) for j in range(3)), "equal valuations, so no split anywhere"
    # valuations of the entries: strictly Monge, identical profiles in the second row
    val = [[0, 0, 0], [3, 2, 1]]
    for (r1, r2) in ((0, 1),):
        for c1, c2 in ((0, 1), (0, 2), (1, 2)):
            assert val[r1][c1] + val[r2][c2] < val[r1][c2] + val[r2][c1]
    # one family cannot supply both second rows: equal entries force equal parameters, so a family with
    # two different second rows needs two different row parameters, whose valuation profile must then
    # differ for the 2 x 2 difference to be nonzero
    prof_M, prof_N = [3, 2, 1], [3, 2, 1]
    assert prof_M == prof_N
    for c1, c2 in ((0, 1), (0, 2), (1, 2)):
        assert (val[0][c1] + val[1][c2]) - (val[0][c2] + val[1][c1]) != 0          # distinct rows: Monge is strict
        # the same two rows of equal valuation profile have zero defining difference
        assert (prof_M[c1] + prof_N[c2]) - (prof_M[c2] + prof_N[c1]) == 0
    print("rem:abstract-family: C(N) = 2 C(M), equal valuations at every column (no split), and the two second rows")
    print("    share the valuation profile (3,2,1), so the strict Monge difference between them is zero")
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
