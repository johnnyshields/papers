r"""Paper sections `sec:coordinates` (Capped cofactors and admissible convex weights) and
`sec:reconstruction` (Reconstruction from two boundary observations).  Target labels:
`eq:Pk-is-capped`, `lem:extension-cofactors`, `eq:iterated-cap`, `eq:ratio-identity`,
`lem:cofactor-factorization`, `lem:top-row-cofactor`, `lem:two-cofactor-reconstruction`,
`thm:boundary-reconstruction`, `cor:two-positive-extensions`, `rem:one-extension-insufficient`,
`def:reversal`, `subsec:intro-main`.

Five exhaustive censuses over connected skew diagrams, every object rebuilt from the definitions by
`_census_common` (cofactors by Laplace expansion of the capped matrix; skew Schur functions by the
Jacobi-Trudi determinant of `skew_core`, a second expansion that shares nothing with it).

  (1) the northeast extension: the cap grid and cofactor vector of X.(k), P_k(C(X)) = s_{X.(k)},
      the iterated-cap identity, and that the ratio quantity
      T(X, r, a) = P_{r+a}(C(X)) - h_a P_r(C(X)) IS, up to sign, the skew Schur function of
      (X.(r)).(a) for r > 0 and of X.(a) for r = 0 -- which is what makes a ratio identity a
      statement about diagrams, and what the ratio-locus census enumerates by;
  (2) lem:cofactor-factorization on EVERY skew presentation, connected or not: the exact support
      criterion, nu^(j) a partition inside lambda wherever it holds, C_j = (-1)^j s_{lambda/nu^(j)},
      C_n != 0 iff connected, C_1 = -s_{Xbar};
  (3) the reconstruction theorem as an ALGORITHM: the prefix-residual induction of
      lem:two-cofactor-reconstruction is executed on the observed polynomials alone (never on the
      diagram), for the first map, the second map and the two-extension corollary, and must return
      the diagram it started from;
  (4) injectivity of the three observation maps over ALL inner boundaries at once, with the degree
      count that identifies which observation is which;
  (5) the explicit witnesses of the front matter and `rem:one-extension-insufficient`.
"""
import itertools
import sys
from collections import defaultdict

from _census_common import (
    SQ, admissible, cofvec, cofvec_reference, connected, deg, det_h, extend, first_row_deleted,
    gen_shapes, grid, h, init_face, neg, padd, pmul, rotate, rows, s_poly, sub, Pk,
)

SIZE_CAP = 10
ROW_CAP = 5
PRES_SIZE = 9          # presentations for (2)
PRES_ROWS = 5


def sp(sh):
    """Skew Schur function by the ordinary Jacobi-Trudi determinant (independent of cofvec)."""
    return s_poly(sh)


def T(sh, r, a):
    vec = cofvec(sh)
    d = grid(sh)[1]
    return sub(Pk(vec, d, r + a), pmul(h(a), Pk(vec, d, r)))


def monomial_div(num, den):
    """The signed multiset num / den as (positive part, negative part), index 0 dropped."""
    from collections import Counter
    cn, cd = Counter(num), Counter(den)
    return sorted((cn - cd).elements()), sorted((cd - cn).elements())


# ------------------------------------------------------------------ (3) the algorithm

def reconstruct(C0, C1):
    """Recover the diagram X (normalized, mu_{n-1} = 0) from C_0(X) and C_1(X) alone, by the
    prefix-residual induction of lem:two-cofactor-reconstruction."""
    w0, f0 = init_face(C0, SQ)
    assert len(f0) == 1
    (Q0, _), = f0.items()
    n = len(Q0)                                  # every rho_i >= 1, so n = number of factors
    A = [0]
    d = [0, deg(C0) - deg(C1)]
    if n == 1:
        pass
    w1, f1 = init_face(C1, SQ)
    assert len(f1) == 1
    (U_prev, _), = f1.items()                    # U_0 = Q_1
    for k in range(1, n):
        def T_j(j):
            cols = list(range(2, k + 1)) + [j]
            return det_h([[d[c] - A[i] for c in cols] for i in range(k)])
        Rk = padd(pmul(T_j(0), C0), pmul(T_j(1), C1))
        assert Rk, ("R_k must be nonzero", k)
        wk, fk = init_face(Rk, SQ)
        assert len(fk) == 1, ("R_k initial monomial unique", k)
        (U_k, _), = fk.items()
        pos, negm = monomial_div(U_k, U_prev)
        assert len(negm) == 1 and len(pos) in (1, 2), (k, pos, negm)
        rho_k = negm[0]
        z_k = min(pos) if len(pos) == 2 else 0
        u_k = max(pos)
        assert u_k > rho_k > z_k >= 0
        A_k = d[k] - z_k
        d_next = A_k + rho_k
        assert u_k == d_next - A[k - 1], ("u_k", k)
        A.append(A_k)
        d.append(d_next)
        U_prev = U_k
    L = d[n] - n + 1
    lam = tuple(L + i - A[i] for i in range(n))
    mu = tuple(L + i - d[i + 1] for i in range(n))
    return lam, mu


def main():
    assert admissible(SQ)

    shapes = gen_shapes(SIZE_CAP, ROW_CAP)
    n_ref = 0
    for sh in shapes:
        if len(sh[0]) <= 5 and sum(rows(sh)) <= 9:
            assert cofvec(sh) == cofvec_reference(sh), sh
            n_ref += 1
    assert n_ref > 100
    print("connected diagrams, size <= %d, rows <= %d : %d" % (SIZE_CAP, ROW_CAP, len(shapes)))

    # ------------------------------------------------ (1) the northeast extension
    n1 = n_t = 0
    for sh in shapes:
        vec = cofvec(sh)
        A, d = grid(sh)
        n = len(sh[0])
        assert sp(sh) == vec[0]
        for k in (1, 2, 3, 4):
            ex = extend(sh, k)
            assert connected(ex)
            Aex, dex = grid(ex)
            assert dex == [0, k] + [k + x for x in d[1:]], ("lem:extension-cofactors grid", sh, k)
            cex = cofvec(ex)
            assert cex[0] == Pk(vec, d, k), ("lem:extension-cofactors, column 0", sh, k)
            for j in range(n + 1):
                assert cex[j + 1] == neg(vec[j]), ("lem:extension-cofactors", sh, k, j)
            assert Pk(vec, d, k) == sp(ex), ("eq:Pk-is-capped", sh, k)
            n1 += 1
        for r in (1, 2, 3):
            for a in (1, 2, 3):
                lhs = sp(extend(extend(sh, r), a))
                rhs = sub(pmul(h(a), sp(extend(sh, r))), sp(extend(sh, r + a)))
                assert lhs == rhs, ("eq:iterated-cap", sh, r, a)
                assert T(sh, r, a) == neg(lhs), ("T is minus the iterated extension", sh, r, a)
        for a in (1, 2, 3, 4):
            assert T(sh, 0, a) == sp(extend(sh, a)), ("r = 0 reads s_{X.(a)}", sh, a)
            n_t += 1
        assert not Pk(vec, d, 0), ("eq:P0-vanishes", sh)
    print("(1) extension lemma on %d (diagram, k) pairs; T(X, r, a) = skew Schur function of the" % n1)
    print("    extended diagram for r in 0..3, a in 1..4 on every diagram")

    # ------------------------------------------------ (2) lem:cofactor-factorization, all presentations
    pres = []
    for n in range(1, PRES_ROWS + 1):
        for rho in itertools.product(range(1, PRES_SIZE + 1), repeat=n):
            if sum(rho) > PRES_SIZE:
                continue
            # mu_{n-1} = 0; mu and lam = mu + rho both weakly decreasing
            def rec2(i, mu_rev, lam_rev):
                if i < 0:
                    pres.append((tuple(reversed(lam_rev)), tuple(reversed(mu_rev))))
                    return
                lo = mu_rev[-1]
                for m in range(lo, lam_rev[-1] + 1):       # mu_i >= mu_{i+1}, and lam_i >= lam_{i+1}
                    lam_i = m + rho[i]
                    if lam_i >= lam_rev[-1]:
                        rec2(i - 1, mu_rev + [m], lam_rev + [lam_i])
            rec2(n - 2, [0], [rho[n - 1]])
    pres = sorted(set(pres))
    n_nonzero = n_zero = n_conn = 0
    for lam, mu in pres:
        n = len(lam)
        vec = cofvec((lam, mu))
        crit_all = True
        for j in range(n + 1):
            crit = all(lam[i] > mu[i - 1] for i in range(1, j))
            assert bool(vec[j]) == crit, ("support criterion", lam, mu, j)
            if crit:
                nu = (lam[0],) + tuple(mu[i - 1] + 1 for i in range(1, j)) + tuple(mu[j:]) if j >= 1 else tuple(mu)
                assert len(nu) == n
                assert all(nu[t] >= nu[t + 1] for t in range(n - 1)) and all(nu[t] <= lam[t] for t in range(n)), \
                    ("nu^(j) is a partition inside lambda", lam, mu, j, nu)
                s = sp((lam, nu))
                assert vec[j] == (s if j % 2 == 0 else neg(s)), ("eq:cofactor-schur", lam, mu, j)
                n_nonzero += 1
            else:
                n_zero += 1
        isconn = all(lam[i] > mu[i - 1] for i in range(1, n))
        assert bool(vec[n]) == isconn, ("C_n != 0 iff connected", lam, mu)
        n_conn += isconn
        bar = sp((lam[1:], mu[1:])) if n > 1 else {(): 1}
        assert vec[1] == neg(bar), ("lem:top-row-cofactor", lam, mu)
    print("(2) %d skew presentations (%d connected), size <= %d, rows <= %d: %d nonzero cofactors identified"
          % (len(pres), n_conn, PRES_SIZE, PRES_ROWS, n_nonzero))
    print("    as skew Schur functions, %d vanishing cofactors exactly where the prefix criterion fails" % n_zero)
    assert n_zero > 0 and len(pres) > n_conn

    # ------------------------------------------------ (3) reconstruction as an algorithm
    n_alg = n_alg2 = n_alg3 = 0
    for sh in shapes:
        vec = cofvec(sh)
        got = reconstruct(vec[0], vec[1])
        assert got == sh, ("first map, algorithm", sh, got)
        n_alg += 1
    for sh in shapes:
        if sum(rows(sh)) > 8:
            continue
        sX = cofvec(sh)[0]
        for a in (1, 2, 3):
            ex = extend(sh, a)
            sXa = cofvec(ex)[0]
            # the unordered pair {s_X, s_{X.(a)}}: degree says which is which and what a is
            lo, hi = sorted((sX, sXa), key=deg)
            aa = deg(hi) - deg(lo)
            assert aa == a and lo == sX
            Z = reconstruct(hi, neg(lo))                 # Z = X.(a), whose first-row deletion is X
            assert first_row_deleted(Z) == sh, ("second map, algorithm", sh, a, Z)
            assert Z == ex
            n_alg2 += 1
    for sh in shapes:
        if sum(rows(sh)) > 7:
            continue
        for a, b in ((1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (3, 4)):
            Fa, Hb = cofvec(extend(sh, a))[0], cofvec(extend(sh, b))[0]
            for F, Hh in ((Fa, Hb), (Hb, Fa)):               # the pair is unordered
                if deg(F) > deg(Hh):
                    continue
                c = deg(Hh) - deg(F)
                sZ = sub(pmul(h(c), F), Hh)                   # eq:iterated-cap
                Z = reconstruct(sZ, neg(F))                   # s_{Zbar} = s_{X.(a')} = F
                X2 = first_row_deleted(first_row_deleted(Z))
                assert X2 == sh, ("two positive extensions, algorithm", sh, a, b)
                assert rows(Z)[1] == deg(F) - sum(rows(sh)), (sh, a, b)
                n_alg3 += 1
    print("(3) reconstruction algorithm returns the diagram: first map %d, second map %d, two extensions %d"
          % (n_alg, n_alg2, n_alg3))

    # ------------------------------------------------ (4) injectivity over all inner boundaries
    sx, sxbar = {}, {}
    seen1, seen2 = {}, {}
    seen3 = {}
    seen4 = {}
    EXT = 4
    ext_cof = {}
    for sh in shapes:
        s0 = tuple(sorted(cofvec(sh)[0].items()))
        sbar = tuple(sorted(sub({}, cofvec(sh)[1]).items()))
        k1 = (s0, sbar)
        assert seen1.setdefault(k1, sh) == sh, ("X -> (s_X, s_Xbar) collides", sh, seen1[k1])
        exts = []
        for a in range(1, EXT + 1):
            ea = tuple(sorted(cofvec(extend(sh, a))[0].items()))
            exts.append(ea)
            k2 = (a, s0, ea)
            assert seen2.setdefault(k2, sh) == sh, ("X -> (s_X, s_{X.(a)}) collides", sh, a)
            # unordered {s_X, s_{X.(a)}}: injective into (X, a) with a free
            k3 = frozenset((s0, ea))
            assert seen3.setdefault(k3, (sh, a)) == (sh, a), ("unordered pair collides", sh, a)
        for a, b in itertools.combinations(range(1, EXT + 1), 2):
            k4 = frozenset((exts[a - 1], exts[b - 1]))
            assert seen4.setdefault(k4, (sh, a, b)) == (sh, a, b), ("two extensions collide", sh, a, b)
    print("(4) over all %d inner boundaries at once: (s_X, s_Xbar) injective; (s_X, s_{X.(a)}) injective for"
          % len(shapes))
    print("    a = 1..%d; the unordered pairs {s_X, s_{X.(a)}} and {s_{X.(a)}, s_{X.(b)}} are injective"
          % EXT)
    print("    in (X, a) and (X, {a, b}) with the lengths not supplied")

    # ------------------------------------------------ (5) the explicit witnesses
    # subsec:child-separation: (3+t,3)/(t,0) share rows {3,3} and the initial monomial h_3^2 of C_0
    inits = []
    for t in (0, 1, 2):
        sh = ((3 + t, 3), (t, 0))
        assert connected(sh) and sorted(rows(sh)) == [3, 3]
        w, fc = init_face(cofvec(sh)[0], SQ)
        assert set(fc) == {(3, 3)}
        inits.append(sh[1])
    assert len(set(inits)) == 3
    print("(5) (3+t,3)/(t,0), t = 0,1,2: rows {3,3}, initial monomial h_3^2, inner boundaries all different")

    def overlaps(sh):
        """Row overlap partitions ro_k: for each k, the multiset over runs of k consecutive rows of
        the number of columns they share; column overlaps are those of the transpose."""
        lam, mu = sh
        mu = tuple(mu) + (0,) * (len(lam) - len(mu))
        n = len(lam)
        out = []
        for k in range(1, n + 1):
            vals = []
            for i in range(n - k + 1):
                w = min(lam[i:i + k]) - max(mu[i:i + k])
                if w > 0:
                    vals.append(w)
            out.append(tuple(sorted(vals, reverse=True)))
        return out

    def col_overlaps(sh):
        lam, mu = sh
        mu = tuple(mu) + (0,) * (len(lam) - len(mu))
        cols = defaultdict(list)
        for i in range(len(lam)):
            for c in range(mu[i] + 1, lam[i] + 1):
                cols[c].append(i)
        cs = sorted(cols)
        out = []
        for k in range(1, len(cs) + 1):
            vals = []
            for a in range(len(cs) - k + 1):
                inter = set(cols[cs[a]])
                for c in cs[a + 1:a + k]:
                    inter &= set(cols[c])
                if len(inter) > 0:
                    vals.append(len(inter))
            out.append(tuple(sorted(vals, reverse=True)))
        return out

    U = ((7, 7, 5, 4), (6, 4, 2, 0))
    V = ((7, 7, 6, 3), (6, 4, 2, 0))
    assert connected(U) and connected(V) and cofvec(U)[0] == cofvec(V)[0]
    assert overlaps(U) == overlaps(V) and overlaps(first_row_deleted(U)) == overlaps(first_row_deleted(V))
    assert col_overlaps(U) == col_overlaps(V)
    Ubar, Vbar = first_row_deleted(U), first_row_deleted(V)
    assert Ubar == ((7, 5, 4), (4, 2, 0)) and Vbar == ((7, 6, 3), (4, 2, 0))
    assert sub(sp(Ubar), sp(Vbar)) == {(7, 3): 1, (6, 4): -1}      # h_3 h_7 - h_4 h_6
    Xf, Yf = ((7, 5, 4), (4, 2, 0)), ((7, 6, 3), (4, 2, 0))
    assert overlaps(Xf) == overlaps(Yf) and col_overlaps(Xf) == col_overlaps(Yf)
    assert sub(cofvec(Xf)[0], cofvec(Yf)[0]) == {(7, 3): 1, (6, 4): -1}
    print("    U, V and X, Y of the front matter and `subsec:fingerprint-not-classification` agree in every row")
    print("    and column overlap partition, and differ exactly as printed")

    # rem:one-extension-insufficient
    def jt_index(sh):
        lam, mu = sh
        mu = tuple(mu) + (0,) * (len(lam) - len(mu))
        n = len(lam)
        return [[lam[i] - mu[j] - i + j for j in range(n)] for i in range(n)]

    base = {}
    for a in range(1, 9):
        mu = (4 * a - 2, 2 * a - 1, 0)
        Ua = ((6 * a - 2, 5 * a - 1, 2 * a), mu)
        Va = ((6 * a - 2, 4 * a - 1, 3 * a), mu)
        assert connected(Ua) and connected(Va)
        Ue, Ve = extend(Ua, a), extend(Va, a)
        assert connected(Ue) and connected(Ve)
        assert sp(Ue) == sp(Ve), ("equal extensions", a)
        assert sub(sp(Ua), sp(Va)) == {(4 * a, 3 * a): 1, (5 * a, 2 * a): -1}, ("difference", a)
        for name, sh in (("U", Ua), ("V", Va), ("Ue", Ue), ("Ve", Ve)):
            if a == 1:
                base[name] = jt_index(sh)
            else:
                b0 = base[name]
                b1 = jt_index(sh)
                assert b1 == [[a * x for x in row] for row in b0], ("subscripts scale by a", name, a)
    X0, Y0 = ((4, 4, 4, 2), (3, 2, 1, 0)), ((4, 4, 3, 3), (3, 2, 1, 0))
    assert extend(((4, 4, 2), (2, 1, 0)), 1) == X0 and extend(((4, 3, 3), (2, 1, 0)), 1) == Y0
    # the substitution h_k -> h_{ak} is an injective ring homomorphism: the a = 1 difference maps
    # onto the a-th, monomial by monomial
    d1 = sub(sp(((4, 4, 2), (2, 1, 0))), sp(((4, 3, 3), (2, 1, 0))))
    for a in range(1, 9):
        da = {tuple(sorted((a * e for e in m), reverse=True)): c for m, c in d1.items()}
        mu = (4 * a - 2, 2 * a - 1, 0)
        assert sub(sp(((6 * a - 2, 5 * a - 1, 2 * a), mu)), sp(((6 * a - 2, 4 * a - 1, 3 * a), mu))) == da
    print("    rem:one-extension-insufficient: a = 1..8 equal extensions, difference h_{3a}h_{4a} - h_{2a}h_{5a},")
    print("    every Jacobi-Trudi subscript a times its a = 1 value, and a = 1 is the equal pair of the example")

    # ------------------------------------------------ def:reversal
    n_rot = 0
    for sh in shapes:
        rt = rotate(sh)
        assert connected(rt)
        assert cofvec(rt)[0] == cofvec(sh)[0], ("a diagram and its rotation are equivalent", sh)
        n_rot += 1
    print("def:reversal: %d diagrams, each skew-equivalent to its 180-degree rotation" % n_rot)
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
