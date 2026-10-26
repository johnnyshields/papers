r"""Paper section `sec:full-rigidity`, subsection `subsec:locus-family` (Reversal pairs on the locus).
Target labels: `lem:two-series-reversal`, `prop:staircase-reversal`, `cor:locus-family`,
`rem:staircase-boundary`.

The family X_w = (w + mu)/mu on the staircase mu = (N-1, ..., 1, 0), built from the definition and
compared with the paper's determinant D(rho) = det(h_{rho_i + 2(j-i)}).

  (A) prop:staircase-reversal over EVERY word w in {2,3}^N with w_0 = w_{N-1} = 2 for N = 4..NMAX:
      X_w and X_{w*} are connected, share the inner boundary and the cap grid d_j = 2j, satisfy the
      ratio identity at (r, a) = (2, 1); P_r(C(X_w)) = D(r, w), and F(w) = h_1 P_2 - P_3 = D(1, 2, w);
      the two diagrams are distinct and s_X != s_{X*} exactly when w != w*; the pair counts are
      2^{N-2} words, 2^{ceil((N-2)/2)} palindromes and (2^{N-2} - 2^{ceil((N-2)/2)})/2 unordered pairs.
      Palindromes give the zero defect, so the count of pairs is the count of nonzero ones.
  (B) cor:locus-family for k = 1..KMAX by the direct determinants: supp G, m = 2k, T_0^+ = {d_1, d_2},
      alpha_0 = 13k + 20, alpha_0 - m_+ = 8, wt(G_2) = 13k - 4, the factorization of the cofactors
      C_j(rho) = (-1)^j prod_{1<=i<j} h_{rho_i - 2} . D(rho_j, ..., rho_{N-1}), the separation of the two
      parents' diagonal square weights by 4 min(j-1, 2k+1-j), and the last two coordinates.  The
      separation and the last two coordinates are then asserted for k up to KBIG from the printed
      factorization alone (which (B) has just verified against the direct determinant), where the
      determinant itself is out of reach.
  (C) rem:staircase-boundary for every nonpalindromic word with w_0 = w_{N-1} = 3: the grid
      d_j = 2j + 1, the first-column expansion h_1 P_r(C(X_w)) = D(r+1, w) + (h_1 h_r - h_{r+1}) D(w) for
      r = 1..N, D(1,2,w) = D(1,2,w*), the relation h_1 P_2(G) - h_1^2 P_1(G) + e_3 G_0 = 0, G_0 != 0, the
      failure of the ratio identity at (2,1), the initial form -h_1^3 h_2 h_4 h_5 of the smallest witness,
      and the weight bookkeeping of the paper's contradiction on the grid d_j = 2j + 1.
"""
import itertools
import sys
from fractions import Fraction

from _census_common import (
    SQ, WEIGHTS, Pair, cofvec, connected, det_dp, grid, h, init_face, neg, padd, pmul, Pk, s_poly, sub, wpoly,
)

NMAX = 9
KMAX = 4
KBIG = 40


def Dpoly(rho):
    """D(rho) = det(h_{rho_i + 2(j - i)}), the determinant running over the length of rho."""
    n = len(rho)
    return det_dp([[rho[i] + 2 * (j - i) for j in range(n)] for i in range(n)])


def X(w):
    N = len(w)
    mu = tuple(range(N - 1, -1, -1))
    return (tuple(a + b for a, b in zip(w, mu)), mu)


def words(N, ends):
    for mid in itertools.product((2, 3), repeat=N - 2):
        yield (ends,) + mid + (ends,)


def ratio_holds(G, d, r, a):
    return Pk(G, d, r + a) == pmul(h(a), Pk(G, d, r))


def main():
    # ------------------------------------------------------------ (A)
    for N in range(4, NMAX + 1):
        n_words = n_pal = n_pairs = 0
        for w in words(N, 2):
            ws = tuple(reversed(w))
            n_words += 1
            Xw, Xs = X(w), X(ws)
            assert connected(Xw) and connected(Xs)
            assert [Xw[0][i] - Xw[1][i] for i in range(N)] == list(w)
            Aw, dw = grid(Xw)
            As, ds = grid(Xs)
            assert Xw[1] == Xs[1] and dw == ds == [2 * j for j in range(N + 1)], (w,)
            assert all(Aw[i] == 2 * i + 2 - w[i] for i in range(N))
            vec = cofvec(Xw)
            # P_r(C(X_w)) = D(r, w) and F(w) = D(1, 2, w)
            for r in (1, 2, 3):
                assert Pk(vec, dw, r) == Dpoly((r,) + w), ("P_r = D(r, w)", w, r)
            Fw = padd(pmul(h(1), Pk(vec, dw, 2)), neg(Pk(vec, dw, 3)))
            assert Fw == Dpoly((1, 2) + w), ("F(w) = D(1,2,w)", w)
            vecs = cofvec(Xs)
            Fs = padd(pmul(h(1), Pk(vecs, dw, 2)), neg(Pk(vecs, dw, 3)))
            assert Fw == Fs, ("F(w) = F(w*)", w)
            G = [padd(a, neg(b)) for a, b in zip(vec, vecs)]
            assert ratio_holds(G, dw, 2, 1), ("ratio identity at (2,1)", w)
            if w == ws:
                n_pal += 1
                assert Xw == Xs and not any(G)
            else:
                n_pairs += 1
                assert Xw != Xs and vec[0] != vecs[0], ("s_X != s_X*", w)
                assert any(G)
        assert n_words == 2 ** (N - 2)
        assert n_pal == 2 ** ((N - 1) // 2), (N, n_pal)               # ceil((N-2)/2)
        assert n_pairs % 2 == 0 and n_pairs // 2 == (2 ** (N - 2) - 2 ** ((N - 1) // 2)) // 2
        print("(A) N = %d: %3d words, %2d palindromes, %3d unordered pairs, all on the ratio locus with s_X != s_X*"
              % (N, n_words, n_pal, n_pairs // 2))
    # the identification needs the end letters: a word with w_0 = 3 has a different grid
    w = (3, 2, 2, 2)
    assert grid(X(w))[1] != [2 * j for j in range(5)]

    # ------------------------------------------------------------ (B)
    for k in range(1, KMAX + 1):
        N = 2 * k + 2
        rA = (2,) + (2,) * k + (3,) * k + (2,)
        rB = (2,) + (3,) * k + (2,) * k + (2,)
        XA, XB = X(rA), X(rB)
        assert rB == tuple(reversed(rA)) and rA[0] == rA[-1] == 2
        P = Pair(XA, XB)
        d, G = P.d, P.G
        assert d == [2 * j for j in range(N + 1)]
        assert ratio_holds(G, d, 2, 1)
        supp = [d[j] for j in range(N + 1) if G[j]]
        assert supp == [0] + [2 * j for j in range(1, 2 * k + 1)], ("support", k, supp)
        assert supp == list(range(0, 4 * k + 1, 2)) and len(supp) - 1 == 2 * k
        assert not G[N - 1] and not G[N]
        al = P.alpha(SQ)
        pos = [j for j in range(1, N + 1) if al[j] is not None]
        m_plus = min(al[j] for j in pos)
        assert [d[j] for j in pos if al[j] == m_plus] == [d[1], d[2]], ("T_0^+", k)
        assert al[0] == 13 * k + 20 and al[0] - m_plus == 8 == 2 * 2 * d[1], ("alpha_0", k, al)
        assert wpoly(G[2], SQ) == 13 * k - 4 and al[2] == m_plus, ("wt(G_2)", k)
        # the printed factorization, against the direct cofactors
        for rho, vecp in ((rA, cofvec(XA)), (rB, cofvec(XB))):
            for j in range(1, N + 1):
                pre = {(): 1}
                for i in range(1, j):
                    pre = pmul(pre, h(rho[i] - 2))
                cj = pmul(pre, Dpoly(rho[j:]) if j < N else {(): 1})
                cj = cj if j % 2 == 0 else neg(cj)
                assert vecp[j] == cj, ("cofactor factorization", k, rho, j)
        # the last two coordinates
        for rho, vecp in ((rA, cofvec(XA)), (rB, cofvec(XB))):
            assert vecp[N - 1] == {tuple(sorted([2] + [1] * k, reverse=True)): -1}     # -h_1^k h_2
            assert vecp[N] == {tuple([1] * k): 1}                                     # h_1^k
        # every clause of thm:ratio-rigidity at all four weights
        for nm, om in WEIGHTS.items():
            a2 = P.alpha(om)
            for i in range(P.v):
                mn = min(v for v in P.F(i, om, a2).values())
                assert [j for j, v in P.F(i, om, a2).items() if v == mn] == [i + 1, i + 2], (nm, k, i)
            Fv = {j: a2[j] + om(d[j] + 2) - om(d[j]) for j in range(N + 1) if a2[j] is not None}
            mn = min(Fv.values())
            assert [j for j, v in Fv.items() if v == mn] == [0, 1], (nm, k)
        print("(B) k = %d (N = %d): supp G = {0,2,...,%d}, m = %d, T_0^+ = {d_1,d_2}, alpha_0 = %d, gap 8, wt(G_2) = %d"
              % (k, N, 4 * k, 2 * k, al[0], 13 * k - 4))

    # diagonal-weight separation and the last two coordinates, from the printed factorization, large k
    def diag_weight(rho, j):
        return (sum((rho[i] - 2) ** 2 for i in range(1, j)) + sum(rho[i] ** 2 for i in range(j, len(rho))))

    # the factorization's diagonal weight against the actual initial face, small k
    for k in range(1, KMAX + 1):
        N = 2 * k + 2
        rA = (2,) + (2,) * k + (3,) * k + (2,)
        rB = (2,) + (3,) * k + (2,) * k + (2,)
        for rho in (rA, rB):
            vec = cofvec(X(rho))
            for j in range(N + 1):
                w, _ = init_face(vec[j], SQ)
                if j == 0:
                    assert w == sum(r * r for r in rho)
                else:
                    assert w == diag_weight(rho, j), ("diagonal weight", k, j)
    for k in range(1, KBIG + 1):
        N = 2 * k + 2
        rA = (2,) + (2,) * k + (3,) * k + (2,)
        rB = (2,) + (3,) * k + (2,) * k + (2,)
        assert len(rA) == N
        for j in range(2, 2 * k + 1):
            assert abs(diag_weight(rA, j) - diag_weight(rB, j)) == 4 * min(j - 1, 2 * k + 1 - j), (k, j)
            assert 4 * min(j - 1, 2 * k + 1 - j) > 0
        for rho in (rA, rB):
            tail = [rho[i] - 2 for i in range(1, N - 1)]
            assert sorted(e for e in tail if e > 0) == [1] * k          # h_1^k at j = N and at j = N-1
    print("(B) separation 4 min(j-1, 2k+1-j) of the parents' diagonal weights and the last two coordinates, k <= %d" % KBIG)

    # ------------------------------------------------------------ (C)
    e3 = {(1, 1, 1): 1, (2, 1): -2, (3,): 1}
    assert wpoly(e3, SQ) == 3
    n_c = 0
    smallest = None
    for N in range(4, 9):
        for w in words(N, 3):
            ws = tuple(reversed(w))
            if w == ws:
                continue
            Xw, Xs = X(w), X(ws)
            assert connected(Xw) and connected(Xs)
            Aw, dw = grid(Xw)
            assert dw == [0] + [2 * j + 1 for j in range(1, N + 1)], ("grid d_j = 2j+1", w)
            vec, vecs = cofvec(Xw), cofvec(Xs)
            for r in range(1, N + 1):
                lhs = pmul(h(1), Pk(vec, dw, r))
                rhs = padd(Dpoly((r + 1,) + w), pmul(padd(pmul(h(1), h(r)), neg(h(r + 1))), Dpoly(w)))
                assert lhs == rhs, ("first-column expansion", w, r)
            assert Dpoly((1, 2) + w) == Dpoly((1, 2) + ws)
            G = [padd(a, neg(b)) for a, b in zip(vec, vecs)]
            rel = padd(padd(pmul(h(1), Pk(G, dw, 2)), neg(pmul(pmul(h(1), h(1)), Pk(G, dw, 1)))), pmul(e3, G[0]))
            assert not rel, ("h1 P2(G) - h1^2 P1(G) + e3 G0 = 0", w)
            assert G[0], ("G_0 != 0", w)
            assert vec[0] != vecs[0]                               # the parents are inequivalent
            assert not ratio_holds(G, dw, 2, 1), ("ratio identity fails at (2,1)", w)
            if smallest is None:
                smallest = (N, w)
            n_c += 1
    print("(C) %d nonpalindromic words with end letters 3 (N = 4..8): expansion, relation, G_0 != 0, no ratio identity" % n_c)
    # the smallest witness on this boundary
    w = (3, 2, 3, 3)
    ws = tuple(reversed(w))
    assert w != ws and X(w)[0][0] == 6
    Pw = Pair(X(w), X(ws))
    diff = padd(pmul(h(1), Pk(Pw.G, Pw.d, 2)), neg(Pk(Pw.G, Pw.d, 3)))
    wm, fc = init_face(diff, SQ)
    assert set(fc) == {(5, 4, 2, 1, 1, 1)} and list(fc.values()) == [-1], fc
    # no shorter nonpalindromic word with end letters 3: a word of length 2 or 3 is a palindrome
    for N in (3,):
        assert all(wd == tuple(reversed(wd)) for wd in words(N, 3))
    # the weight bookkeeping of the contradiction, on the grid d_j = 2j + 1, for every length
    for N in range(4, 60):
        d = [0] + [2 * j + 1 for j in range(1, N + 1)]
        # P_1(G): column 1 at u + (d_1+1)^2 - d_1^2, column 0 at (u + 12) + 1, columns j >= 2 at >= u + ...
        c1 = (d[1] + 1) ** 2 - d[1] ** 2
        assert c1 == 7
        c0 = 12 + 1
        assert c0 == 13
        later1 = min((d[j] + 1) ** 2 - d[j] ** 2 for j in range(2, N + 1))
        assert later1 == 11
        # P_2(G): every summand at least u + 16
        p2 = [12 + 4] + [(d[j] + 2) ** 2 - d[j] ** 2 for j in range(1, N + 1)]
        assert min(p2) == 16
        # the three terms: >= u + 1 + 16, exactly u + 2 + 7, exactly u + 3 + 12
        assert 1 + min(p2) == 17 and 2 + c1 == 9 and 3 + 12 == 15
        assert min(17, 9, 15) == 9 and (9 != 15) and 9 < 15 < 17           # a unique minimum
    print("    weight bookkeeping u+7, u+13, >= u+11, >= u+16 -> terms >= u+17, u+9, u+15 for N = 4..59:")
    print("    the minimum u+9 is unique, so the relation cannot vanish")
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
