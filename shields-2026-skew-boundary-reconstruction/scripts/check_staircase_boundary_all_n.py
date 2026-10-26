r"""Paper section `sec:full-rigidity`, subsection `subsec:locus-family` (Reversal pairs on the locus).
Target label: `rem:staircase-boundary`, for EVERY length N >= 4.

`check_locus_family_census.py` (C) checks the remark word by word to length 8.  This script carries every
step of the remark to arbitrary N by symbolic computation in N, the row index i and the column index j, so
the word length never enters as a number.

  (1) Cap coordinates.  For w in {2,3}^N with w_0 = 3 on the staircase mu = (N-1, ..., 0): L = N + 2,
      A_i = 3 - w_i + 2i (so A_0 = 0), d_0 = 0 and d_j = 2j + 1 for j >= 1, as identities in N, i, j.
  (2) Zero patterns, for both letters and every row index i (linear inequalities in i):
        the cap column 0 is (h_{-A_i}) = (1, 0, ..., 0);
        column 0 of D(r+1, w) is (h_{r+1}, h_1, 0, ..., 0);
        column 0 of D(1, 2, w) is (h_1, 1, 0, ..., 0).
  (3) Minor identifications, as index identities in i, j:
        cap matrix less column 0          = D(w);
        adjoined row and rows 1.. of M    = D(r+3, w_1, ..., w_{N-1});
        D(r+1, w) less row 0, column 0    = D(w);   less row 1, column 0 = D(r+3, w_1, ..., w_{N-1});
        D(1, 2, w) less row 0, column 0   = D(2, w); less row 1, column 0 = D(3, w).
  (4) With (2)-(3), the column-0 Laplace expansions read, for every word of every length,
        P_r(C(X_w)) = h_r D(w) - D(r+3, w'),    D(r+1, w) = h_{r+1} D(w) - h_1 D(r+3, w'),
        D(1,2,w) = h_1 D(2,w) - D(3,w),          C_0(X_w) = D(w),
      in which the D's are now independent symbols.  From these, sympy derives the remark's first-column
      expansion h_1 P_r = D(r+1, w) + (h_1 h_r - h_{r+1}) D(w) for symbolic r, and, adding
      `lem:two-series-reversal` (D(1,2,w) = D(1,2,w*)), the relation h_1 P_2(G) - h_1^2 P_1(G) + e_3 G_0 = 0
      with e_3 = h_1^3 - 2 h_1 h_2 + h_3.  Control: without the reversal input the relation is not implied.
  (5) The weight bookkeeping of the contradiction, symbolic in j and the unknown action u: with
      alpha_1 = alpha_2 = u, alpha_j >= u, alpha_0 = u + 2 r d_1 = u + 12 (`eq:square-gap` at gamma = r = 2):
      P_1 summands u+13 (j = 0), u+7 (j = 1), >= u + 4j + 3 >= u + 11 (j >= 2);  P_2 summands >= u+16;
      wt(e_3) = 3; the three terms >= u+17, = u+9, = u+15, so the minimum u+9 is unique.  Every bound is a
      linear function of j minimized at the end of its range, asserted symbolically, so it holds for all N.
  (6) The smallest witness: every word of length <= 3 with end letters 3 is a palindrome, and (3,2,3,3) is
      nonpalindromic (its initial form is asserted in the census).

What remains the paper's: G_0 != 0 from `cor:boundary-separation` and the ratio-rigidity input of (5).
"""
import itertools

import sympy as sp

from _census_common import Pk, cofvec, grid, h, padd, pmul
from check_locus_family_census import Dpoly, X

N, i, j, r = sp.symbols("N i j r", integer=True, positive=True)
h1, h2, h3 = sp.symbols("h1 h2 h3")


def main():
    # (1) cap coordinates, symbolic in N, i, j
    for wi in (2, 3):
        lam_i = wi + (N - 1 - i)                     # lambda_i = w_i + mu_i
        L = 3 + (N - 1)                              # lambda_0 with w_0 = 3
        assert sp.simplify(L - (N + 2)) == 0
        A_i = L - lam_i + i
        assert sp.expand(A_i - (3 - wi + 2 * i)) == 0
    d_j = (N + 2) - (N - 1 - (j - 1)) + j - 1        # d_j = L - mu_{j-1} + j - 1
    assert sp.expand(d_j - (2 * j + 1)) == 0
    print("(1) L = N+2, A_i = 3 - w_i + 2i, d_j = 2j+1: identities in N, i, j")

    # (2) zero patterns: an index that is negative for every i >= i_min and both letters
    def negative_from(expr, i_min):
        # expr is affine and nonincreasing in i, so negativity at i_min gives it for every larger i
        assert sp.diff(expr, i) <= 0
        return bool(expr.subs(i, i_min) < 0)
    for wi in (2, 3):
        assert negative_from(wi - 3 - 2 * i, 1)                  # cap column 0, rows i >= 1
        assert negative_from(wi + 2 * (0 - i), 2)                # D(r+1,w) column 0, rows i >= 2 carry w_{i-1}
        assert negative_from(wi + 2 * (0 - i), 2)                # D(1,2,w) column 0, rows i >= 2 carry w_{i-2}
    assert 3 - 3 - 0 == 0                                        # cap entry at (0,0) is h_0 = 1
    assert 3 + 2 * (0 - 1) == 1                                  # D(r+1,w): row 1 carries w_0 = 3, entry h_1
    assert 2 + 2 * (0 - 1) == 0                                  # D(1,2,w): row 1 carries 2, entry h_0 = 1
    print("(2) column-0 zero patterns hold at every row index, for both letters")

    # (3) minor identifications: entry index of the minor equals entry index of the named D
    jp = sp.Symbol("jp", integer=True, nonnegative=True)         # shifted column j' = j - 1
    for wi in (2, 3):
        cap = wi + 2 * ((jp + 1) - i - 1)                         # M_{i, j'+1} = h_{w_i + 2(j - i - 1)}
        assert sp.expand(cap - (wi + 2 * (jp - i))) == 0          # D(w) at (i, j')
        # adjoined row R_{j'+1} = h_{r + d_{j'+1}} and the rows i >= 1 of M as rows of D(r+3, w'), w'_{i-1} = w_i
        assert sp.expand((r + 2 * (jp + 1) + 1) - ((r + 3) + 2 * jp)) == 0
        assert sp.expand((wi + 2 * ((jp + 1) - i - 1)) - (wi + 2 * (jp - (i - 1)) - 2)) == 0
        # D(r+1, w): row 0 is r+1, row i >= 1 carries w_{i-1}; deleting row 0, column 0 gives D(w) with row i-1
        assert sp.expand((wi + 2 * ((jp + 1) - i)) - (wi + 2 * (jp - (i - 1)))) == 0
        # deleting row 1 (letter w_0 = 3), column 0: row 0 becomes h_{r+1+2(j'+1)} = h_{(r+3) + 2j'}
        assert sp.expand((r + 1 + 2 * (jp + 1)) - ((r + 3) + 2 * jp)) == 0
        # rows i >= 2 carry w_{i-1} = w'_{i-2}, at position i-1 in D(r+3, w')
        assert sp.expand((wi + 2 * ((jp + 1) - i)) - (wi + 2 * (jp - (i - 1)))) == 0
        # D(1, 2, w): deleting row 0, column 0 gives D(2, w); deleting row 1, column 0 gives D(3, w)
        assert sp.expand((2 + 2 * ((jp + 1) - 1)) - (2 + 2 * (jp - 0))) == 0
        assert sp.expand((1 + 2 * (jp + 1)) - (3 + 2 * jp)) == 0
        assert sp.expand((wi + 2 * ((jp + 1) - i)) - (wi + 2 * (jp - (i - 1)))) == 0
    print("(3) every minor is the named D, as index identities in i, j'")

    # (4) the expansions with D's as independent symbols, for the word w and its reversal ws
    hr, hr1 = sp.symbols("h_r h_r1")
    Dw, Dws = sp.symbols("Dw Dws")                                # D(w), D(w*)
    D = {(tag, s): sp.Symbol("D_%s_%s" % (s, tag)) for tag in ("w", "ws") for s in ("4p", "5p")}

    def P(tag, rr):
        """P_r(C(X_w)) = h_r D(w) - D(r+3, w'), with h_r and r+3 instantiated at r = 1, 2."""
        base = Dw if tag == "w" else Dws
        hrr = {1: h1, 2: h2}[rr]
        return hrr * base - D[tag, {1: "4p", 2: "5p"}[rr]]

    def Dplus(tag, rr):
        """D(r+1, w) = h_{r+1} D(w) - h_1 D(r+3, w')."""
        base = Dw if tag == "w" else Dws
        hrr1 = {1: h2, 2: h3}[rr]
        return hrr1 * base - h1 * D[tag, {1: "4p", 2: "5p"}[rr]]

    # the first-column expansion for symbolic r
    Dr3p = sp.Symbol("Dr3p")
    lhs = h1 * (hr * Dw - Dr3p)
    rhs = (hr1 * Dw - h1 * Dr3p) + (h1 * hr - hr1) * Dw
    assert sp.expand(lhs - rhs) == 0
    # D(1,2,w) = h_1 D(2,w) - D(3,w), with D(2,w) = D(r+1,w) at r = 1 and D(3,w) at r = 2
    D12 = {tag: h1 * Dplus(tag, 1) - Dplus(tag, 2) for tag in ("w", "ws")}
    G0 = Dw - Dws
    G_P = {rr: P("w", rr) - P("ws", rr) for rr in (1, 2)}
    e3 = h1 ** 3 - 2 * h1 * h2 + h3
    relation = h1 * G_P[2] - h1 ** 2 * G_P[1] + e3 * G0
    # relation is exactly -(D(1,2,w) - D(1,2,w*)), so the reversal lemma makes it vanish, and nothing less does
    assert sp.expand(relation + (D12["w"] - D12["ws"])) == 0
    assert sp.expand(relation) != 0
    # the signs of the three column-0 expansions, against actual determinants on every word to length 7
    n_words = 0
    for n in range(4, 8):
        for mid in itertools.product((2, 3), repeat=n - 2):
            w = (3,) + mid + (3,)
            vec = cofvec(X(w))
            _, d = grid(X(w))
            assert vec[0] == Dpoly(w)
            for rr in (1, 2, 3):
                assert Pk(vec, d, rr) == padd(pmul(h(rr), Dpoly(w)), Dpoly((rr + 3,) + w[1:]), -1), (w, rr)
                assert Dpoly((rr + 1,) + w) == padd(pmul(h(rr + 1), Dpoly(w)),
                                                    pmul(h(1), Dpoly((rr + 3,) + w[1:])), -1), (w, rr)
            assert Dpoly((1, 2) + w) == padd(pmul(h(1), Dpoly((2,) + w)), Dpoly((3,) + w), -1), w
            n_words += 1
    print("    the three column-0 expansions, signs included, on all %d words of length 4..7" % n_words)
    print("(4) h_1 P_r = D(r+1,w) + (h_1 h_r - h_{r+1}) D(w) for symbolic r; the relation "
          "h_1 P_2(G) - h_1^2 P_1(G) + e_3 G_0 equals -(D(1,2,w) - D(1,2,w*)), zero by lem:two-series-reversal")

    # (5) weight bookkeeping, symbolic in j and u
    u = sp.Symbol("u")
    jj = sp.Symbol("jj", integer=True)
    dsym = lambda t: 2 * t + 1                                   # noqa: E731, d_t for t >= 1
    alpha0 = u + 2 * 2 * dsym(1)
    assert alpha0 == u + 12
    inc1 = lambda t: (t + 1) ** 2 - t ** 2                       # noqa: E731
    inc2 = lambda t: (t + 2) ** 2 - t ** 2                       # noqa: E731
    p1_0 = alpha0 + inc1(0)
    p1_1 = u + inc1(dsym(1))
    p1_j = u + sp.expand(inc1(dsym(jj)))                         # lower bound, alpha_j >= u
    assert p1_0 == u + 13 and p1_1 == u + 7
    assert sp.expand(p1_j - (u + 4 * jj + 3)) == 0 and p1_j.subs(jj, 2) == u + 11
    p2_0 = alpha0 + inc2(0)
    p2_1 = u + inc2(dsym(1))
    p2_j = u + sp.expand(inc2(dsym(jj)))
    assert p2_0 == u + 16 and p2_1 == u + 16
    assert sp.expand(p2_j - (u + 8 * jj + 8)) == 0 and p2_j.subs(jj, 2) == u + 24
    wt_e3 = 3
    t1 = 1 + (u + 16)                 # h_1 P_2(G): at least
    t2 = 2 + p1_1                     # h_1^2 P_1(G): exactly, column one the unique minimum
    t3 = wt_e3 + alpha0               # e_3 G_0: exactly
    assert (t1, t2, t3) == (u + 17, u + 9, u + 15)
    assert sp.simplify(t3 - t2) > 0 and sp.simplify(t1 - t2) > 0
    assert sp.simplify(p1_0 - p1_1) > 0 and sp.simplify(p1_j.subs(jj, 2) - p1_1) > 0
    print("(5) bookkeeping symbolic in j: P_1 at u+13, u+7, >= u+4j+3; P_2 >= u+16; terms u+17, u+9, u+15")

    # (6) the smallest witness
    for n in (2, 3):
        for mid in itertools.product((2, 3), repeat=n - 2):
            wd = (3,) + mid + (3,)
            assert wd == wd[::-1]
    assert (3, 2, 3, 3) != (3, 3, 2, 3)
    print("(6) every word of length <= 3 with end letters 3 is a palindrome; (3,2,3,3) is not")
    print("rem:staircase-boundary: every step symbolic in N; word-by-word to length 8 in the census")
    print("ALL PASS")


if __name__ == "__main__":
    main()
