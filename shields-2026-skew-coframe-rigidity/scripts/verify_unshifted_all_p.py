r"""Paper section `sec:unshifted` (Unshifted opposite-end exclusion).  Target `ph:unshifted-exclusion`, for EVERY
exponent p >= 2 on every board in range.

`verify_unshifted.py` checks the exponents two through four.  The exponent is removed here by a degree bound.
Write H = theta + U with U = sum_{i<M} H_i z^i.  Then [H^p]_j = theta^p sum_{i<=j} binom(p, i) theta^{-i} [U^i]_j,
a polynomial in p of degree at most j times theta^p, and p H^{p-1} is theta^p times a polynomial of degree at
most j + 1.  The defect

    E(p) = [ T_{G,C}(H^p) - p H^{p-1} D ]_{<2M},     D = T_{G,C}(H),

therefore has every coefficient equal to theta^p times a polynomial in p of degree at most 2M (the coframes
G, C do not depend on p).  The script asserts that degree bound numerically (interpolation from 2M+1
exponents reproduces three further ones), then for every nonself board V != V* reads off a coefficient whose
polynomial is nonzero with no integer root p >= 2.  A nonzero value at one rational point of the letters is
nonzero as a polynomial, so the identity of the lemma fails for every p >= 2: the lemma holds for all p on
every connected board of span 3 .. SPAN.  On self boards V = V* the defect vanishes at all 2M + 4 exponents,
hence for every p; and p = 1 is the excluded boundary, where it vanishes on every board.

The board quantifier stays a census (every connected board through span SPAN).
"""
import random

import sympy as sp

from _coframes import z, theta, letter, right_coframe, left_coframe, clock, clip, operator, connected_boards, rotate

random.seed(20261104)
SPAN = 5
P = sp.Symbol("p")


def defect_coefficients(g, c, h, M, p):
    d = operator(g, c, h, M)
    e = clip(operator(g, c, h ** p, M) - p * h ** (p - 1) * d, 2 * M)
    poly = sp.Poly(sp.expand(e), z)
    return [sp.cancel(poly.coeff_monomial(z ** k)) for k in range(2 * M)]


def numeric_point(M):
    return {theta: sp.Rational(random.randint(2, 9), random.randint(1, 4)),
            **{letter(i): sp.Rational(random.randint(-9, 9) or 1, random.randint(1, 5)) for i in range(1, M + 1)}}


def main():
    n_nonself = n_self = 0
    for M in range(3, SPAN + 1):
        for board in connected_boards(M):
            for _ in range(5):
                pt = numeric_point(M)
                try:
                    g = sp.expand(right_coframe(board).subs(pt))
                    c = sp.expand(left_coframe(board).subs(pt))
                    break
                except ZeroDivisionError:
                    continue
            assert all(x.is_Rational for x in sp.Poly(g, z).coeffs() + sp.Poly(c, z).coeffs())
            h = sp.expand(clock(M - 1).subs(pt))
            th = pt[theta]
            ps = list(range(1, 2 * M + 6))
            table = {p: [x / th ** p for x in defect_coefficients(g, c, h, M, p)] for p in ps}
            assert all(x == 0 for x in table[1]), board                      # exponent one: the boundary
            fit = range(2, 2 * M + 3)                                           # 2M + 1 exponents
            polys = []
            for k in range(2 * M):
                pk = sp.expand(sp.interpolate([(p, table[p][k]) for p in fit], P))
                for p in ps[1:]:
                    assert pk.subs(P, p) == table[p][k], ("degree bound", board, k, p)
                polys.append(pk)
            if board == rotate(board):
                assert all(pk == 0 for pk in polys), board
                n_self += 1
                continue
            witness = [pk for pk in polys if pk != 0 and not any(
                r.is_integer and r >= 2 for r in sp.Poly(pk, P).all_roots())]
            assert witness, ("some exponent p >= 2 satisfies the identity", board)
            n_nonself += 1
    assert n_nonself > 10 and n_self > 0
    print("PASS ph:unshifted-exclusion for every p >= 2 on all %d nonself connected boards of span 3..%d "
          "(defect coefficients polynomial in p of degree <= 2M, nonzero with no integer root >= 2); "
          "zero for every p on %d self boards; zero at p = 1 everywhere" % (n_nonself, SPAN, n_self))
    print("ALL PASS")


if __name__ == "__main__":
    main()
