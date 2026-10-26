r"""Paper section `sec:charts` (Marked charts, boundary words, and Jacobi--Trudi data).

Targets `eq:phi`, `eq:normalizer`, `eq:exact-corner-transport` and `lem:faithful`, in the
subsection on functions, cofactors and normalizations.

Marked inners are enumerated from actual skew diagrams `E` (every legal mark of every case
`(a)`--`(d)`, plus the empty mark), outers `D` from actual skew diagrams, and the composition
`D o_omega E` is built cell by cell from the origin formula of the paper.  Schur functions are
Jacobi--Trudi determinants evaluated exactly (`Fraction`) at fixed rational alphabets; each
identity is a polynomial identity, so agreement at independent random alphabets is a
Schwartz--Zippel test, not a proof.  The modified-composition homomorphism `Phi` is applied to
the Jacobi--Trudi determinant of `D` with `Phi(h_j) = A^{j-1} s_{Row_j o E}` read off actual
row probes, `A, B, C` are Schur functions of the actual `W`, `hat W`, `hat O`.  The corner
derivative `kappa_S = d/dh_{N_S} Q_S` is taken from the determinant (linear in `h_{N_S}`,
verified at three values) and compared with the displayed corner formula, whose caps `K_-`,
`K_+` are cut from `E^-` by content.

Asserted: `eq:normalizer` up to a sign that is exactly `+1` for the ordinary cases and
`(-1)^{r(D)-1}` for the mixed ones (the paper leaves the mixed sign to the convention);
`eq:exact-corner-transport` for rows, for `E` and for general `D` with the components of `D^-`;
the exponent nonnegativity and the span bounds of the factors; and `lem:faithful` on the sampled
outers (equal parents force equal outers).  Sampled, not exhaustive: marks on `E` up to 6 cells
(3 rows, 4 columns) and outers up to 4 cells.
"""
import sys
from fractions import Fraction

from check_regroup_mixed import (Mark, add, content, is_connected, legal_marks, min_content,
                                 skew_shapes, span, sw, translate, smul, vH, E_CELL)
from _schur_common import alphabet, components, determinant, minus, schur

HS = [alphabet(s) for s in (11, 12)]


def hats(m):
    """`hat W` and `hat O` of condition (IV) for the lower copy and the middle."""
    U = set()
    for k in range(-12, 13):
        U |= set(translate(smul(k, m.v), m.E))
    W1 = set(m.W)
    hatW = {x for x in U if add(x, E_CELL) in W1} | {x for x in W1 if add(x, E_CELL) in U}
    O = m.middle()
    hatO = frozenset(x for x in O if add(x, E_CELL) in O)
    return frozenset(hatW), hatO


def rows_cols_span(D):
    return len({x[0] for x in D}), len({x[1] for x in D}), span(D)


def kappa(S, h):
    N = span(S)
    r = len({x[0] for x in S})
    vals = [schur(S, lambda j, t=t: Fraction(t) if j == N else h(j)) for t in (0, 1, 2)]
    assert vals[2] - vals[1] == vals[1] - vals[0], "s_S must be affine in h_{N_S}"
    return (-1) ** (r - 1) * (vals[1] - vals[0])


def poly_span_bound(S):
    """Largest generator index `j` occurring in the Jacobi--Trudi data of `S` (max over components)."""
    return max((span(C) for C in components(S)), default=0)


def main():
    outers = [D for D in skew_shapes(4, 3, 3) if len(D) >= 2]
    n_marks = n_norm = n_corner = n_faith = n_pairs = 0
    signs = {}
    for E in skew_shapes(6, 3, 4):
        if len(E) < 2:
            continue
        marks = list(legal_marks(E)) + [Mark(E, frozenset(), vH(E), 'a')]
        for m in marks:
            n_marks += 1
            p, w = m.period(), m.width()
            c0 = min_content(E)
            Em = minus(E)
            Km = frozenset(x for x in Em if 0 <= content(x) - c0 < w)
            Kp = frozenset(x for x in Em if p <= content(x) - c0 < p + w)
            hw, ho = hats(m)
            for h in HS:
                A, B, C = schur(m.W, h), schur(hw, h), schur(ho, h)
                Th = schur(Km, h) * schur(Kp, h)
                if w == 0:
                    assert (A, B, Th) == (1, 1, 1) and C == schur(Em, h)   # empty width
                # polynomial spans of the local factors: at most w, w, p-w-2, w-1 (when nonnegative)
                for name, S, bound in (('A', m.W, w), ('B', hw, w), ('C', ho, p - w - 2),
                                       ('Theta', Km, w - 1), ('Theta', Kp, w - 1)):
                    if bound >= 0:
                        assert poly_span_bound(S) <= bound, (name, m.case, sorted(E), sorted(m.W))
                    assert poly_span_bound(S) < p
                kE = kappa(E, h)
                assert kE == Th * C                                          # kappa(E)
                for j in (1, 2, 3):
                    R = m.compose(frozenset((0, k) for k in range(j)))
                    assert kappa(R, h) == Th * C ** j * B ** (j - 1)         # kappa(Row_j o E)

                def phi(j):
                    if j <= 0:
                        return h(j)
                    return A ** (j - 1) * schur(m.compose(frozenset((0, k) for k in range(j))), h)

                parents = {}
                for D in outers:
                    F = m.compose(D)
                    rD, cD, N = rows_cols_span(D)
                    nD = len(D)
                    lhs = Fraction(1)
                    for comp in components(D):
                        a_rows = sorted({x[0] for x in comp})
                        lo = [min(x[1] for x in comp if x[0] == i) for i in a_rows]
                        hi = [max(x[1] for x in comp if x[0] == i) + 1 for i in a_rows]
                        k = len(a_rows)
                        lhs *= determinant([[phi(hi[i] - lo[j] - i + j) for j in range(k)]
                                            for i in range(k)])
                    ex = nD - N
                    rhs = A ** (nD - rD) * B ** (nD - cD) * (C ** ex if ex >= 0 else 1 / C ** (-ex)) * schur(F, h)
                    assert nD - rD >= 0 and nD - cD >= 0
                    assert rhs != 0
                    q = lhs / rhs
                    want = 1 if m.case in 'ab' else (-1) ** (rD - 1)
                    assert q == want, (m.case, sorted(E), sorted(m.W), sorted(D), q)   # eq:normalizer
                    n_norm += 1
                    # corner transport for D o E
                    Dm = minus(D)
                    kids = components(Dm)
                    ex_r = rD - 1 - sum(len({x[0] for x in K_}) for K_ in kids)
                    ex_c = cD - 1 - sum(len({x[1] for x in K_}) for K_ in kids)
                    ex_n = N - sum(span(K_) for K_ in kids)
                    assert min(ex_r, ex_c, ex_n) >= 0                         # exponents nonnegative
                    prod = Fraction(1)
                    for K_ in kids:
                        prod *= schur(m.compose(K_), h)
                    assert kappa(F, h) == Th * A ** ex_r * B ** ex_c * C ** ex_n * prod
                    n_corner += 1
                    parents.setdefault(schur(F, h), []).append(D)
                for val, Ds in parents.items():
                    n_pairs += len(Ds) * (len(Ds) - 1) // 2
                    for D1 in Ds:                                           # lem:faithful
                        assert schur(D1, h) == schur(Ds[0], h)
                        n_faith += 1
            signs[m.case] = signs.get(m.case, 0) + 1
    print(f"marks {n_marks} {signs}, normalizer {n_norm}, corner {n_corner}, "
          f"faithfulness {n_faith} ({n_pairs} equal-parent pairs)")
    assert n_norm > 0 and n_corner > 0 and set(signs) == set('abcd')
    print("PASS")


if __name__ == "__main__":
    main()
