r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

`lem:distinct-leading` and `eq:distinct-leading` on legal positive marks with distinct phases.

For every legal mark `eta` of period `p`, width `w > 0` and phases `t != s` on a small inner `U`
(`check_regroup_mixed.legal_marks`, phases read from the middle as in `eq:coding`) the modified
homomorphism `Phi_eta(h_j) = A^(j-1) s_{Row_j o_eta U}` is built symbolically in `h_1, h_2, ...`
(`sympy`, Jacobi--Trudi determinants of the actual compositions).  The statement asserts a fixed
`gamma` in `{id, AT}`, a legal mark `eta_0` on `U_0 = Core(U)` and a core phase `epsilon = +-1` with, for
every nonzero weighted-homogeneous `f` of weight `d`, `in_ord Phi_eta(f) = epsilon^d Phi_{eta_0}(iota_gamma f)`
and `ord_ord Phi_eta(f) = d r(U_0)`, where `in_ord`/`ord_ord` are the least ordinary-degree
component and its degree (`h_j` of degree one for `j > 0`, `h_0 = 1`).  The script searches the
finite set of `(gamma, eta_0, epsilon)` for one that satisfies the identity on the test family
`h_1, h_2, h_3, h_1^2, h_1 h_2, e_2` (weights up to 3) and asserts it exists
and the least ordinary degree equals `d r(U_0)` for the whole family.  `iota` sends `h_j` to `e_j`
(the Jacobi--Trudi determinant of `h`).  Sampled: inners of up to 5 cells in 3 rows and 3 columns; test family above.
"""
import itertools

import sympy as sp

from check_regroup_mixed import content, legal_marks, min_content, skew_shapes, translate
from verify_charts import beta_lists, from_betas

NH = 24
Hs = sp.symbols(f"h1:{NH + 1}")


def h(j):
    return sp.Integer(0) if j < 0 else (sp.Integer(1) if j == 0 else Hs[j - 1])


def schur_sym(S, sub=None):
    if not S:
        return sp.Integer(1)
    X, Y = beta_lists(S)
    return sp.expand(sp.Matrix(len(X), len(X), lambda i, j: h(X[i] - Y[j])).det())


def core(S):
    X, Y = beta_lists(S)
    common = set(X) & set(Y)
    Xc = tuple(x for x in X if x not in common)
    Yc = tuple(y for y in Y if y not in common)
    return from_betas(Xc, Yc) if Xc else frozenset()


def row(j):
    return frozenset((0, k) for k in range(j))


def phi_gens(m, J):
    A = schur_sym(m.W)
    return {j: sp.expand(A ** (j - 1) * schur_sym(m.compose(row(j)))) for j in range(1, J + 1)}


def apply_phi(f, gens):
    return sp.expand(f.subs({Hs[j - 1]: gens[j] for j in gens}, simultaneous=True))


def e_poly(j):
    return sp.expand(sp.Matrix(j, j, lambda a, b: h(1 - a + b)).det()) if j else sp.Integer(1)


def iota(f):
    return sp.expand(f.subs({Hs[j - 1]: e_poly(j) for j in range(1, 4)}, simultaneous=True))


def ord_parts(P):
    P = sp.Poly(P, *Hs)
    if P.is_zero:
        return None, 0
    by = {}
    for mon, c in P.terms():
        by[sum(mon)] = by.get(sum(mon), 0) + c * sp.Mul(*[v ** k for v, k in zip(Hs, mon)])
    d = min(by)
    return d, sp.expand(by[d])


FAMILY = [Hs[0], Hs[1], Hs[2], Hs[0] ** 2, Hs[0] * Hs[1]]
WEIGHT = [1, 2, 3, 2, 3]


def main():
    n = nfound = 0
    for U in skew_shapes(5, 3, 3):
        if len(U) < 2:
            continue
        U0 = core(U)
        marks = [m for m in legal_marks(U) if m.width() > 0]
        for m in marks:
            c0 = min_content(U)
            cs = sorted(content(x) - c0 for x in m.middle())
            p, w = m.period(), m.width()
            s_, t_ = cs[0], cs[-1] - p + 1
            if s_ == t_ or not U0:
                continue
            gens = phi_gens(m, 3)
            fam = FAMILY + [e_poly(2)]
            wts = WEIGHT + [2]
            images = [apply_phi(f, gens) for f in fam]
            parts = [ord_parts(P) for P in images]
            r0 = len({x[0] for x in U0})
            cands = [m0 for m0 in legal_marks(U0) if m0.period() == p and m0.width() == w]
            assert cands
            ok_any = False
            for g in ('id', 'AT'):
                for m0 in cands:
                    g0 = phi_gens(m0, 3)
                    for eps in (1, -1):
                        good = True
                        for f, d, (od, lead) in zip(fam, wts, parts):
                            fi = f if g == 'id' else iota(f)
                            target = sp.expand(eps ** d * apply_phi(fi, g0))
                            if od != d * r0 or sp.expand(lead - target) != 0:
                                good = False
                                break
                        if good:
                            ok_any = True
                            break
                    if ok_any:
                        break
                if ok_any:
                    break
            assert ok_any, ("no (gamma, eta_0, epsilon) realizes eq:distinct-leading", sorted(U), sorted(m.W), m.case)
            nfound += 1
            n += 1
    print(f"distinct-phase positive marks {n}, all realized by some (gamma, eta_0, epsilon): {nfound}")
    assert n > 0
    print("PASS")


if __name__ == "__main__":
    main()
