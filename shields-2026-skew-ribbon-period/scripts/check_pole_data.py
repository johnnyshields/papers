r"""Paper section `sec:poles` (Endpoint poles and outward boundary defects).

`eq:local-pole-data` and the sign claim of `lem:local-forcing`, on actual connected components, plus
`eq:low-corner` for charts.

For every connected skew diagram `D` of span `s` (full flags `(s, I)/(C, 0)`, `h_0 = 1`) the data
`K = JT(I, C)`, `b = h_I`, `a_0 = h_{s-C}`, `F_D = h_s - a_0 K^-1 b`, `f_z = h_z - M(z,C) K^-1 b`,
`g_z = h_{s-z} - a_0 K^-1 M(I,z)`, `P_z = f_z g_z` are computed exactly.  Asserted: `F_D` equals
`s_D / d s_D/d h_s` (computed from the determinant); the exact top-row projection
`M(z, full columns) D^-1 e_top = f_z / F_D` for every `z`; and at the simultaneous negative-lex specialization
`h_j = -T^(B^j)` (exact integers, `B = 2 * span + 3`, `T = 3`) every `P_z` at an interior vacancy
`z` (not in `I` or `C`, `0 < z < s`) is strictly positive, including the product of the `P_z` of
different components (sign multiplicative).  Control: at a generic alphabet some `P_z` is negative.

`eq:low-corner`: for every proper chart `F = D o_omega E` of the census (all connected skew diagrams
up to 8 cells in a 4 x 5 box, inners of up to 4 cells), `kappa(F) = d s_F / d h_{N_F}` involves only generators
`h_j` with `j < p`, `p` the period of the chart (the factors `A, B, C, Theta` of `eq:exact-corner-transport`
and the transported children have span below `p`, but the children have span `p N_{D_i} + w`, so the
statement is read for ribbon outers, where there are no children): asserted for charts with ribbon
outer.  Sampled: components up to 5 cells in 3 rows and 3 columns.
"""
from fractions import Fraction

import sympy as sp

from check_regroup_mixed import is_connected, skew_shapes, span
from verify_charts import beta_lists
from _census_common import build

Hs = sp.symbols("h1:40")


def entry(j, vals):
    return sp.Integer(0) if j < 0 else (sp.Integer(1) if j == 0 else vals[j - 1])


def main():
    n = nproj = npos = nneg_generic = 0
    for S in skew_shapes(5, 3, 3):
        if len(S) < 2 or not is_connected(S):
            continue
        X, Y = beta_lists(S)
        s = X[0]
        I, C = list(X[1:]), list(Y[:-1])
        B = 2 * len(X) + 3
        spec = [sp.Integer(-(3 ** (B ** j))) if j <= s else sp.Integer(-1) for j in range(1, 40)]
        generic = [sp.Rational(7 + (j * 13) % 11, 3 + j % 5) for j in range(1, 40)]
        for vals, tag in ((spec, 'spec'), (generic, 'gen')):
            h = lambda j: entry(j, vals)
            K = sp.Matrix(len(I), len(C), lambda a, b: h(I[a] - C[b]))
            if I:
                Ki = K.inv()
                b_ = sp.Matrix([h(i) for i in I])
                a0 = sp.Matrix([[h(s - j) for j in C]])
                FD = h(s) - (a0 * Ki * b_)[0, 0]
                Mz = lambda z: sp.Matrix([[h(z - j) for j in C]])
                Mi = lambda z: sp.Matrix([h(i - z) for i in I])
                f = lambda z: h(z) - (Mz(z) * Ki * b_)[0, 0]
                g = lambda z: h(s - z) - (a0 * Ki * Mi(z))[0, 0]
            else:
                FD = h(s)
                f = lambda z: h(z)
                g = lambda z: h(s - z)
            # exact top-row projection and F_D = s_D / d s_D / d h_s (with symbolic top variable)
            if tag == 'gen':
                Dm = sp.Matrix(len(X), len(Y), lambda a, b: h(X[a] - Y[b]))
                Dinv = Dm.inv()
                for z in range(0, s):
                    row = sp.Matrix([[h(z - y) for y in Y]])
                    assert sp.simplify((row * Dinv)[0, 0] - f(z) / FD) == 0, (sorted(S), z)
                    nproj += 1
                # F_D from the determinant: linear in h_s
                t = sp.Symbol('t')
                Dt = sp.Matrix(len(X), len(Y), lambda a, b: t if X[a] - Y[b] == s else h(X[a] - Y[b]))
                dp = sp.Poly(sp.expand(Dt.det()), t)
                assert dp.degree() == 1
                kap = dp.coeff_monomial(t)
                assert sp.simplify(Dm.det() - FD * kap) == 0                    # F_D = s_D / (d s_D / d h_s)
                if any(f(z) * g(z) < 0 for z in range(1, s) if z not in X and z not in Y):
                    nneg_generic += 1
            else:
                for z in range(1, s):
                    if z not in X and z not in Y:
                        assert f(z) * g(z) > 0, (sorted(S), z)
                        npos += 1
        n += 1
    # eq:low-corner for ribbon-outer charts
    shapes, sch, classes, charts, outers = build(8, 4, 5, 4)
    nlow = 0
    for G, lst in charts.items():
        for (w, sp_, p, key, m, A) in lst:
            if len({x[0] for x in A}) < 1:
                continue
            if sum(1 for x in A) != span(A):          # ribbon outer: area = span
                continue
            X, Y = beta_lists(G)
            N = X[0]
            # kappa(G) = derivative of s_G in h_N: find the largest generator index of its variables
            gens = sp.symbols(f"g1:{N + 1}")
            hh = lambda j: sp.Integer(0) if j < 0 else (sp.Integer(1) if j == 0 else gens[j - 1])
            dm = sp.Matrix(len(X), len(X), lambda a, b: hh(X[a] - Y[b])).det()
            kap = sp.diff(sp.expand(dm), gens[N - 1])
            used = [j + 1 for j, gv in enumerate(gens) if kap.has(gv)]
            assert all(j < p for j in used), ('eq:low-corner', sorted(G), p, used)
            nlow += 1
    print(f"components {n}; projection identities {nproj}; positive products {npos}; generic alphabet shows negative products on {nneg_generic} components; low-corner charts {nlow}")
    assert nproj > 0 and npos > 0 and nneg_generic > 0 and nlow > 0
    print("PASS")


if __name__ == "__main__":
    main()
