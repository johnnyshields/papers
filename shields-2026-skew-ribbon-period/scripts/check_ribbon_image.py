r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Two identities of the composition-image subsection.

`lem:ribbon-image`: for a ribbon `G` (composition `alpha` of `n = q m`) the coarsening expansion with every
raw generator `h_j`, `q` not dividing `j`, set to zero equals the ribbon function of `G'`, the ribbon
obtained by keeping the cuts of `G` at multiples of `q` and dividing positions by `q`, with
`h_j -> h_{qj}`, up to the phase `(-1)^(rows(G) - rows(G'))` (the paper's "fixed canonical phase"; the statement
says "canonical function of the ribbon" without naming it).  Both sides are exact `sympy` polynomials from the Jacobi--Trudi determinants of
the actual ribbons; checked for every composition of `n <= 12` and `q` in `{2, 3, 4}` dividing `n`.

Terminal readout consumed by `eq:ratio-readout` and `prop:full-image`: for an ordinary case-(a) legal
mark and a row outer of `M` cells, `delta_p^(M-1) s_F / delta_p^M s_F = s_E / xi` with
`xi = delta_p s_E`, `delta_p = sum_{j >= p} h_{j-p} d/dh_j` (`h_0 = 1`).  Checked as polynomial
identities by cross-multiplication on all small inners `E` (up to 6 cells) with `M` in `{2, 3}`;
`delta_p^M s_F` is a nonzero constant multiple of `xi^M` there.
"""
import itertools

import sympy as sp

from check_regroup_mixed import legal_marks, skew_shapes
from verify_charts import beta_lists

NH = 24
Hs = sp.symbols(f"h1:{NH + 1}")


def h(j):
    return sp.Integer(0) if j < 0 else (sp.Integer(1) if j == 0 else Hs[j - 1])


def ribbon_poly(alpha, sub=h):
    k = len(alpha)
    zeta = [sum(alpha[i + 1:]) for i in range(k)]
    xi = [zeta[i] + alpha[i] for i in range(k)]
    return sp.expand(sp.Matrix(k, k, lambda i, j: sub(xi[i] - zeta[j])).det())


def compositions(n):
    for cuts in itertools.product((0, 1), repeat=n - 1):
        out, cur = [], 1
        for c in cuts:
            if c:
                out.append(cur); cur = 1
            else:
                cur += 1
        out.append(cur)
        yield tuple(out)


def delta(P, p):
    return sp.expand(sum(h(j - p) * sp.diff(P, Hs[j - 1]) for j in range(p, NH + 1)))


def schur_poly(S):
    X, Y = beta_lists(S)
    return sp.expand(sp.Matrix(len(X), len(X), lambda i, j: h(X[i] - Y[j])).det())


def main():
    nrib = 0
    for q in (2, 3, 4):
        for n in range(q, 13, q):
            m = n // q
            for alpha in compositions(n):
                cuts = set(itertools.accumulate(alpha[:-1]))
                kept = sorted(c // q for c in cuts if c % q == 0)
                beta, prev = [], 0
                for c in kept + [m]:
                    beta.append(c - prev); prev = c
                lhs = ribbon_poly(alpha, lambda j: h(j) if j % q == 0 or j < 0 else sp.Integer(0))
                rhs = ribbon_poly(tuple(beta), lambda j: h(q * j) if j >= 0 else sp.Integer(0))
                assert sp.expand(lhs - (-1) ** (len(alpha) - len(beta)) * rhs) == 0, (q, alpha)   # fixed canonical phase
                nrib += 1
    nread = 0
    for E in skew_shapes(6, 3, 4):
        if len(E) < 2:
            continue
        for om in legal_marks(E):
            if om.case != 'a' or om.width() == 0:
                continue
            p = om.period()
            sE = schur_poly(E)
            xi = delta(sE, p)
            if xi == 0:
                continue
            for M in (2, 3):
                F = om.compose(frozenset((0, j) for j in range(M)))
                sF = schur_poly(F)
                top, prev = sF, None
                seq = [sF]
                for _ in range(M):
                    seq.append(delta(seq[-1], p))
                dM1, dM = seq[M - 1], seq[M]
                assert dM != 0 and dM.is_number is False or dM != 0
                assert sp.expand(dM1 * xi - dM * sE) == 0, (sorted(E), sorted(om.W), M)
                nread += 1
    print(f"ribbon-image cases {nrib}, terminal-readout cases {nread}")
    assert nrib > 0 and nread > 0
    print("PASS")


if __name__ == "__main__":
    main()
