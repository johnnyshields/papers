r"""Paper section `app:cell-cut` (Integral cuts with a cell-only proper interior).

Targets `eq:cell-coarsenings`, `eq:physical-cut-sum`, `eq:all-unit-contraction`, `eq:cut-creation` and
`eq:whole-h1-jets` of the cut theorem's proof.

Boards are actual connected diagrams built from row lengths `r_i` and adjacent gaps
`g_i` in `{0, 1}` (overlap `g_i + 1` columns, so every positive component of `C^-` is a cell) with
`r_i > g_{i-1} + g_i`, up to four rows and row lengths up to four; beta lists are read off the cell sets, never from the
formulas.  `Q_C = (-1)^{s-1} det JT(X, Y)` with `h_0 = 1`, as a polynomial in `h_1, ...`.
Asserted for every board and every operator `L` in a range:
  * `eq:cell-coarsenings`: `Q_C` equals the sum over contiguous partitions of the rows with the
    stated block weights `q_B` and `h_1` exponent `e(P)` (the sign is `(-1)^{|P|-1}` as written);
  * `eq:all-unit-contraction`: for every `d` from `s - |Z|` to `s`, `psi_d((Q_C)_d)` equals the sum over
    sets `T` of `s - d` common betas of `epsilon_T Q_{B_T}^{[d]}`, with `B_T` built by deleting the rows
    and columns of `T`, subtracting one from every retained row beta, and the retained phase
    `(-1)^{d-1}` over all `d` slots;
  * `eq:cut-creation`: with `V_L^H, delta_L^H` the Hall/weighted derivations in the shifted variables
    `H_j = h_{j+1}`, the two contraction identities (the second with `d(q_{d+1})/d H_{L-1}`);
  * `eq:whole-h1-jets`: the `h_1`-jet recursions of `V_L Q_C` and `delta_L Q_C`.
# TODO: not yet verified -- `eq:ribbon-vertex-gates`, `eq:vertex-mask`, `eq:vertex-count`,
# `eq:vertex-saturation`, `eq:run-barriers`, `eq:path-surplus`, `eq:cell-mask-matching`,
# `eq:physical-unit-transport`, `eq:strip-indicators`: these are consequences of the theorem's
# hypotheses on `Q_0` (the whole currents are `m Q_0` and `alpha Q_0` with `Q_0` integral of span `R`),
# which describe a hypothetical current-area diagram `J`; no actual board satisfies them unless the
# conclusion already holds, so there is nothing to sample.  `eq:cut-creation`
# and the other identities above hold for every board and are what is asserted here.
"""
import itertools

import sympy as sp

from verify_charts import from_betas
from verify_descent import from_profile, normalize
from check_contact_currents import beta_lists

NH = 12
Hs = sp.symbols(f"h1:{NH + 1}")
Hh = sp.symbols(f"H0:{NH + 1}")           # H_j, j >= 1 used (H_0 = 1)


def h(j):
    return sp.Integer(0) if j < 0 else (sp.Integer(1) if j == 0 else Hs[j - 1])


def HH(j):
    return sp.Integer(0) if j < 0 else (sp.Integer(1) if j == 0 else Hh[j])


def boards(maxrows=4, maxlen=4):
    for s in range(1, maxrows + 1):
        for gaps in itertools.product((0, 1), repeat=s - 1):
            gp = (0,) + gaps + (0,)
            lo = [gp[i] + gp[i + 1] + 1 for i in range(s)]
            for lens in itertools.product(*[range(l, maxlen + 1) for l in lo]):
                if sum(lens) - sum(gaps) > 7:
                    continue
                yield lens, gaps


def lists(lens, gaps):
    S = from_profile(list(lens), [g + 1 for g in gaps])
    X, Y = beta_lists(S)
    return X, Y


def Qpoly(X, Y):
    s = len(X)
    return sp.expand((-1) ** (s - 1) * sp.Matrix(s, s, lambda i, j: h(X[i] - Y[j])).det())


def coarsenings(lens, gaps):
    s = len(lens)
    tot = 0
    for cuts in itertools.product((0, 1), repeat=s - 1):       # 1 = cut after row i
        blocks, cur = [], [0]
        for i, c in enumerate(cuts):
            if c:
                blocks.append(cur)
                cur = [i + 1]
            else:
                cur.append(i + 1)
        blocks.append(cur)
        term = (-1) ** (len(blocks) - 1)
        e = 0
        for B in blocks:
            qB = sum(lens[i] for i in B) - sum(gaps[i] for i in B[:-1])
            e += sum(gaps[i] for i in B[:-1])
            term *= h(qB)
        tot += term * h(1) ** e
    return sp.expand(tot)


def deg_part(P, d):
    P = sp.Poly(P, *Hs)
    return sum(c * sp.Mul(*[v ** k for v, k in zip(Hs, mon)]) for mon, c in P.terms() if sum(mon) == d)


def psi(P):
    out = 0
    for mon, c in sp.Poly(P, *Hs).terms():
        term = c
        for j, k in enumerate(mon, start=1):
            if j > 1:
                term *= Hh[j - 1] ** k
        out += term
    return sp.expand(out)


def Qshift(Xr, Yr):
    d = len(Xr)
    return sp.expand((-1) ** (d - 1) * sp.Matrix(d, d, lambda i, j: HH(Xr[i] - 1 - Yr[j])).det()) if d else 0


def vop_H(P, L, weighted):
    """`V_L^H` or `delta_L^H` on a polynomial in H_1.. (the derivations in shifted variables)."""
    out = 0
    for j in range(max(L, 1), NH):
        coeff = (j - L) if weighted else 1
        out += coeff * HH(j - L) * sp.diff(P, Hh[j]) if j < len(Hh) else 0
    return sp.expand(out)


def derivation(P, L, weighted):
    return sp.expand(sum(((j - L) if weighted else 1) * h(j - L) * sp.diff(P, Hs[j - 1])
                         for j in range(max(L, 1), NH + 1)))


def marked_cut(X, Y, L, t=None):
    """Marked-entry cofactor sum with `h_{x_i - y_j - L}` in place of the entry; with an indicator
    `y_j < t <= x_i - L` when `t` is given, without one (all `x_i - y_j >= L`) otherwise."""
    s = len(X)
    tot = 0
    for i in range(s):
        for j in range(s):
            k = X[i] - Y[j] - L
            if k < 0 or (t is not None and not Y[j] < t <= X[i] - L):
                continue
            minor = sp.Matrix(s - 1, s - 1, lambda a, b: h(X[a if a < i else a + 1] - Y[b if b < j else b + 1])) if s > 1 else sp.Matrix([[1]])
            cof = (-1) ** (i + j) * (minor.det() if s > 1 else 1)
            tot += h(k) * cof
    return sp.expand((-1) ** (s - 1) * tot)


def main():
    ncutsum = 0
    n = nT = ncut = njet = 0
    for lens, gaps in boards():
        s = len(lens)
        X, Y = lists(lens, gaps)
        assert len(X) == s
        Q = Qpoly(X, Y)
        assert Q == coarsenings(lens, gaps), (lens, gaps)                              # eq:cell-coarsenings
        n += 1
        Z = sorted(set(X) & set(Y))
        qd = {}
        for d in range(s - len(Z), s + 1):
            lhs = psi(deg_part(Q, d))
            rhs = 0
            for T in itertools.combinations(Z, s - d):
                IT = [i for i, x in enumerate(X) if x in T]
                JT = [j for j, y in enumerate(Y) if y in T]
                eps = (-1) ** sum(IT[k] - JT[k] + 1 for k in range(len(T)))      # positions (i, j) with x_i = y_j
                # pairs (i, j) with x_i = y_j in T
                pairs = [(X.index(z), Y.index(z)) for z in T]
                eps = (-1) ** sum(i - j + 1 for i, j in pairs)
                Xr = [X[i] - 1 + 1 - 0 for i in range(s) if i not in {p[0] for p in pairs}]
                Yr = [Y[j] for j in range(s) if j not in {p[1] for p in pairs}]
                rhs += eps * Qshift(Xr, Yr)
            assert sp.expand(lhs - rhs) == 0, ('contraction', lens, gaps, d)
            qd[d] = lhs
            nT += 1
        # eq:physical-cut-sum: V_L Q_C = sum_t N_t; the unweighted marked sum is delta_L Q_C
        for L in (2, 3, 4):
            R = X[0] - L
            if R >= 1:
                assert sp.expand(derivation(Q, L, True) - sum(marked_cut(X, Y, L, t) for t in range(1, R + 1))) == 0, (lens, gaps, L)
            assert sp.expand(derivation(Q, L, False) - marked_cut(X, Y, L)) == 0, (lens, gaps, L)
            ncutsum += 1
        # eq:cut-creation
        for L in (2, 3, 4):
            for d in range(s - len(Z), s + 1):
                Vq = psi(deg_part(derivation(Q, L, True), d))
                Dq = psi(deg_part(derivation(Q, L, False), d))
                rV = sp.expand(vop_H(qd[d], L, True) + vop_H(qd[d], L, False))
                rD = vop_H(qd[d], L, False)
                if d + 1 in qd and L - 1 >= 1:
                    rD = sp.expand(rD + sp.diff(qd[d + 1], Hh[L - 1]))
                assert sp.expand(Vq - rV) == 0, ('cut-creation V', lens, gaps, L, d)
                assert sp.expand(Dq - rD) == 0, ('cut-creation D', lens, gaps, L, d)
                ncut += 1
            # eq:whole-h1-jets
            jets = {j: sp.expand(sp.Poly(Q, Hs[0]).coeff_monomial(Hs[0] ** j)) for j in range(0, s + 2)}

            def op0(P, weighted):
                return sp.expand(derivation(P, L, weighted).subs(Hs[0], 0))
            for weighted in (True, False):
                full = derivation(Q, L, weighted)
                for j in range(0, s + 1):
                    lhs = sp.expand(sp.Poly(full, Hs[0]).coeff_monomial(Hs[0] ** j)) if full != 0 else 0
                    prev = jets.get(j - 1, 0) if j >= 1 else 0
                    rhs = op0(jets[j], weighted) + (sp.diff(prev, Hs[L]) if L + 1 <= NH else 0)
                    assert sp.expand(lhs - rhs) == 0, ('jets', lens, gaps, L, j, weighted)
                    njet += 1
    print(f"physical-cut sums {ncutsum}, boards {n}, contraction instances {nT}, cut-creation {ncut}, jet recursions {njet}")
    assert min(n, nT, ncut, njet) > 0
    print("PASS")


if __name__ == "__main__":
    main()
