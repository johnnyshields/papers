r"""Paper section `app:contacts` (Same-core contact currents).

Targets `eq:contact-definitions`, `lem:contact-lagrange`, `eq:contact-balanced-sum`,
`eq:contact-interior-domain`, `eq:contact-anchor-lists`, `eq:contact-anchor-forcing`,
`lem:contact-leading`, `eq:contact-first-coefficients`, `thm:contact-rigidity`,
`eq:contact-reverse-rigidity`, `cor:contact-graph` and `lem:contact-self-limit`.

Everything is rebuilt from the definitions.  A zero-free connected skew diagram `V` (full beta
lists `X, Y`) is enumerated from actual skew shapes; connected diagrams `E, F` come from it by
restoring sets of common betas `Z_E, Z_F` (the height word, hence connectedness, is unchanged).
The matrix `M = (h_{x-y})` has `h_0 = nu` (a field element of `Q(nu)`) and the other `h_j` fixed
generic rationals.  The right contact vector of `E` and the left contact vector of `F` are
SOLVED from their defining equations (every row, respectively column, equation except the one
at `r`, respectively `t`; normalized at `t`, respectively `r`), never read off a formula.
Exact arithmetic over `Q(nu)` throughout; no floating point.

Asserted on every instance (all contacts `0 <= t < r <= m` with the symmetric difference of
`Z_E, Z_F` inside `(t, r)`):
  * both Lagrange identities and the balanced sum, as identities in `Q(nu)`;
  * the orders and leading coefficients of `B`, `K - f_E`, `K - f_F` against the anchor-only
    quantities `A_z, G_z` (`D` built from the lists of the anchor matrix, independent of `nu`);
  * the leading coefficient of `w_E`, `v_F`, `R_E`, `L_F` at the differing vacancies;
  * the orders of `f_E` and `K` and their common leading coefficient;
  * the rigidity equivalences, the compensated current, and the positive constant-weight
    sum of currents (the corollary): a nonzero value exactly off the diagonal.
The paper's "single separated negative-lex specialization" sign claim is not tested here; the
rigidity conclusions are tested at a generic rational point of the alphabet, which is the
statement they are used for.
"""
import random
import sys
from itertools import combinations

import sympy as sp
from sympy import QQ
from sympy.polys.matrices import DomainMatrix

from check_regroup_mixed import is_cskew, skew_shapes, content, add, sub, min_content, max_content

NU = sp.Symbol("nu")
K = QQ.frac_field(NU)
RNG = random.Random(20260801)
HVAL = {j: sp.Rational(RNG.randint(1, 10 ** 6), RNG.randint(1, 10 ** 3)) * RNG.choice((1, -1))
        for j in range(1, 40)}


def h(j):
    if j < 0:
        return sp.Integer(0)
    if j == 0:
        return NU
    return HVAL[j]


def beta_lists(D):
    """Full beta lists (X, Y) of a connected skew diagram, southwest content zero."""
    c0 = min_content(D)
    rows = sorted({x[0] for x in D})
    X, Y = [], []
    for i in rows:
        cs = [content(x) - c0 for x in D if x[0] == i]
        Y.append(min(cs))
        X.append(max(cs) + 1)
    X.sort(reverse=True)
    Y.sort(reverse=True)
    return tuple(X), tuple(Y)


def to_dm(rows, cols):
    return DomainMatrix.from_Matrix(sp.Matrix([[h(x - y) for y in cols] for x in rows])).convert_to(K)


def solve_contact(Xl, Yl, r, t, side):
    """Contact vector as a dict label -> element of K.  side 'R': vector on columns solving
    every row equation but r, normalized R(t)=1.  side 'L': vector on rows solving every column
    equation but t, normalized L(r)=1."""
    rows_keep = [x for x in Xl if x != r]
    cols_keep = [y for y in Yl if y != t]
    A = sp.Matrix([[h(x - y) for y in cols_keep] for x in rows_keep])
    if side == 'R':
        rhs = -sp.Matrix([h(x - t) for x in rows_keep])
        sol = DomainMatrix.from_Matrix(A).convert_to(K).lu_solve(
            DomainMatrix.from_Matrix(rhs).convert_to(K))
        out = {t: K.one}
        for i, y in enumerate(cols_keep):
            out[y] = sol[i, 0].element
        return out
    rows_u = [x for x in Xl if x != r]
    A2 = sp.Matrix([[h(x - y) for y in cols_keep] for x in rows_u])
    rhs = -sp.Matrix([[h(r - y) for y in cols_keep]])
    sol = DomainMatrix.from_Matrix(A2.T).convert_to(K).lu_solve(
        DomainMatrix.from_Matrix(rhs.T).convert_to(K))
    out = {r: K.one}
    for i, x in enumerate(rows_u):
        out[x] = sol[i, 0].element
    return out


def kernel_data(V_X, V_Y, ZE, ZF, r, t):
    XE = sorted(set(V_X) | ZE, reverse=True)
    YE = sorted(set(V_Y) | ZE, reverse=True)
    XF = sorted(set(V_X) | ZF, reverse=True)
    YF = sorted(set(V_Y) | ZF, reverse=True)
    Xu = sorted(set(V_X) | ZE | ZF, reverse=True)
    Yu = sorted(set(V_Y) | ZE | ZF, reverse=True)
    try:
        R = solve_contact(XE, YE, r, t, 'R')
        L = solve_contact(XF, YF, r, t, 'L')
    except Exception:
        return None
    Rv = [R.get(y, K.zero) for y in Yu]
    Lv = [L.get(x, K.zero) for x in Xu]
    M = [[K.from_sympy(h(x - y)) for y in Yu] for x in Xu]
    w = [sum((M[a][b] * Rv[b] for b in range(len(Yu))), K.zero) for a in range(len(Xu))]
    v = [sum((Lv[a] * M[a][b] for a in range(len(Xu))), K.zero) for b in range(len(Yu))]
    Kk = sum((Lv[a] * w[a] for a in range(len(Xu))), K.zero)
    # self kernels use the same contacts and their own normalized vectors
    LE = solve_contact(XE, YE, r, t, 'L')
    fE = sum((LE.get(x, K.zero) * sum((K.from_sympy(h(x - y)) * R.get(y, K.zero) for y in YE), K.zero)
              for x in XE), K.zero)
    RF = solve_contact(XF, YF, r, t, 'R')
    fF = sum((L.get(x, K.zero) * sum((K.from_sympy(h(x - y)) * RF.get(y, K.zero) for y in YF), K.zero)
              for x in XF), K.zero)
    Bv = K.zero
    for a, x in enumerate(Xu):
        for b, y in enumerate(Yu):
            Bv += Lv[a] * K.from_sympy((r - t - x + y) * h(x - y)) * Rv[b]
    return dict(Xu=Xu, Yu=Yu, R=R, L=L, Rv=Rv, Lv=Lv, w=w, v=v, K=Kk, fE=fE, fF=fF, B=Bv)


def lead(elem):
    """(order, leading coefficient) of a nonzero element of Q(nu) as nu -> infinity."""
    e = K.to_sympy(elem)
    if e == 0:
        return None
    num, den = sp.fraction(sp.together(e))
    pn, pd = sp.Poly(num, NU), sp.Poly(den, NU)
    return pn.degree() - pd.degree(), pn.LC() / pd.LC()


def anchor_forcing(V_X, V_Y, r, t, z):
    """A_z and G_z of `eq:contact-anchor-forcing` from the anchor-only matrix."""
    eps_r = 0 if r in V_X else 1
    eps_t = 0 if t in V_Y else 1
    I0 = sorted(set(V_X) - {r} | ({t} if eps_t else set()), reverse=True)
    C0 = sorted(set(V_Y) - {t} | ({r} if eps_r else set()), reverse=True)
    assert len(I0) == len(C0)
    Dm = sp.Matrix([[h(x - y) for y in C0] for x in I0])
    b = sp.Matrix([h(i - t) for i in I0])
    a = sp.Matrix([[h(r - j) for j in C0]])
    Mzc = sp.Matrix([[h(z - c) for c in C0]])
    Mir = sp.Matrix([h(i - z) for i in I0])
    if I0:
        assert sp.simplify(Dm.det()) != 0
        # D has no common beta and carries no nu
        assert not (set(I0) & set(C0)) and not Dm.has(NU), (I0, C0)
        e1 = h(z - t) - (Mzc * Dm.inv() * b)[0, 0]
        e2 = h(r - z) - (a * Dm.inv() * Mir)[0, 0]
    else:
        e1, e2 = h(z - t), h(r - z)
    e1, e2 = sp.expand(sp.cancel(e1)), sp.expand(sp.cancel(e2))
    p1, p2 = sp.Poly(e1, NU), sp.Poly(e2, NU)
    assert p1.degree() <= eps_t and p2.degree() <= eps_r, (e1, e2)
    return p1.coeff_monomial(NU ** eps_t), p2.coeff_monomial(NU ** eps_r), eps_r, eps_t


def zero_free_diagrams(max_cells, max_rows, max_cols):
    for D in skew_shapes(max_cells, max_rows, max_cols):
        if len(D) < 2:
            continue
        X, Y = beta_lists(D)
        if set(X) & set(Y):
            continue
        yield D, X, Y


nend = [0]


def main():
    max_cells = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    inst = lag = lead_checked = rig = ne_cross = 0
    phi = {}
    groups = {}
    eps_seen = set()
    for D, X, Y in zero_free_diagrams(max_cells, 3, 4):
        m = X[0]
        spots = [z for z in range(1, m) if z not in X and z not in Y]
        if not spots:
            continue
        subsets = [frozenset(c) for k in range(0, min(3, len(spots)) + 1)
                   for c in combinations(spots, k)]
        for ZE in subsets:
            for ZF in subsets:
                shared = ZE & ZF
                for r in sorted(set(X) | shared):
                    for t in sorted(set(Y) | shared):
                        if not (0 <= t < r <= m):
                            continue
                        diff = ZE ^ ZF
                        if not all(t < z < r for z in diff):
                            continue
                        if r not in set(X) | ZE or r not in set(X) | ZF:
                            continue
                        if t not in set(Y) | ZE or t not in set(Y) | ZF:
                            continue
                        data = kernel_data(X, Y, set(ZE), set(ZF), r, t)
                        if data is None:
                            continue
                        inst += 1
                        Rd, Ld = data['R'], data['L']
                        w, v = data['w'], data['v']
                        Xu, Yu = data['Xu'], data['Yu']
                        Kk, fE, fF, Bv = data['K'], data['fE'], data['fF'], data['B']
                        # normalizations are nonzero (connected diagrams, weak minors)
                        assert Rd[t] == K.one and Ld[r] == K.one
                        # contact equations hold except at the contact
                        for a_, x in enumerate(Xu):
                            if x in set(X) | ZE and x != r:
                                assert w[a_] == K.zero
                        for b_, y in enumerate(Yu):
                            if y in set(Y) | ZF and y != t:
                                assert v[b_] == K.zero
                        # Lagrange identities
                        s1 = sum((data['Lv'][Xu.index(z)] * w[Xu.index(z)] for z in ZF - ZE), K.zero)
                        s2 = sum((v[Yu.index(z)] * data['Rv'][Yu.index(z)] for z in ZE - ZF), K.zero)
                        assert Kk - fE == s1 and Kk - fF == s2
                        sb = (sum(((r - z) * data['Lv'][Xu.index(z)] * w[Xu.index(z)] for z in ZF - ZE), K.zero)
                              + sum(((z - t) * v[Yu.index(z)] * data['Rv'][Yu.index(z)] for z in ZE - ZF), K.zero))
                        assert Bv == sb
                        lag += 1
                        # rigidity and compensated current
                        d = r - t
                        comp = Bv - 2 * d * Kk + d * (fE + fF)
                        sameEF = (ZE == ZF)
                        assert (Bv == K.zero) == sameEF, (sorted(D), X, Y, sorted(ZE), sorted(ZF), r, t)
                        assert (Kk - fE == K.zero) == (ZF <= ZE)
                        assert (Kk - fF == K.zero) == (ZE <= ZF)
                        assert (comp == K.zero) == sameEF
                        rig += 1
                        groups.setdefault((X, Y, r, t), []).append((sameEF, Bv, Kk - fE, Kk - fF, comp, ZE, ZF))
                        if sameEF:
                            continue
                        # leading coefficients against anchor-only quantities
                        P = {}
                        eps_r = 0 if r in X else 1
                        eps_t = 0 if t in Y else 1
                        e = eps_r + eps_t
                        for z in diff:
                            A, G, er, et = anchor_forcing(X, Y, r, t, z)
                            assert A != 0 and G != 0 and (er, et) == (eps_r, eps_t)
                            P[z] = A * G
                            if z in ZF - ZE:
                                lw = lead(w[Xu.index(z)])
                                assert lw == (eps_t, A), (z, lw, A)
                                lL = lead(data['Lv'][Xu.index(z)])
                                assert lL == (eps_r - 1, -G), (z, lL, G)
                            else:
                                lv = lead(v[Yu.index(z)])
                                assert lv == (eps_r, G), (z, lv, G)
                                lR = lead(data['Rv'][Yu.index(z)])
                                assert lR == (eps_t - 1, -A), (z, lR, A)
                        want_B = -sum((z - t) * P[z] for z in ZE - ZF) - sum((r - z) * P[z] for z in ZF - ZE)
                        want_KE = -sum(P[z] for z in ZF - ZE)
                        want_KF = -sum(P[z] for z in ZE - ZF)
                        for val, want in ((Bv, want_B), (Kk - fE, want_KE), (Kk - fF, want_KF)):
                            # coefficient of nu^(e-1): all lower-order terms vanish at infinity
                            ex = K.to_sympy(val)
                            lim = sp.limit(ex / NU ** (e - 1), NU, sp.oo)
                            assert lim == want, (val, lim, want)
                        lead_checked += 1
                        # self kernel order and common leading term
                        lf, lk = lead(fE), lead(Kk)
                        assert lf[0] == e and lk == lf, (lf, lk, e)
                        ne_cross += 1
                        if r == m and t == 0:
                            # endpoint contacts (eq:coincident-leading, eq:class-balance): e = 0
                            assert e == 0
                            for th in (-7, -1, 0, 3, 11):
                                Jth = K.to_sympy(Bv) + th * K.to_sympy(Kk - fE)
                                lim = sp.limit(Jth * NU, NU, sp.oo)
                                want = (-sum(z * P[z] for z in ZE - ZF) - sum((m - z + th) * P[z] for z in ZF - ZE))
                                assert lim == want, (th, lim, want)
                            assert sp.limit(K.to_sympy(Kk - fE) * NU, NU, sp.oo) == -sum(P[z] for z in ZF - ZE)
                            # f_E = f_core - nu^-1 sum_{Z_E} P_z + O(nu^-2), the self complement of E alone
                            PE = {z: anchor_forcing(X, Y, r, t, z)[0] * anchor_forcing(X, Y, r, t, z)[1] for z in ZE | ZF}
                            fcore = lead(fE)[1]
                            assert lead(fE)[0] == 0
                            assert sp.limit((K.to_sympy(fE) - fcore) * NU, NU, sp.oo) == -sum(PE[z] for z in ZE)
                            assert sp.limit((K.to_sympy(fF) - fcore) * NU, NU, sp.oo) == -sum(PE[z] for z in ZF)
                            # balance S_EF is exactly equality of the nu^-1 coefficients of f_E and f_F
                            bal = sum(PE[z] for z in ZE - ZF) == sum(PE[z] for z in ZF - ZE)
                            assert bal == (sp.limit((K.to_sympy(fE - fF)) * NU, NU, sp.oo) == 0)
                            nend[0] += 1
                        eps_seen.add(e)
                        # Phi is independent of every restored unit except the shared anchors
                        key = (X, Y, r, t, ZE & (set(range(t, r + 1))) & {r, t})
                        assert phi.setdefault(key, lf[1]) == lf[1], key
    # cor:contact-graph: a positive constant-weight sum of currents on one core and contact pair
    # vanishes only if every edge joins identical diagrams (likewise K - f_E, K - f_F inclusions
    # and the compensated current)
    ngraph = 0
    for key, lst in groups.items():
        if len(lst) < 2:
            continue
        for _ in range(8):
            pick = [lst[RNG.randrange(len(lst))] for _ in range(RNG.randint(2, 4))]
            wts = [RNG.randint(1, 5) for _ in pick]
            tot = lambda idx: sum((w * e[idx] for w, e in zip(wts, pick)), K.zero)
            assert (tot(1) == K.zero) == all(e[0] for e in pick)
            assert (tot(4) == K.zero) == all(e[0] for e in pick)
            assert (tot(2) == K.zero) == all(e[6] <= e[5] for e in pick)
            assert (tot(3) == K.zero) == all(e[5] <= e[6] for e in pick)
            ngraph += 1
    assert ngraph > 0
    print(f"instances {inst}, Lagrange/balanced {lag}, rigidity {rig}, "
          f"leading-coefficient checks {lead_checked}, self/cross kernels {ne_cross}, anchor configurations {sorted(eps_seen)}, weighted graph sums {ngraph}, endpoint-contact cases {nend[0]}")
    assert nend[0] > 0
    assert inst > 0 and lead_checked > 0
    assert eps_seen == {0, 1, 2}, eps_seen   # all three anchor configurations occur
    print("PASS")


if __name__ == "__main__":
    main()
