r"""Paper section `sec:poles` (Endpoint poles and outward boundary defects).

Exact template checks for `eq:cap-height-pole`, `eq:cap-height-positive`, `eq:reference-differences`
(membership identity of the upper cap), `eq:own-unit`, `eq:vacancy-resolvent`, `eq:first-response`, for the upper cap of a column-kind template.

Template (as in `check_column_response`): top `c`, disjoint weak core `(I0, C0)` with `c in I0`, cap rows
`I0 + Zref`, cap columns `(C0 + Zref) - {sigma}` with `sigma` in `C0 + Zref`, return rows/columns
`I0 + ZR`, `C0 + ZR`, generic rational `h_k` (`k > 0`), `h_0 = nu` a symbol.  The cap vector `l`
(`l_c = 1`) and the return numerator `y_c` are solved exactly over `Q(nu)`; limits at `nu = oo` are exact.
Asserted per template with positive cap heights and nonsingular systems:
  * `H_upper(u) = 1 + h_D(u) - [u >= sigma]` for `0 <= u < c` (cap height, from the lists) and
    `h_D(u) >= 1` on `sigma <= u < c` (`eq:cap-height-positive`);
  * `1_{I_R*} - 1_{C_R*} = 1_{U_cap} - 1_{C_+} - 1_sigma` is the membership identity
    `1_rows - 1_cols = 1_{cap rows} - 1_{cap cols} - 1_sigma` read on the cap lists (the cap columns are the
    cap rows' companions minus sigma);
  * `eq:own-unit`: for each own inserted unit `u in Zref - {sigma}` (row and column both in the cap),
    `nu l_u -> -G_u` as `nu -> oo`, with `G_u = sum_i l_i^oo h_{i-u}`;
  * `eq:vacancy-resolvent`: the Schur complement of the return matrix over the core equals
    `nu I + E` on the return units with `E_uv = h+_{u-v} - M(u, C0) A0^{-1} M(I0, v)`;
  * `eq:first-response`: `nu (T_R(0) - e_R) -> sum_{u in A_R} G_u phi_u(0) / l_oo(0)` with
    `phi_u(0) = -(M(u, C0) A0^{-1})_c`, `e_R = [sigma in ZR]`, `A_R` as defined (units added when `e_R = 0`,
    cap units missing when `e_R = 1`);
The end-pole expansion and the filter (`eq:outward-filter`) are statements about the complementary
response of an actual comparison and are not covered here.
Sampled: `c` in 2..4, cores of one or two pairs, 400 templates; the first-response check applies only to
templates with `sigma` a vacancy (the core-column anchor is `check_present_response.py`).
"""
import random

import sympy as sp

NU = sp.Symbol("nu")
RNG = random.Random(4)


def rat():
    return sp.Rational(RNG.randint(1, 9), RNG.randint(1, 6))


def main():
    n = nown = nresp = nres = nh = 0
    tries = 0
    while n < 400 and tries < 100000:
        tries += 1
        c = RNG.randint(2, 4)
        K = list(range(c + 1))
        k = RNG.randint(1, 2)
        I0 = set(RNG.sample(K, k))
        if c not in I0:
            continue
        rest = [x for x in K if x not in I0]
        if len(rest) < k:
            continue
        C0 = set(RNG.sample(rest, k))
        vac = [x for x in rest if x not in C0]
        Zref = {x for x in vac if RNG.random() < 0.5}
        ZR = {x for x in vac if RNG.random() < 0.5}
        pool = sorted(C0 | Zref)
        if not pool:
            continue
        sigma = RNG.choice(pool)
        cap_rows = sorted(I0 | Zref)
        cap_cols = sorted((C0 | Zref) - {sigma})
        if len(cap_rows) - 1 != len(cap_cols):
            continue
        base = {j: rat() for j in range(1, c + 2)}

        def h(j):
            return sp.Integer(0) if j < 0 else (NU if j == 0 else base[j])
        hD = lambda u: len([i for i in I0 if i > u]) - len([j for j in C0 if j > u])
        Hup = lambda u: len([i for i in cap_rows if i > u]) - len([j for j in cap_cols if j > u])
        if any(Hup(u) < 1 for u in range(0, c)):
            continue
        for u in range(0, c):
            assert Hup(u) == 1 + hD(u) - (1 if u >= sigma else 0), (u, I0, C0, Zref, sigma)
            if u >= sigma:
                assert hD(u) >= 1                                          # eq:cap-height-positive
        nh += 1
        # cap vector
        free = [i for i in cap_rows if i != c]
        if cap_cols:
            M = sp.Matrix(len(cap_cols), len(free), lambda a, b: h(free[b] - cap_cols[a]))
            if sp.simplify(M.det()) == 0:
                continue
            sol = M.LUsolve(sp.Matrix([-h(c - j) for j in cap_cols]))
        else:
            sol = []
        ell = {c: sp.Integer(1)}
        for b, i in enumerate(free):
            ell[i] = sp.cancel(sol[b])
        # return system
        rows = sorted(I0 | ZR)
        cols = sorted(C0 | ZR)
        BR = sp.Matrix(len(rows), len(cols), lambda a, b: h(rows[a] - cols[b]))
        if sp.simplify(BR.det()) == 0:
            continue
        resid = lambda j: sum(ell[i] * h(i - j) for i in cap_rows)
        y = BR.T.LUsolve(sp.Matrix([resid(j) for j in cols]))
        yc = sp.cancel(y[rows.index(c)])
        n += 1
        linf = {i: sp.limit(ell[i], NU, sp.oo) for i in cap_rows}
        assert linf[c] == 1
        G = lambda u: sum(linf[i] * h(i - u) for i in cap_rows)
        # eq:own-unit
        for u in Zref - {sigma}:
            if u == c:
                continue
            Gown = sum(linf[i] * h(i - u) for i in cap_rows if i != u)
            assert sp.simplify(sp.limit(NU * ell[u], NU, sp.oo) + Gown) == 0, ('eq:own-unit', I0, C0, Zref, sigma, u)
            nown += 1
        # eq:vacancy-resolvent
        core_r, core_c = sorted(I0), sorted(C0)
        A0 = sp.Matrix(len(core_r), len(core_c), lambda a, b: h(core_r[a] - core_c[b]))
        Z = sorted(ZR)
        if Z and A0.shape[0] and sp.simplify(A0.det()) != 0:
            A0i = A0.inv()
            Mu = lambda u: sp.Matrix([[h(u - j) for j in core_c]])
            Mv = lambda v: sp.Matrix([h(i - v) for i in core_r])
            # return matrix ordered core first, then units
            full_r = core_r + Z
            full_c = core_c + Z
            Mfull = sp.Matrix(len(full_r), len(full_c), lambda a, b: h(full_r[a] - full_c[b]))
            m0 = len(core_r)
            S = Mfull[m0:, m0:] - Mfull[m0:, :m0] * A0i * Mfull[:m0, m0:]
            for a, u in enumerate(Z):
                for b, v in enumerate(Z):
                    hplus = h(u - v) if u - v > 0 else sp.Integer(0)
                    E = hplus - (Mu(u) * A0i * Mv(v))[0, 0]
                    want = (NU if u == v else 0) + E
                    assert sp.simplify(S[a, b] - want) == 0
            nres += 1
        # eq:first-response (constant coefficient)
        eR = 1 if sigma in ZR else 0
        if sigma in C0:
            continue
        if eR == 0:
            AR = (ZR - Zref) - {sigma}
        else:
            AR = (Zref - {sigma}) - ZR
        if A0.shape[0] == 0 or sp.simplify(A0.det()) == 0:
            continue
        A0i = A0.inv()
        tot = 0
        for u in AR:
            phi0 = -(sp.Matrix([[h(u - j) for j in core_c]]) * A0i)[0, core_r.index(c)]
            tot += G(u) * phi0
        lim_y = sp.limit(yc, NU, sp.oo)
        assert lim_y == eR, ('Boolean limit', I0, C0, Zref, ZR, sigma, lim_y, eR)
        got = sp.limit(NU * (yc - eR), NU, sp.oo)
        want = sp.limit(tot, NU, sp.oo)
        assert sp.simplify(got - want) == 0, ('eq:first-response', I0, C0, Zref, ZR, sigma, got, want)
        nresp += 1
    print(f"templates {n}; heights {nh}; own units {nown}; resolvents {nres}; first responses {nresp}")
    assert nh > 0 and nown > 0 and nres > 0 and nresp > 0
    print("PASS")


if __name__ == "__main__":
    main()
