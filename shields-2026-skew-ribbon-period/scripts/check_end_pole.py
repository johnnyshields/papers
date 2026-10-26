r"""Paper section `sec:poles` (Endpoint poles and outward boundary defects): `eq:end-pole-expansion`,
`eq:cap-pole-regular`, `eq:local-pole-data`.

The end-pole expansion is an exact statement about the cap and return templates; the main
theorem's comparison enters only through the filter that consumes it, so the expansion itself is
tested on templates built backwards from the paper's data (as in `check_cap_template.py`): top
`c` (2..5), a disjoint weak core `(I0, C0)` of one to three pairs with `c in I0`, reference
vacancies `Zref`, return units `ZR`, an upper active index `sigma` that is a vacancy in `Zref`
(the proper-core-column and bottom-column anchors are not sampled), generic rational `h_k`,
`h_0 = nu` symbolic.  The highest positive component of the core has support `[b, c)` with local
flags `(s, I_D)/(C_D, 0)`, `s = c - b`, local labels shifted by `-b`.  Exactly, over `Q(nu)`:

  * `[nu^{-1}]_infty t_R`, with `t_R = [z^0] T_R` the coefficient of the top cap row in the return
    solve, equals `sum_{u in A_R, b < u < c} G_u phi_u(0)` (the lemma `lem:first-response` term,
    restricted to the highest component: the summands with `u` outside `(b, c)` vanish);
  * with `f_z, g_z, F_D, P_z = f_z g_z` of `eq:local-pole-data` on the local component and
    `U_z = k(sigma, z)/f_sigma` for a vacancy `sigma`, `k(u, z) = h_{u-z} - M(u, C) K^{-1} M(I, z)`:
    `G_u = g_z - F_D U_z` at `z = u - b` (`eq:cap-pole-regular`), and `phi_u(0) = -f_z / F_D`;
  * consequently `[nu^{-1}]_infty t_R = -S_R^end / F_{D_R} + R_R` with `S_R^end = sum P_z` and
    `R_R = sum f_z U_z` over `u in A_R` with `b < u < c`.
Control: replacing `U_z` by zero (the bottom-column value) breaks the last identity on every
instance whose regular sum is nonzero.

Uncovered: the lower side (dual, not rebuilt), the two anchors `sigma` a proper core column or
the bottom core column, the positivity of the residue numerators (`lem:local-forcing`), and the
filter `thm:end-filter` itself.
"""
import random

import sympy as sp

NU = sp.Symbol("nu")
RNG = random.Random(17)


def rat():
    return sp.Rational(RNG.randint(1, 9), RNG.randint(1, 6))


def main():
    n = interior = nonzero_regular = broken = 0
    tries = 0
    while n < 150 and tries < 400000:
        tries += 1
        c = RNG.randint(2, 5)
        K = list(range(c + 1))
        k = RNG.randint(1, 3)
        I0 = set(RNG.sample(K, k))
        if c not in I0:
            continue
        rest = [x for x in K if x not in I0]
        if len(rest) < k:
            continue
        C0 = set(RNG.sample(rest, k))
        vac = [x for x in rest if x not in C0]
        Zref = {x for x in vac if RNG.random() < 0.6}
        ZR = {x for x in vac if RNG.random() < 0.5}
        if not Zref:
            continue
        sigma = RNG.choice(sorted(Zref))
        hD = lambda u: len([i for i in I0 if i > u]) - len([j for j in C0 if j > u])
        if any(hD(u) < 0 for u in range(c)):
            continue
        cap_rows = sorted(I0 | Zref)
        cap_cols = sorted((C0 | Zref) - {sigma})
        if len(cap_rows) - 1 != len(cap_cols):
            continue
        Hup = lambda u: len([i for i in cap_rows if i > u]) - len([j for j in cap_cols if j > u])
        if any(Hup(u) < 1 for u in range(0, c)):
            continue
        # highest positive component [b, c)
        b = c
        while b - 1 >= 0 and hD(b - 1) > 0:
            b -= 1
        if b == c or sigma < b:
            continue
        base = {j: rat() for j in range(1, c + 2)}

        def h(j):
            return sp.Integer(0) if j < 0 else (NU if j == 0 else base[j])
        free = [i for i in cap_rows if i != c]
        if cap_cols:
            M = sp.Matrix(len(cap_cols), len(free), lambda a, bb: h(free[bb] - cap_cols[a]))
            if sp.simplify(M.det()) == 0:
                continue
            sol = M.LUsolve(sp.Matrix([-h(c - j) for j in cap_cols]))
        else:
            sol = []
        ell = {c: sp.Integer(1)}
        for bb, i in enumerate(free):
            ell[i] = sp.cancel(sol[bb])
        rows = sorted(I0 | ZR)
        cols = sorted(C0 | ZR)
        BR = sp.Matrix(len(rows), len(cols), lambda a, bb: h(rows[a] - cols[bb]))
        if sp.simplify(BR.det()) == 0:
            continue
        resid = lambda j: sum(ell[i] * h(i - j) for i in cap_rows)
        y = BR.T.LUsolve(sp.Matrix([resid(j) for j in cols]))
        tR = sp.cancel(y[rows.index(c)])
        eR = 1 if sigma in ZR else 0
        linf = {i: sp.limit(ell[i], NU, sp.oo) for i in cap_rows}
        if not all(v.is_finite for v in linf.values()):
            continue
        G = lambda u: sum(linf[i] * h(i - u) for i in cap_rows)
        core_r, core_c = sorted(I0), sorted(C0)
        A0 = sp.Matrix(len(core_r), len(core_c), lambda a, bb: h(core_r[a] - core_c[bb]))
        if A0.shape[0] == 0 or sp.simplify(A0.det()) == 0:
            continue
        A0i = A0.inv()
        AR = ((ZR - Zref) - {sigma}) if eR == 0 else ((Zref - {sigma}) - ZR)
        # local component data (labels shifted by -b), top s = c - b
        s = c - b
        ID = sorted((i - b for i in I0 if b <= i < c), reverse=True)
        CD = sorted((j - b for j in C0 if b <= j < c), reverse=True)
        assert CD and CD[-1] == 0
        Kloc = sp.Matrix(len(ID), len(CD) - 1, lambda a, bb: h(ID[a] - CD[bb]))
        cols_proper = CD[:-1]
        if len(ID) != len(cols_proper):
            continue
        if ID:
            Ki = Kloc.inv()
            bvec = sp.Matrix([h(i) for i in ID])
            a0 = sp.Matrix([[h(s - j) for j in cols_proper]])
            omega = (a0 * Ki * bvec)[0, 0]
        else:
            Ki = sp.zeros(0, 0)
            omega = sp.Integer(0)
        FD = h(s) - omega

        def f_(z):
            return h(z) - ((sp.Matrix([[h(z - j) for j in cols_proper]]) * Ki * bvec)[0, 0] if ID else 0)

        def g_(z):
            return h(s - z) - ((a0 * Ki * sp.Matrix([h(i - z) for i in ID]))[0, 0] if ID else 0)

        def kk(u, z):
            return h(u - z) - ((sp.Matrix([[h(u - j) for j in cols_proper]]) * Ki
                                * sp.Matrix([h(i - z) for i in ID]))[0, 0] if ID else 0)
        ssig = sigma - b
        if ssig <= 0 or ssig >= s:
            continue
        if sp.simplify(f_(ssig)) == 0:
            continue
        U = lambda z: kk(ssig, z) / f_(ssig)
        S = R = 0
        got_terms = 0
        for u in sorted(AR):
            phi0 = -(sp.Matrix([[h(u - j) for j in core_c]]) * A0i)[0, core_r.index(c)]
            if not (b < u < c):
                assert sp.simplify(phi0) == 0, ('component support', u, b, c)
                continue
            z = u - b
            assert sp.simplify(phi0 + f_(z) / FD) == 0, ('phi', I0, C0, u)
            assert sp.simplify(G(u) - (g_(z) - FD * U(z))) == 0, ('eq:cap-pole-regular', I0, C0, u)
            S += f_(z) * g_(z)
            R += f_(z) * U(z)
            got_terms += 1
        lhs = sp.limit(NU * (tR - eR), NU, sp.oo)
        total = sum(G(u) * (-(sp.Matrix([[h(u - j) for j in core_c]]) * A0i)[0, core_r.index(c)])
                    for u in AR if b < u < c)
        assert sp.simplify(lhs - sp.limit(total, NU, sp.oo)) == 0, ('first response on (b, c)', I0, C0)
        want = sp.limit(-S / FD + R, NU, sp.oo)
        assert sp.simplify(lhs - want) == 0, ('eq:end-pole-expansion', I0, C0, Zref, ZR, sigma)
        n += 1
        if got_terms:
            interior += 1
            if sp.simplify(sp.limit(R, NU, sp.oo)) != 0:
                nonzero_regular += 1
                if sp.simplify(sp.limit(-S / FD, NU, sp.oo) - lhs) != 0:
                    broken += 1
    print(f'templates {n}; with an index in (b, c): {interior}; nonzero regular part {nonzero_regular}; '
          f'dropping U breaks {broken}')
    assert n > 20 and interior > 5
    print('ALL PASS')


if __name__ == '__main__':
    main()
