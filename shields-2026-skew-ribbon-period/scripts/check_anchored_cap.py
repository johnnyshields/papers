r"""Paper section `sec:poles` (Endpoint poles and outward boundary defects).

Anchored cap vector: limit and unit asymptotics.

Checks, for the three anchor kinds of the upper cap (vacancy row, vacancy column, proper core
column, bottom column) on small weak cores, the statements used in `lem:first-response`,
`lem:local-forcing` and `eq:cap-pole-regular` of `shields-2026-skew-ribbon-period.tex`
(section `sec:poles`):

  * the anchored cap vector (l_c = 1, annihilating the cap columns) is the unanchored cap
    vector of a modified core: vacancy anchor (I0 - c + sigma, C0), core-column anchor
    (I0 - c, C0 - sigma); its limit l_inf on the core rows is -h_{c - C'} A'^{-1};
  * on a unit u with its own column, nu * l_u -> -G_u, G_u = h_{c-u} + sum l_inf_i h_{i-u};
  * G vanishes on the cap core columns.
"""
import random
import sympy as sp

nu = sp.symbols("nu")


def run(c, I0, C0, Z, sigma, kind, seed):
    rnd = random.Random(seed)
    hv = {j: sp.Rational(rnd.randint(2, 9), rnd.randint(1, 5)) for j in range(1, c + 2)}

    def h(j):
        return nu if j == 0 else (hv[j] if j > 0 else 0)

    if kind == "row":
        rows = sorted(set(I0) | set(Z) | {sigma})
        cols = sorted(set(C0) | set(Z))
        core = sorted((set(I0) - {c}) | {sigma})
        ccore = sorted(C0)
    elif kind == "vacancy_col":
        rows = sorted(set(I0) | set(Z))
        cols = sorted((set(C0) | set(Z)) - {sigma})
        Zu = sorted(set(Z) - {sigma})
        core = sorted((set(I0) - {c}) | {sigma})
        ccore = sorted(C0)
        Z = Zu
    else:
        rows = sorted(set(I0) | set(Z))
        cols = sorted((set(C0) | set(Z)) - {sigma})
        core = sorted(set(I0) - {c})
        ccore = sorted(set(C0) - {sigma})
    unk = [r for r in rows if r != c]
    assert len(unk) == len(cols), (kind, unk, cols)
    M = sp.Matrix(len(unk), len(cols), lambda a, b: h(unk[a] - cols[b]))
    rhs = sp.Matrix([-h(c - j) for j in cols])
    ell = sp.simplify(M.T.LUsolve(rhs))
    lim = {r: sp.limit(ell[k], nu, sp.oo) for k, r in enumerate(unk)}
    # the limit vanishes on the units and equals -h_{c-C'} A'^{-1} on the core rows
    for r in unk:
        if r not in core:
            assert lim[r] == 0, (kind, r, lim[r])
    A = sp.Matrix(len(core), len(ccore), lambda a, b: hv.get(core[a] - ccore[b], 0)
                  if core[a] != ccore[b] else 0)
    assert A.shape[0] == A.shape[1]
    assert A.det() != 0
    pred = sp.Matrix([[-hv.get(c - j, 0) for j in ccore]]) * A.inv()
    for k, r in enumerate(core):
        assert sp.simplify(lim[r] - pred[0, k]) == 0, (kind, r)

    def G(u):
        return h(c - u) + sum(lim[r] * h(r - u) for r in core)

    for j in ccore:
        assert sp.simplify(G(j)) == 0, (kind, "core cap column", j)
    for u in Z:
        k = unk.index(u)
        val = sp.limit(nu * ell[k], nu, sp.oo)
        assert sp.simplify(val + G(u)) == 0, (kind, "unit", u, val, G(u))
    return True


cases = [
    (5, [5, 2], [0, 1], [4], 3, "row"),
    (5, [5, 2], [0, 1], [], 3, "row"),
    (5, [5, 2], [0, 1], [3, 4], 3, "vacancy_col"),
    (5, [5, 2], [0, 1], [4], 1, "column"),
    (5, [5, 2], [0, 1], [3, 4], 0, "column"),
    (6, [6, 4, 2], [0, 1, 3], [5], 1, "column"),
    (6, [6, 4, 2], [0, 1, 3], [5], 3, "column"),
]
for k, case in enumerate(cases):
    run(*case, seed=k)
    print("ok", case)
print("ALL PASS")
