r"""Paper section `app:coincident` (Positive coincident attachment phases).

The seam form of the top component of a periodic source (`app:coincident`, "The whole
marked-band determinant", `eq:marked-floor`, `eq:weighted-seam-ribbon`; `TopSeamForm` in
`lean/SkewRibbonPeriod/Reduction/ClassTopSeam.lean`).

For a diagram `S` of span `L g + u` with `P(g, u)` heights and one interior component `B_i` of span
`u` on each internal band `0 < i < L`, give `h_j` the weight `floor(j / g)`, take the weight-`L`
part of `s_S`, keep every low variable `h_m` (`m < g`), send `h_{j g + u}` to `x_j` and every other
high variable to `0`.  The claim: the result is `Phi * W_L(x; q)`, with `Phi` free of `x`,
nonzero, and the port of cut `i` the ratio `q_i = (d s_{B_i} / d h_u) / s_{B_i}` of the interior
component.  Checked on coincident case-(a) composites over row outers, with `g` the period of the
mark.  The orientation of the cuts does not matter: `W_L` is invariant under `i -> L - i`, which
is asserted as well.  Swept again over every connected skew diagram of at most 13 cells in a
5 x 7 box, at every `3 <= g <= 6`, `2 <= u < g` where it qualifies.
"""

import itertools

import sympy as sp

from check_band_single_component import components, interior
from check_chart_witnesses import flags
from check_line_charge import phases
from check_regroup_mixed import content, legal_marks, min_content, skew_shapes

DEG = 40
H = {0: sp.Integer(1)}
H.update({j: sp.Symbol(f"h{j}") for j in range(1, DEG + 1)})


def row(m):
    return frozenset((0, j) for j in range(m))


def jt(cells):
    X, Y, _ = flags(cells)
    return sp.expand(sp.Matrix([[H.get(x - y, 0) if x - y >= 0 else 0 for y in Y]
                                for x in X]).det())


def seam(x, q, L):
    tot = 0
    for r in range(L):
        for T in itertools.combinations(range(1, L), r):
            cuts = [0, *T, L]
            term = sp.Integer((-1) ** len(T))
            for t in T:
                term *= q[t]
            for a, b in zip(cuts, cuts[1:]):
                term *= x[b - a]
            tot += term
    return tot


def heights_ok(S, g, u):
    c0 = min_content(S)
    span = len({content(x) for x in S})
    L, rem = divmod(span - u, g)
    if rem or L < 1:
        return None
    ht = lambda k: sum(1 for x in S if content(x) == c0 + k)
    for k in range(u + 1, L * g - g):
        if ht(k + g) != ht(k):
            return None
    for j in range(L):
        if ht(u + j * g) != 1 or ht((j + 1) * g - 1) != 1:
            return None
    return L


def check(S, g, u):
    L = heights_ok(S, g, u)
    if L is None or L < 2:
        return False
    c0 = min_content(S)
    comps = components(interior(S))
    B = {}
    for i in range(1, L):
        lo, hi = c0 + i * g, c0 + i * g + u - 1
        inside = [C for C in comps if all(lo <= content(x) <= hi for x in C)]
        if len(inside) != 1 or len({content(x) for x in inside[0]}) != u:
            return False
        B[i] = inside[0]
    s = sp.Poly(jt(S), *[H[j] for j in range(1, DEG + 1)])
    top = 0
    for mon, coeff in s.terms():
        if sum(e * ((j + 1) // g) for j, e in enumerate(mon)) == L:
            top += coeff * sp.Mul(*[H[j + 1] ** e for j, e in enumerate(mon)])
    xs = sp.symbols(f"x0:{L + 1}")
    sub = {}
    for j in range(g, DEG + 1):
        sub[H[j]] = xs[j // g] if j % g == u and j // g <= L else 0
    top = sp.expand(top.subs(sub))
    q = {}
    for i, C in B.items():
        sB = jt(C)
        q[i] = sp.diff(sB, H[u]) / sB
    W = seam(xs, q, L)
    Wrev = seam(xs, {i: q[L - i] for i in q}, L)
    assert sp.simplify(W - Wrev) == 0
    Phi = sp.expand(top).coeff(xs[L], 1)
    Phi = Phi.subs({x: 0 for x in xs})
    assert Phi != 0, (sorted(S), g, u)
    assert sp.simplify(top - Phi * W) == 0, (sorted(S), g, u)
    return True


def main():
    cases = 0
    for E in skew_shapes(8, 4, 5):
        for om in legal_marks(E):
            if om.case != 'a':
                continue
            u = om.width()
            s, t = phases(om)
            if not (s == t and 0 < s < u and u >= 2):
                continue
            g = om.period()
            for m in (2, 3):
                S = om.compose(row(m))
                if check(S, g, u):
                    cases += 1
    print(f"periodic sources checked: {cases}")
    assert cases > 0
    # every connected skew diagram in a box, at every (g, u) where it qualifies: the statement is
    # about one diagram, so the counterpart shapes (wide marks, column outers) are covered too
    generic = 0
    for X in skew_shapes(13, 5, 7):
        for g in range(3, 7):
            for u in range(2, g):
                if check(X, g, u):
                    generic += 1
    print(f"qualifying diagrams in the box: {generic}")
    assert generic > cases
    print("ALL PASS")


if __name__ == "__main__":
    main()
