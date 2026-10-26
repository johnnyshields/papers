r"""Paper section `app:coincident` (Positive coincident attachment phases).

The block split of the top component behind the seam form (`app:coincident`, "The whole
marked-band determinant", `eq:marked-floor`, `eq:weighted-seam-ribbon`; `TopSeamForm` in
`lean/SkewRibbonPeriod/Reduction/ClassTopSeam.lean`, `det_seamBlock` in
`lean/SkewRibbonPeriod/Reduction/SeamDet.lean`).

For a diagram of span `L g + u` with `P(g, u)` heights and one span-`u` interior component on each
internal band, with row betas `X` and column betas `Y` (least column beta `0`):

* the top degree `sum floor(X / g) - sum floor(Y / g)` is `L`;
* each internal band `1 <= a < L` has as many marked rows (betas in `[a g, a g + u]`) as marked
  columns, a row `a g + u` and a column `a g`;
* the bottom cap (betas in `[0, u]`) has one column more than rows, and carries the column `0`;
  the top cap (betas in `[L g, L g + u]`) has one row more than columns, and carries the row
  `L g + u`;
* the two cap minors (bottom cap without the column `0`, top cap without the row `L g + u`) and
  every private band block are nonzero.

Then the marked matrix splits into the bottom cap minor, the seam block and the top cap minor,
and the top component is a nonzero `x`-free factor times the seam block determinant
`prod det D_a * W_L(x; q)` with `q_a = (D_a^{-1})_{k_a, j_a}`, which is asserted on the full
matrix as well.
"""

import itertools

import sympy as sp

from check_band_single_component import components, interior
from check_chart_witnesses import flags
from check_regroup_mixed import content, min_content, skew_shapes
from check_top_seam_form import H, heights_ok, seam


def hval(d):
    return H.get(d, 0) if d >= 0 else 0


def jt_lists(X, Y):
    return sp.Matrix([[hval(x - y) for y in Y] for x in X]).det()


def check(S, g, u):
    L = heights_ok(S, g, u)
    if L is None or L < 2:
        return False
    c0 = min_content(S)
    comps = components(interior(S))
    for i in range(1, L):
        lo, hi = c0 + i * g, c0 + i * g + u - 1
        inside = [C for C in comps if all(lo <= content(x) <= hi for x in C)]
        if len(inside) != 1 or len({content(x) for x in inside[0]}) != u:
            return False
    X, Y, span = flags(S)
    assert min(Y) == 0 and span == L * g + u
    assert sum(x // g for x in X) - sum(y // g for y in Y) == L, (sorted(S), g, u)
    band = lambda b, a: a * g <= b <= a * g + u
    for a in range(1, L):
        R = [x for x in X if band(x, a)]
        C = [y for y in Y if band(y, a)]
        assert len(R) == len(C) and a * g + u in R and a * g in C, (sorted(S), g, u, a)
    R0 = [x for x in X if band(x, 0)]
    C0 = [y for y in Y if band(y, 0)]
    assert len(C0) == len(R0) + 1 and 0 in C0
    RL = [x for x in X if band(x, L)]
    CL = [y for y in Y if band(y, L)]
    assert len(RL) == len(CL) + 1 and L * g + u in RL
    assert jt_lists(sorted(R0, reverse=True), sorted([y for y in C0 if y != 0], reverse=True)) != 0
    assert jt_lists(sorted([x for x in RL if x != L * g + u], reverse=True),
                    sorted(CL, reverse=True)) != 0
    for a in range(L):
        Rp = [x for x in X if x // g == a and x % g > u]
        Cp = [y for y in Y if y // g == a and y % g > u]
        assert len(Rp) == len(Cp)
        assert jt_lists(sorted(Rp, reverse=True), sorted(Cp, reverse=True)) != 0
    # the seam block: internal marked rows plus the row L g + u, internal marked columns plus 0
    xs = sp.symbols(f"x0:{L + 1}")

    def topE(b, c):
        if b < c or b % g < c % g:
            return 0
        d = b - c
        if d == 0:
            return 1
        if d < g:
            return H[d]
        return xs[d // g] if d % g == u else 0

    Rs = [x for a in range(1, L) for x in sorted(X) if band(x, a)] + [L * g + u]
    Cs = [0] + [y for a in range(1, L) for y in sorted(Y) if band(y, a)]
    seamdet = sp.expand(sp.Matrix([[topE(b, c) for c in Cs] for b in Rs]).det())
    q, prod = {}, 1
    for a in range(1, L):
        R = sorted(x for x in X if band(x, a))
        C = sorted(y for y in Y if band(y, a))
        Da = sp.Matrix([[topE(b, c) for c in C] for b in R])
        prod *= Da.det()
        q[a] = Da.inv()[C.index(a * g), R.index(a * g + u)]
    assert sp.simplify(seamdet - (-1) ** (len(Rs) - 1) * prod * seam(xs, q, L)) == 0 or \
        sp.simplify(seamdet + (-1) ** (len(Rs) - 1) * prod * seam(xs, q, L)) == 0
    full = sp.expand(sp.Matrix([[topE(b, c) for c in sorted(Y)] for b in sorted(X)]).det())
    ratio = sp.simplify(full / seamdet)
    assert ratio != 0 and not (ratio.free_symbols & set(xs)), (sorted(S), g, u)
    return True


def main():
    generic = 0
    for X in skew_shapes(13, 5, 7):
        for g in range(3, 7):
            for u in range(2, g):
                if check(X, g, u):
                    generic += 1
    print(f"qualifying diagrams in the box: {generic}")
    assert generic > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
