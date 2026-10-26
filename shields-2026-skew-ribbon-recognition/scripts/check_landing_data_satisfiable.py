"""Satisfiability of the landing data of the nonliteral two-copy comparison.

Paper section `sec:reduction` (Factor readout and the two-copy reduction), rt:lower-landing:
the data E = V o_mu J, U = V' o_mu J consumed by sec:comparison and app:endpoints.

The landing data asks for: a legal marked inner mu on a connected J; connected coarse factors V, V'
of equal span at least 3, equal skew Schur functions, V' not a translate of V; the chart (V, mu)
source-minimal for E = V o_mu J; and an upper width w < period(mu), w != width(mu).

This script searches small diagrams for the combinatorial part of a witness:

* every pair V, V' of connected skew diagrams in a 3 x 3 box with span >= 3, equal span, equal
  skew Schur function (compared as polynomials in |V| variables, enough to separate symmetric
  functions of that degree), and V' not a translate of V;
* for the inner, the horizontal empty mark on a two-cell connected J: period = span J = 2, width 0,
  so w = 1 satisfies 0 <= w < 2 and w != 0;
* source-minimality of (V, mu): its score is (width, span J) = (0, 2), and every connected skew
  diagram with at least two cells has span at least 2 (checked here over the box), so no proper
  chart of E has a smaller score.

It asserts that at least one witness exists, and that the smallest is V = (2,1), V' = (2,2)/(1).
"""

from itertools import product
from collections import Counter

BOX = 3


def skew_shapes(box):
    """All skew shapes lam/mu with lam inside a box x box square, as frozensets of (row, col)."""
    parts = [p for p in product(range(box + 1), repeat=box) if all(p[i] >= p[i + 1] for i in range(box - 1))]
    shapes = set()
    for lam in parts:
        for mu in parts:
            if all(mu[i] <= lam[i] for i in range(box)):
                cells = frozenset((i, j) for i in range(box) for j in range(mu[i], lam[i]))
                if cells:
                    shapes.add(normalize(cells))
    return shapes


def normalize(cells):
    r0 = min(i for i, _ in cells)
    c0 = min(j for _, j in cells)
    return frozenset((i - r0, j - c0) for i, j in cells)


def connected(cells):
    cells = set(cells)
    start = next(iter(cells))
    seen = {start}
    stack = [start]
    while stack:
        i, j = stack.pop()
        for d in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            n = (i + d[0], j + d[1])
            if n in cells and n not in seen:
                seen.add(n)
                stack.append(n)
    return len(seen) == len(cells)


def span(cells):
    return len({j - i for i, j in cells})


def schur_poly(cells, nvars):
    """Skew Schur polynomial in nvars variables: Counter of exponent vectors over the SSYT."""
    order = sorted(cells)
    result = Counter()

    def fill(k, tab):
        if k == len(order):
            exp = [0] * nvars
            for v in tab.values():
                exp[v] += 1
            result[tuple(exp)] += 1
            return
        i, j = order[k]
        lo = 0
        if (i, j - 1) in tab:
            lo = max(lo, tab[(i, j - 1)])
        if (i - 1, j) in tab:
            lo = max(lo, tab[(i - 1, j)] + 1)
        for v in range(lo, nvars):
            tab[(i, j)] = v
            fill(k + 1, tab)
            del tab[(i, j)]

    fill(0, {})
    return result


def main():
    shapes = [s for s in skew_shapes(BOX) if connected(s)]
    # every connected skew diagram with at least two cells has span at least 2
    assert all(span(s) >= 2 for s in shapes if len(s) >= 2)

    coarse = [s for s in shapes if span(s) >= 3]
    witnesses = []
    for V in coarse:
        for Vp in coarse:
            if V == Vp or len(V) != len(Vp) or span(V) != span(Vp):
                continue
            n = len(V)
            if schur_poly(V, n) == schur_poly(Vp, n):
                witnesses.append((len(V), sorted(V), sorted(Vp)))
    witnesses.sort()
    print(f"connected shapes in the {BOX}x{BOX} box: {len(shapes)}")
    print(f"coarse pairs (span >= 3, equal Schur, not translates): {len(witnesses)}")
    for w in witnesses[:6]:
        print("  ", w)

    # inner: horizontal empty mark on the horizontal domino, period 2, width 0, upper width 1
    J = frozenset({(0, 0), (0, 1)})
    period, width, w = span(J), 0, 1
    assert connected(J) and period == 2 and 0 <= w < period and w != width
    # score (0, 2) is least among proper charts, since every proper inner has span >= 2

    assert witnesses, "no landing data witness found"
    smallest = witnesses[0]
    assert smallest[0] == 3
    assert {tuple(smallest[1]), tuple(smallest[2])} == {
        ((0, 0), (0, 1), (1, 0)),
        ((0, 1), (1, 0), (1, 1)),
    }
    print("landing data witness: V = (2,1), V' = (2,2)/(1), J = row of 2, empty mark, w = 1")
    print("ALL PASS")


if __name__ == "__main__":
    main()
