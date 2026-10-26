r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

The list-level end windows of the empty source section (`lem:conormal-caps`,
`prop:noncell-realization`, `eq:empty-section`): when the source is the empty-mark composite
E = J o_eta U (case (a) copies `content(d) v + d_1 e`, e = (1, 1)) of a connected skew J of span R
with the connected inner U of period q = span U, the entries of the upper list X_E strictly
between 0 and q lie in X_U, and the lower list Y_U lies in Y_E.  These are the two inclusions
`EndWindowLists` (SkewRibbonPeriod/Aligned/LiftSection/SectionAssemble.lean) asks of the actual
source, and the script asserts them, together with the residue-class statement used to build
the section diagram (the entries of X_E, Y_E divisible by q are q times the lists of J).
Sampled: random inners U of 1 to 4 rows and random connected J of span at least 2 (seeded).

These are checks on supplied empty composites.  They do not construct the original aligned
comparison, verify source minimality, or establish the fresh-minimum quotient recursion.
The window predicates checked here are the stated list inclusions, not an additional claim
of complete physical-window reconstruction.
"""
import random

from check_row_probe_caps import (betas, connected, content, is_skew, legal_marks, normalize,
                                  random_skew)


def compose(J, U, v):
    cells = set()
    for (i, j) in J:
        c = j - i
        o = (c * v[0] + i, c * v[1] + i)
        for (a, b) in U:
            cells.add((a + o[0], b + o[1]))
    return normalize(cells)


def main():
    rng = random.Random(7)
    tested = 0
    seen = set()
    for _ in range(6000):
        U = random_skew(rng, rng.randint(1, 4))
        if U in seen or not is_skew(U) or not connected(U) or not 2 <= len(U) <= 9:
            continue
        seen.add(U)
        for w, v, ph in legal_marks(U):
            if w != 0:
                continue
            xU, zU = betas(U)
            q = xU[0]
            X_U, Y_U = set(xU), set(zU)
            for _ in range(6):
                J = random_skew(rng, rng.randint(1, 3))
                if not is_skew(J) or not connected(J):
                    continue
                xJ, zJ = betas(J)
                R = xJ[0]
                if R < 2:
                    continue
                E = compose(J, U, v)
                if not is_skew(E) or not connected(E):
                    continue
                xE, zE = betas(E)
                if xE[0] != R * q:
                    continue
                X_E, Y_E = set(xE), set(zE)
                assert all(x in X_U for x in X_E if 0 < x < q), (U, J, v)
                assert Y_U <= Y_E, (U, J, v)
                assert {x // q for x in X_E if x % q == 0} == set(xJ), (U, J, v)
                assert {y // q for y in Y_E if y % q == 0} == set(zJ), (U, J, v)
                tested += 1
    assert tested > 50, tested
    print("tested", tested, "composites: end windows and residue class OK")


if __name__ == "__main__":
    main()
