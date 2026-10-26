r"""Paper section `app:aligned` (`prop:noncell-realization`, `eq:empty-section`): substitute source.

The empty-mark section annihilates the source only through its Schur function.  For E in the
Schur class of a composite E0 = J o_eta U, let J' be the section diagram of E (beta lists = the
residue class 0 mod q of the lists of E divided by q, common betas restored) and E' = J' o_eta U
the literal composite.  The script tests s_{E'} = s_E, where E' has the end windows of U for free,
and reports the smallest counterexample.
"""
import random
import sys

from check_common_betas_original import schur, shapes_c, span, nrows, rowmap
from check_end_window_lists import compose
from check_end_window_transport import empty_v
from check_row_probe_caps import betas, connected, is_skew, normalize, random_skew


def from_lists(xi, ze):
    cells = set()
    for r, (x, z) in enumerate(zip(xi, ze)):
        for j in range(z + r, x + r):
            cells.add((r, j))
    return normalize(cells)


def section_diagram(E, q):
    X, Y = betas(E)
    xs = sorted({x // q for x in X if x % q == 0}, reverse=True)
    ys = sorted({y // q for y in Y if y % q == 0}, reverse=True)
    if len(xs) != len(ys) or not xs:
        return None
    J = from_lists(xs, ys)
    if not J or not (is_skew(J) and connected(J)):
        return None
    return J


def main():
    amax = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    rng = random.Random(11)
    seen = set()
    inner_pool = [s for A in range(2, 7) for s in shapes_c(A) if empty_v(s) is not None]
    tested = bad = nojp = withz = same = rotsame = 0
    worst = None
    for _ in range(int(sys.argv[2]) if len(sys.argv) > 2 else 3000):
        U = rng.choice(inner_pool)
        J = random_skew(rng, rng.randint(1, 3))
        if not (is_skew(J) and connected(J)):
            continue
        R, q = span(J), span(U)
        if R < 2 or q < 2:
            continue
        v = empty_v(U)
        E0 = compose(J, U, v)
        A = len(E0)
        if A > amax or not (is_skew(E0) and connected(E0)) or span(E0) != R * q:
            continue
        if (E0, U) in seen:
            continue
        seen.add((E0, U))
        key = schur(E0)
        for E in shapes_c(A, nrows(E0)):
            if span(E) != R * q or schur(E) != key:
                continue
            tested += 1
            Jp = section_diagram(E, q)
            if Jp is None or span(Jp) != R:
                nojp += 1
                continue
            X, Y = betas(E)
            withz += bool(set(X) & set(Y) & {x for x in X if x % q == 0})
            Ep = compose(Jp, U, v)
            same += Ep == E
            rotsame += Ep == normalize({(-a, -b) for (a, b) in E})
            if schur(Ep) != key:
                bad += 1
                if worst is None or len(E) < len(worst[0]):
                    worst = (E, U, Jp, Ep)
    print("classes", len(seen), "tested", tested, "no section diagram", nojp,
          "with residue common betas", withz, "E'=E", same, "E'=rot E", rotsame, "schur(E') != schur(E):", bad)
    if worst:
        E, U, Jp, Ep = worst
        print("smallest counterexample E", sorted(E), "U", sorted(U), "J'", sorted(Jp), "E'", sorted(Ep))
    assert tested > 50
    assert bad == 0


if __name__ == "__main__":
    main()
