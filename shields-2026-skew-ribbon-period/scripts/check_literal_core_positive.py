r"""Paper label `lem:lower-full` (source-minimal domination: Cl(G) = F(omega, s_A) for every source-minimal chart).

Source-minimality of the survivors of check_literal_core.py at area 16.

Score of a chart is (width of the mark, span of the inner) in the lexicographic order
(Chart.score in the Lean tree).  A positive-width chart has width >= 1 > 0, so it never beats an
empty-mark chart; whether (J, eta) with eta the empty mark of U is source-minimal is therefore
decided by the empty-mark charts of G alone: no empty-mark chart of G may have an inner of span
below N_U.  This script (1) recomputes the survivors of check_literal_core.py, (2) lists every
empty-mark chart of each survivor G over every inner area, (3) re-tests each survivor H for Schur
equality with G under independent random specializations, and (4) asserts that no survivor is a
genuine, source-minimal, Schur-equal counterexample.
"""
import random
import sys
from fractions import Fraction

src = open(__file__.replace("check_literal_core_positive", "check_literal_core")).read()
src = src.replace("\nmain()\n", "\n")
sys.argv = [sys.argv[0], "16"]
exec(compile(src, "check_literal_core", "exec"))   # defines skews, rot, compose, schur_key, ...

rng = random.Random(20260801)
HVS = [{m: Fraction(rng.randint(2, 10**6), rng.randint(3, 10**6)) for m in range(1, 60)}
       for _ in range(3)]


def empty_charts(G):
    """All (area a, inner e, outer J2) with J2 o_empty e == G up to translation or rotation."""
    n = len(G)
    out = []
    for a in range(2, n):
        if n % a:
            continue
        for U2 in skews(a):
            for e in (U2, rot(U2)):
                for J2 in skews(n // a):
                    G2 = compose(J2, e)
                    if len(G2) == n and is_skew(G2) and (G2 == G or rot(G2) == G):
                        out.append((a, sorted(e), sorted(J2)))
    return out


def survivors():
    out = []
    nU, nJ = 8, 2
    n = 16
    S8, S2, S16 = skews(nU), skews(nJ), skews(n)
    cls = {}
    for H in S16:
        cls.setdefault(schur_key(H), []).append(H)
    for U in S8:
        if len({i for i, _ in U}) == 1 or len({j for _, j in U}) == 1 or composite(U):
            continue
        allowed = set()
        for Jp in S2:
            for e in (U, rot(U)):
                x = compose(Jp, e)
                if is_skew(x) and connected(x):
                    allowed |= {normalize(x), rot(normalize(x))}
        for J in S2:
            G = compose(J, U)
            if not (is_skew(G) and connected(G) and len(G) == n):
                continue
            for H in cls[schur_key(G)]:
                if H not in allowed:
                    out.append((U, J, G, H))
    return out


def main():
    surv = survivors()
    print("survivors at area 16 (U area 8, J area 2):", len(surv))
    genuine = 0
    for U, J, G, H in surv:
        charts = empty_charts(G)
        smaller = [k for k in charts if k[0] < len(U)]
        sU = sorted(U)
        same = all(k[0] >= len(U) for k in charts)
        eq = [c.schur(G, hv) == c.schur(H, hv) for hv in HVS]
        print("U", sU, "J", sorted(J))
        print("  empty-mark charts of G (area of inner, inner, outer):", charts)
        print("  chart with inner of smaller span:", bool(smaller), "| source-minimal (width 0, no smaller span):", same)
        print("  H Schur-equal to G under 3 independent specializations:", eq)
        if same and all(eq):
            genuine += 1
            print("  H", sorted(H))
    print("genuine counterexamples (source-minimal and Schur-equal):", genuine)
    assert genuine == 0, "CoreMarkMinimal fails: source-minimal chart whose Schur class leaves omega o D"
    print("PASS")


main()
