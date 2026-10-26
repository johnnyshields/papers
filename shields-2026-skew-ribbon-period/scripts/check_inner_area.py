r"""Paper section `app:aligned` (`prop:noncell-realization`, `eq:empty-section`): inner area.

For a legal mark omega on E and a connected D with at least two cells, the composite D o_omega E
has strictly more cells than E, so the inner diagram of a chart of area n has area below n.
Also reports the obstruction to the inner-class induction: the class quotient concludes
s_{chi1.omega.E} = s_{chi2.omega.J} only for a chart chi1 whose parent has the mark omega, so a
statement about E needs a parent D o_omega E in the class of a composite of the fine mark.
"""
from _gluing_common import compose, legal
from _mark_builders import diagrams, marks


def main():
    tested = 0
    for E in diagrams(7):
        for mk in marks(E):
            if not legal(mk):
                continue
            for D in diagrams(4):
                F = compose(D, mk)
                tested += 1
                assert len(F) > len(E), (E, D)
    print("composites tested", tested, "all have area > area(E)")


if __name__ == "__main__":
    main()
