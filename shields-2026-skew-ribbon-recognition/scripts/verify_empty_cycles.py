r"""Paper sections `sec:completion` (Completion of marked-factor recognition) and `app:boundary`
(Boundary constructions and exceptional entrances), rt:empty-cycles and ge:primitive-cycle.

rt:empty-cycles.  J carries its genuine horizontal empty mark, span r, X_J = {r} u I,
Y_J = C u {0}.  For 0 < w < r with (I - w) mod r in I u {0} and (C + w) mod r in C u {0}, put
g = gcd(r, w).  If g = 1 the full marked J is self-reflecting (J equals its half-turn); if g >= 2
there is a proper period-g empty chart J = A o_EMPTY K, span K = g, both factors strictly smaller.
The chart is found in a table built from the other side: every pair of connected A, K with
|A| |K| <= CELLS composed through the empty mark of K.

ge:primitive-cycle.  For a positive ordinary inner J of period r, width v and contacts s, t, put
B = X_W u B_-, C = Y_W u C_-.  If b in B \ {s} implies b + delta in B and c in C \ {t} implies
c - delta in C (mod r) with gcd(r, delta) = 1, the full marked J is self-rotational: its mark equals
its half-turned mark.  The conditions on s, t, 0, v (s in B, t in C, 0 not in B, v not in C) are
asserted as well.  Every delta with 1 <= delta < r is tried on every mark.

Exhaustive over every connected J of at most CELLS cells.
"""
from math import gcd

from _gluing_common import compose, empty_mark, normalize, rotate, rotated_mark, span
from check_two_copy_flags import betas, diagrams, marks, phases

CELLS = 12


def main():
    table = {}
    for A in diagrams(CELLS // 2):
        for K in diagrams(CELLS // 2):
            if len(A) * len(K) <= CELLS:
                J = compose(A, empty_mark(K))
                table.setdefault(J, set()).add(span(K))
    reflecting = chains = 0
    for J in diagrams(CELLS):
        X, Y = betas(J)
        r = X[0]
        I = set(X) - {r}
        C = set(Y) - {0}
        for w in range(1, r):
            if all(((i - w) % r) in I | {0} for i in I) and \
                    all(((c + w) % r) in C | {0} for c in C):
                g = gcd(r, w)
                if g == 1:
                    assert normalize(rotate(J)) == J, sorted(J)
                    reflecting += 1
                else:
                    assert g in table.get(J, set()), (sorted(J), w, g)
                    chains += 1
    assert reflecting > 0 and chains > 0
    print(f'rt:empty-cycles: {reflecting} self-reflecting (g = 1) and {chains} chart (g >= 2) cases')
    cycles = 0
    for J in diagrams(CELLS):
        XJ, YJ = betas(J)
        for mu in marks(J):
            if mu.case != 'a' or not mu.lower:
                continue
            r, v = mu.period, mu.width
            s, t = phases(mu)
            XW, YW = betas(mu.lower)
            B = set(XW) | {x for x in XJ if v < x < r}
            C = set(YW) | {y for y in YJ if v < y < r}
            assert s in B and t in C and 0 not in B and v not in C, (sorted(J), s, t)
            for delta in range(1, r):
                if gcd(r, delta) != 1:
                    continue
                if all(((b + delta) % r) in B for b in B - {s}) and \
                        all(((c - delta) % r) in C for c in C - {t}):
                    assert rotated_mark(mu) == mu, (sorted(J), sorted(mu.lower), delta)
                    cycles += 1
    assert cycles > 0
    print(f'ge:primitive-cycle: {cycles} (mark, delta) cases, every one self-rotational')
    print('ALL PASS')


if __name__ == '__main__':
    main()
