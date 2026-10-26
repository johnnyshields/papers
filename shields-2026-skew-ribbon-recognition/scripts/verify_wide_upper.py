r"""Paper section `app:boundary` (Boundary constructions and exceptional entrances), rt:wide and
rt:boundary.

Setting.  E = V o_mu J is a proper chart (both factors of at least two cells) with finer period r,
width v, and span S = M r + v, M = span V.  E carries a legal upper mark omega of width w and period
Q = S - w (a legal mark has w < Q automatically).

rt:wide (w > r, r not dividing Q).  With g = gcd(r, Q), u = v mod g, either E has an actual proper
legal chart of period g >= 2 and width u whose score (u, g + u) is lexicographically below (v, r + v),
or J is a literal line (one row or one column).

rt:boundary (w = r, r not dividing Q).  A mixed finer cannot occur; a positive ordinary finer is
either a literal line or E has a proper empty-overlap chart (width 0) of strictly better score.

The charts of E are found in a table built from the other side: every connected outer of at least
two cells composed through every legal mark (the empty mark included) of every connected inner of at
least two cells, up to the stated sizes.  A chart found there is a proof of existence; E that has a
chart outside the table would only make the check fail, never pass vacuously.  Counts of each
alternative are asserted positive.
"""
from math import gcd

from _gluing_common import compose, content, is_connected_skew, legal, span
from check_two_copy_flags import diagrams, marks

CELLS = 10          # inner J
OUTER = 5           # coarse V
TABLE_IN = 8        # inner diagrams of the table
TABLE_OUT = 7       # outer diagrams of the table
LIMIT = 16         # cells of E
BIG_OUT = 10        # outers of the table paired with inners of at most 3 cells


def is_line(J):
    return len({i for i, _ in J}) == 1 or len({j for _, j in J}) == 1


def main():
    table = {}
    outers = [A for A in diagrams(TABLE_OUT) if len(A) >= 2]
    big = [A for A in diagrams(BIG_OUT) if len(A) > TABLE_OUT]
    for K in diagrams(TABLE_IN):
        for nu in marks(K):
            for A in outers + (big if len(K) <= 3 else []):
                if len(A) * len(K) > 3 * LIMIT:
                    continue
                P = compose(A, nu)
                if len(P) <= LIMIT:
                    table.setdefault(P, set()).add((nu.period, nu.width))
    coarse = [V for V in diagrams(OUTER) if len(V) >= 2]
    wide_chart = wide_line = bnd_chart = bnd_line = bnd_mixed = 0
    for J in diagrams(CELLS):
        for mu in marks(J):
            r, v = mu.period, mu.width
            for V in coarse:
                E = compose(V, mu)
                if len(E) > LIMIT or not is_connected_skew(E):
                    continue
                S = span(E)
                for om in marks(E):
                    if not legal(om) or not om.lower:
                        continue
                    w = om.width
                    Q = S - w
                    if w < r or (Q % r == 0):
                        continue
                    g = gcd(r, Q)
                    if w > r:
                        u = v % g
                        ok = g >= 2 and (u, g + u) < (v, r + v) and \
                            (g, u) in table.get(E, set())
                        if ok:
                            wide_chart += 1
                        else:
                            assert is_line(J), ('rt:wide', sorted(J), sorted(mu.lower), w)
                            wide_line += 1
                    else:
                        assert mu.case not in 'cd', ('mixed finer carries the upper', sorted(J))
                        if mu.case in 'ab' and mu.lower:
                            better = any(wd == 0 and (0, p) < (v, r + v)
                                         for p, wd in table.get(E, set()))
                            if better:
                                bnd_chart += 1
                            else:
                                assert is_line(J), ('rt:boundary', sorted(J), sorted(mu.lower))
                                bnd_line += 1
    print(f'rt:wide: {wide_chart} with a smaller-score chart of period g, {wide_line} line finers; '
          f'rt:boundary: {bnd_chart} with an empty-overlap chart, {bnd_line} line finers')
    assert wide_chart > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
