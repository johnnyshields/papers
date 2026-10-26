r"""Paper section `sec:comparison` (Finite comparisons on actual composition charts), ph:activation,
the open mate implications.

For every source E of the form V o_mu J (V of at most OUTER cells and span at least 3, J of at most
CELLS cells, mu any legal mark of J) and every legal positive upper mark omega of E of width w and
period Q = S - w, S = span E, the paper's open mate implications

    x in X_E, 0 < x < w   =>   Q + x in X_E,
    y in Y_E, Q < y < S   =>   y - Q in Y_E

hold, for all four attachment types.  Also asserted on every connected diagram E with a legal
positive mark, without a composition structure.  The equality T_Q(E) = T_Q(U) of the lemma is a
statement about Schur-function equalities of whole parents and is not checked here.
"""
from _gluing_common import compose, is_connected_skew, legal, span
from check_two_copy_flags import betas, diagrams, marks

CELLS = 7
OUTER = 5
BARE = 11


def mate(E, om):
    X, Y = betas(E)
    S = X[0]
    w = om.width
    Q = S - w
    assert Q == om.period
    assert all((Q + x) in X for x in X if 0 < x < w), (sorted(E), om.case)
    assert all((y - Q) in Y for y in Y if Q < y < S), (sorted(E), om.case)


def main():
    seen = {}
    for E in diagrams(BARE):
        for om in marks(E):
            if om.lower:
                mate(E, om)
                seen[om.case] = seen.get(om.case, 0) + 1
    assert set(seen) == set('abcd')
    sources = 0
    for J in diagrams(CELLS):
        for mu in marks(J):
            for V in diagrams(OUTER):
                if span(V) < 3:
                    continue
                E = compose(V, mu)
                if not is_connected_skew(E):
                    continue
                for om in marks(E):
                    if om.lower and legal(om):
                        mate(E, om)
                        sources += 1
    print(f'ph:activation (mate implications): {sum(seen.values())} bare marks {seen}, '
          f'{sources} (source, upper mark) pairs on compositions')
    print('ALL PASS')


if __name__ == '__main__':
    main()
