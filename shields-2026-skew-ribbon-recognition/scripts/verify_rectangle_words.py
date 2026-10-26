r"""Paper section `app:boundary` (Boundary constructions and exceptional entrances), ge:rectangle.

A connected diagram P of span N = m g + a (1 <= g < N, m >= 2, 0 <= a < g) with a singleton
diagonal at content g - 1 and closed words satisfying X_P(x + g) - X_P(x) = [x = s],
Y_P(x + g) - Y_P(x) = -[x = t] for 0 <= x <= N - g is a composition of a rectangle through a legal
ordinary or empty inner of period g and width a; for g >= 2 both factors are proper and strictly
smaller, and for g = 1 the diagram P is a rectangle.

The converse side of the statement is not needed: the check enumerates every connected diagram P of
at most CELLS cells, selects those meeting the word hypotheses for some g, and looks the composition
up in a table built independently from the other side -- every connected inner of at most CELLS - 1
cells, every legal ordinary or empty mark of it, every rectangle outer, composed by the gluing
composition.  The table is checked to contain P with the stated period and width.  The number of P
meeting the hypotheses is asserted positive for g = 1 and for g >= 2, so the claim is not vacuous.
"""
from _gluing_common import compose, content, is_connected_skew, normalize, span
from check_two_copy_flags import betas, diagrams, marks

CELLS = 10
RECT = CELLS // 2


def rectangle(r, c):
    return frozenset((i, j) for i in range(r) for j in range(c))


def is_rectangle(P):
    rows = {i for i, _ in P}
    cols = {j for _, j in P}
    return len(P) == len(rows) * len(cols)


def hypotheses(P, g):
    X, Y = betas(P)
    N = X[0]
    if not (1 <= g < N):
        return None
    m, a = divmod(N, g)
    if m < 2:
        return None
    word = lambda L, x: 1 if x in L else 0
    dX = [word(X, x + g) - word(X, x) for x in range(N - g + 1)]
    dY = [word(Y, x + g) - word(Y, x) for x in range(N - g + 1)]
    if sorted(dX) != sorted([0] * (N - g) + [1]):
        return None
    if sorted(dY) != sorted([-1] + [0] * (N - g)):
        return None
    base = min(content(c) for c in P)
    if sum(1 for c in P if content(c) - base == g - 1) != 1:
        return None
    return m, a


def main():
    table = {}
    for E in diagrams(CELLS - 1):
        for mk in marks(E):
            if mk.case not in 'ab':
                continue
            for r in range(1, RECT + 1):
                for c in range(1, RECT + 1):
                    if r * c < 2:
                        continue
                    try:
                        P = compose(rectangle(r, c), mk)
                    except AssertionError:
                        continue
                    if len(P) > CELLS:
                        continue
                    table.setdefault(P, []).append((mk.period, mk.width, len(E), r * c))
    counts = {1: 0, 2: 0}
    for P in diagrams(CELLS):
        for g in range(1, span(P)):
            res = hypotheses(P, g)
            if res is None:
                continue
            m, a = res
            counts[min(g, 2)] += 1
            if g == 1:
                assert is_rectangle(P), sorted(P)
                continue
            hits = [t for t in table.get(P, []) if t[0] == g and t[1] == a]
            assert hits, ('no rectangle composition', sorted(P), g, a)
            assert any(len(P) > e >= 2 and len(P) > rc >= 2 for _, _, e, rc in hits), sorted(P)
    assert counts[1] > 0 and counts[2] > 0, counts
    print(f'ge:rectangle: hypotheses met by {counts[1]} (P, g = 1) and {counts[2]} (P, g >= 2) '
          f'pairs among diagrams up to {CELLS} cells; every one is as stated')
    print('ALL PASS')


if __name__ == '__main__':
    main()
