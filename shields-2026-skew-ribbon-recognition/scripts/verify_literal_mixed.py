r"""Paper section `sec:boundary` (Boundary comparisons and actual marked factors), ge:literal-mixed.

J carries a legal type-(d) mark mu of period r and width v, P = A o_mu J is an actual composition
(a one-cell A allowed), 0 < L < r, and for 0 <= x <= H

    X_P(x + L) = X_P(x),    Y_P(x + L) <= Y_P(x),    H >= r - 1,

where X_P, Y_P are the indicator words of the beta lists of P and every displayed position is real
(x + L <= span P).  H is not given a value in the statement; every admissible H from r - 1 up to
span P - L is tried, so the strongest hypothesis (the largest H) and the weakest are both covered.
Then J has a proper factor of period d = gcd(r, L), with 2 <= d < r and d not dividing v.  The
factor is looked up in a table of every composition of a connected outer of at least two cells
through a legal mark of an inner of at least two cells.

Exhaustive over every connected J of at most CELLS cells, every type-(d) mark, every connected A of
at most OUTER cells.  The count of triples meeting the hypotheses is asserted positive.
"""
from math import gcd

from _gluing_common import compose, span
from check_two_copy_flags import betas, diagrams, marks

CELLS = 9
OUTER = 6
TABLE_IN = 6
TABLE_OUT = 6


def indicator(L, size):
    return [1 if x in L else 0 for x in range(size + 1)]


def main():
    table = {}
    outers = [A for A in diagrams(TABLE_OUT) if len(A) >= 2]
    for K in diagrams(TABLE_IN):
        for nu in marks(K):
            for A in outers:
                P = compose(A, nu)
                if len(P) <= CELLS:
                    table.setdefault(P, set()).add(nu.period)
    cell = frozenset({(0, 0)})
    hits = triples = 0
    for J in diagrams(CELLS):
        for mu in marks(J):
            if mu.case != 'd' or not mu.lower:
                continue
            r, v = mu.period, mu.width
            for A in [cell] + [A for A in diagrams(OUTER)]:
                P = compose(A, mu)
                triples += 1
                X, Y = betas(P)
                N = X[0]
                Xw, Yw = indicator(X, N + 1), indicator(Y, N + 1)
                for L in range(1, r):
                    for H in range(r - 1, N - L + 1):
                        if all(Xw[x + L] == Xw[x] and Yw[x + L] <= Yw[x] for x in range(H + 1)):
                            d = gcd(r, L)
                            assert 2 <= d < r and v % d != 0, (sorted(J), sorted(mu.lower), L, H)
                            assert d in table.get(J, set()), (sorted(J), d)
                            hits += 1
    assert hits > 0
    print(f'ge:literal-mixed: {triples} (J, mark, A) triples, {hits} (L, H) cases meeting the '
          f'hypotheses, each with a proper factor of period gcd(r, L), 2 <= d < r, d not dividing v')
    print('ALL PASS')


if __name__ == '__main__':
    main()
