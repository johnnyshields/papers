r"""Paper section `sec:boundary` (Boundary comparisons and actual marked factors), ge:endpoint-splice
(the consumer step of ph:endpoint-splice).

J is an ordinary finer inner of period r, width 0 < v < r, contacts s = v, t = 0 (case (a) mark mu),
with an ordinary or EMPTY upper of width 0 <= w < v, delta = v - w.  The splices S = D < J and
T = J < B are built from the restriction flags of ph:endpoint-splice.  The "complete physical
endpoint identity" of the statement is the equality s_S = s_T of Schur functions delivered by
ph:endpoint-splice; it is imposed here as a hypothesis, tested by exact Schur functions.  The lemma's
conclusion is then asserted: J is literally self-rotational with its full mark (mu equals its
half-turn), or J has an actual proper chart of period d dividing r, d < r, whose score
(v mod d, d + v mod d) is lexicographically below (v, r + v) -- the improvement of the minimum held on
E and U.  The chart is looked up in a table of compositions A o_nu K (K up to TABLE_IN cells, A up to
TABLE_OUT cells).

Control: instances failing the identity are counted; the identity is what separates the self-rotational
marks from the rest.  The held-minimum clause (E source-minimal) is not imposed, which is the stated
gap: the conclusion is checked as an either/or, never as the claim that the second alternative
contradicts a minimum.
"""
from _gluing_common import compose, rotated_mark, schur
from check_two_copy_flags import betas, diagrams, marks, phases
from verify_endpoint_splice import checked_diagram, splice

CELLS = 10
TABLE_IN = 6
TABLE_OUT = 6


def main():
    table = {}
    outers = [A for A in diagrams(TABLE_OUT) if len(A) >= 2]
    for K in diagrams(TABLE_IN):
        for nu in marks(K):
            for A in outers:
                table.setdefault(compose(A, nu), set()).add((nu.period, nu.width))
    holds_self = holds_chart = fails_identity = 0
    for J in diagrams(CELLS):
        XJ, YJ = betas(J)
        for mu in marks(J):
            if mu.case != 'a' or not mu.lower:
                continue
            v, r = mu.width, mu.period
            if phases(mu) != (v, 0):
                continue
            N = r + v
            XW, YW = betas(mu.lower)
            for w in range(0, v):
                d = v - w
                if w:
                    XB = sorted({d} | {x for x in XW if 0 < x < d}, reverse=True)
                    YB = sorted((y for y in YW if 0 <= y < d), reverse=True)
                    XD = sorted((x - w for x in XW if w < x <= v), reverse=True)
                    YD = sorted({0} | {y - w for y in YW if w < y < v}, reverse=True)
                else:
                    XB, YB, XD, YD = XW, YW, XW, YW
                try:
                    S = checked_diagram(*splice(XD, YD, XJ, YJ, N))
                    T = checked_diagram(*splice(XJ, YJ, XB, YB, d))
                except AssertionError:
                    continue
                if schur(S) != schur(T):
                    fails_identity += 1
                    continue
                if rotated_mark(mu) == mu:
                    holds_self += 1
                    continue
                better = any(p < r and r % p == 0 and p >= 2 and
                             (v % p, p + v % p) < (v, r + v)
                             for p, _ in table.get(J, set()))
                assert better, (sorted(J), r, v, w)
                holds_chart += 1
    assert holds_self > 0 and holds_chart > 0 and fails_identity > 0
    print(f'ge:endpoint-splice: s_S = s_T in {holds_self} self-rotational and {holds_chart} '
          f'improving-chart cases; {fails_identity} cases without the identity')
    print('ALL PASS')


if __name__ == '__main__':
    main()
