r"""The aligned-case score comparison of the narrow reduction (rt:preprocessing).

Paper section `sec:reduction` (Factor readout and the two-copy reduction), rt:preprocessing,
rt:finer-parameters.

Reading: the first paragraph of the proof compares scores (width, span) lexicographically, the
finer chart scoring (v, r + v) and the original (w, Q + w), with S = M r + v, Q = S - w, Q > w,
M >= 3, r | Q.  Two parts.

(1) Arithmetic box: r | Q forces w = v (mod r); on the whole box r, v, w, M in a bounded range
the finer score is strictly lower exactly when v <= w (for v = w, r + v < Q + w since Q >= 2r);
the box also contains the cases w < v with w = v (mod r), where the finer score is NOT lower.  The paragraph states the hypotheses Q > w,
M >= 3 and w = v (mod r) only, so the conclusion needs the additional input v <= w.
(2) Actual charts: for every connected J up to J_CELLS cells, legal mark mu of J (period r,
width v), and connected outer V up to V_CELLS cells with span M >= 3, every legal mark omega of
E = V o_mu J with period Q, width w, Q + w = N_E, Q > w and r | Q is listed; the count with
w < v is asserted to be zero: on actual charts v <= w holds, together with the identity
N_E = M r + v of rt:finer-parameters on every such E.

Every actual instance (all compositions of every connected inner up to J_CELLS cells through every
legal mark, every outer up to V_CELLS cells, every upper mark with r | Q) is asserted to have the
finer score strictly below the original: the census-wide score decrease.  Uncovered: the held
minimum over all charts of E (the census carries no second chart of a Schur-equal parent), the
existence of the complete aligned theorem's proper period-r chart, and the three excluded cases.
"""
from _gluing_common import compose, intersection_mark, legal, span
from check_two_copy_flags import betas, diagrams

J_CELLS = 7
V_CELLS = 5


def lower(a, b):
    return a < b


def main():
    below = notbelow = 0
    for r in range(2, 8):
        for v in range(0, 12):
            for M in range(3, 7):
                S = M * r + v
                for w in range(0, S):
                    Q = S - w
                    if not (Q > w and Q % r == 0):
                        continue
                    assert (w - v) % r == 0
                    is_lower = lower((v, r + v), (w, Q + w))
                    if v <= w:
                        assert is_lower
                        below += 1
                    else:
                        assert not is_lower and w < v
                        notbelow += 1
    assert below > 0 and notbelow > 0
    print(f'arithmetic box: finer score lower in {below}, not lower (w < v) in {notbelow}')

    inst = wless = 0
    outers = [V for V in diagrams(V_CELLS) if span(V) >= 3]
    for J in diagrams(J_CELLS):
        for cell in J:
            try:
                mu = intersection_mark(J, cell)
            except AssertionError:
                continue
            if not legal(mu) or mu.width == 0:
                continue
            r, v = mu.period, mu.width
            for V in outers:
                try:
                    E = compose(V, mu)
                except AssertionError:
                    continue
                M = span(V)
                X, _ = betas(E)
                assert X[0] == M * r + v
                for c2 in E:
                    try:
                        om = intersection_mark(E, c2)
                    except AssertionError:
                        continue
                    if not legal(om):
                        continue
                    Q, w = om.period, om.width
                    assert Q + w == X[0]
                    if Q > w and Q % r == 0:
                        inst += 1
                        assert (w - v) % r == 0
                        wless += w < v
                        assert (v, r + v) < (w, Q + w), (sorted(E), r, v, Q, w)
    print(f'actual marks with r | Q: {inst}, of which w < v: {wless}')
    assert inst > 0 and wless == 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
