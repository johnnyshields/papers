r"""Paper section `sec:extraction` (Recovering ordinary factors).

Starts from the parent rather than from a chart.  For every connected diagram
\(F\) of at most `--max-area` cells (default 9) the composition engine
(`_composition_engine.py`) enumerates every proper legal chart \(F=D\circ E\) of
every attachment case by an exhaustive search over the placements of \(E\) in
\(F\); its composition, its marks, and its factorizations do not share code with
`schur_tools.compose` or `schur_tools.legal_marks`.  Then, for each \((F,p)\)
pair, the decoder, which sees only \(P=s_F\) and \(p\), is run, and
`cor:period-test`, `thm:extraction`, `lem:mixed-vanishing`, `rt:mixed-readout`
and `lem:terminal-readout` are asserted on every chart found.

The converse is measured, not asserted: a pair that passes the test of
`cor:period-test` and has no chart in the box is counted, which is what the
sentence after the corollary says.  SymPy arithmetic is exact.
"""

import argparse
import time
from collections import Counter

import sympy as sp

from schur_tools import apply, decode, delta, schur, shapes, standard_tableaux
from _weighted_readout import decode_mixed, involution
import _composition_engine as eng


def test_passes(P, p):
    """The two conditions of cor:period-test, read off the parent alone."""
    try:
        decode(P, p)
    except ValueError:
        return False
    return True


def is_ribbon(D):
    return len({j - i for i, j in D}) == len(D)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-area', type=int, default=9)
    args = parser.parse_args()
    t0 = time.time()
    counts = Counter()
    ordinary_pairs = set()
    tested = {}
    for n in range(4, args.max_area + 1):
        for F in shapes(n):
            Fe = eng.normalize(frozenset(F))     # the engine's own corner convention
            charts = eng.factorizations(Fe)
            if not charts:
                continue
            P = schur(F)
            counts['parents with a chart'] += 1
            for D, E, Wsw, Wne, case in charts:
                v = eng.v_of_W(E, Wsw, Wne, case)
                p = v[1] - v[0]
                if case in ('a', 'b'):
                    a, got_E, got_D, T, U, ratios = decode(P, p)
                    expected = schur(D) if case == 'a' else involution(schur(D))
                    assert a == len(D)
                    assert got_E == schur(E)
                    assert got_D == sp.expand(expected) or got_D == expected
                    assert all(r.is_Rational for r in ratios.values())
                    f = standard_tableaux(frozenset(D))
                    assert ratios[(1,) * a] == 1 and ratios[(a,)] == apply(expected, (a,)) / f
                    assert T != 0 and U != 0
                    ordinary_pairs.add((F, p))
                    counts['ordinary charts decoded'] += 1
                    counts['ordinary case ' + case] += 1
                else:
                    # lem:mixed-vanishing: every period-multiple Hall adjoint vanishes
                    for k in range(p, len(F) + 1, p):
                        assert delta(P, k) == 0, (sorted(F), p)
                    assert not test_passes(P, p)
                    counts['mixed charts annihilated'] += 1
                    if is_ribbon(D):
                        got = decode_mixed(P, p)
                        assert got['area'] == len(D)
                        assert got['inner'] == schur(E)
                        assert got['outer'] == schur(D)
                        counts['mixed ribbon charts recovered'] += 1
            tested[F] = P
    # cor:period-test: a proper ordinary chart at period p makes the test pass.  Every one
    # above decoded, and the loop below asserts the implication pair by pair.
    passing_without_chart = failing = passing = 0
    for n in range(4, args.max_area + 1):
        for F in shapes(n):
            P = tested.get(F)
            if P is None:
                P = schur(F)
            for p in range(1, len(F) + 1):
                ok = test_passes(P, p)
                if (F, p) in ordinary_pairs:
                    assert ok
                if ok:
                    passing += 1
                    passing_without_chart += (F, p) not in ordinary_pairs
                else:
                    failing += 1
    assert failing > 0 and passing_without_chart > 0
    print(f'PASS: decoder on every proper chart of every connected parent of 4 to {args.max_area} cells: '
          f'{dict(sorted(counts.items()))}')
    print(f'PASS: cor:period-test over all (F, p) of the box: {failing} pairs rejected, {passing} pass; '
          f'{passing_without_chart} passing pairs have no proper ordinary chart, so passing builds none')
    print(f'ALL PASS t={time.time() - t0:.0f}s')


if __name__ == '__main__':
    main()
