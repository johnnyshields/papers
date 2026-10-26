r"""Paper section `sec:geometry` (Periodic cores and actual boundary comparisons).

`lem:phase-confinement` and `eq:open-middle`, on single line charts.

The lemma is stated for an original line chart of period `p` and positive width `w` inside the
comparison, where `g = gcd(p, q)` and `c = w mod g`.  Its content concerns the one chart, so it is tested
on every small line-outer positive ordinary chart `S = L_M o_omega E` with each divisor `g` of `p`
in place of `gcd(p, q)` (`g < p`, `c = w mod g`, and the condition `w = d g + c` with `c > 0`).  Phases
`(t, s)` are read from the middle of the mark (`eq:coding`); the full boundary words are read from
the beta lists of `S`.  Asserted: the initial/terminal bounds of the displayed table (`t <= c` and
`w - s <= c` for a row outer in case (a); `s <= c` and `w - t <= c` for a column outer) hold, and both
boundary words are `p`-periodic on `{c + 1, ..., N - c - 1}` whenever `N` allows two periods there
(the hypotheses `N >= 2 p + c` and `g`-periodic diagonal heights on `c < k < N - c`, which the comparison
supplies and the check imposes; without the height hypothesis the bounds fail).  Sampled: inners of up to
8 cells, `M` in `{2, 3, 4}`.  The cases (b), (c), (d) of the table are reported but not asserted when the
table gives no bound for them.
"""
from math import gcd

from check_regroup_mixed import content, legal_marks, min_content, skew_shapes, span
from verify_charts import beta_lists, height_word


def words(S):
    X, Y = beta_lists(S)
    N = span(S)
    return {k: int(k in Y) for k in range(1, N)}, {k: int(k in X) for k in range(1, N)}


def main():
    n = nper = nbound = 0
    for E in skew_shapes(8, 4, 5):
        if len(E) < 2:
            continue
        for om in legal_marks(E):
            p, w = om.period(), om.width()
            if w == 0 or om.case != 'a':
                continue
            c0 = min_content(E)
            cs = sorted(content(x) - c0 for x in om.middle())
            s_, t_ = cs[0], cs[-1] - p + 1
            for g in range(2, p):
                if p % g:
                    continue
                c = w % g
                if c == 0:
                    continue
                for M in (2, 3, 4):
                    for rho, outer in ((0, frozenset((0, j) for j in range(M))), (1, frozenset((j, 0) for j in range(M)))):
                        S = om.compose(outer)
                        N = span(S)
                        if N < 2 * p + c:
                            continue
                        H = height_word(S)
                        if not all(H[k] == H[k + g] for k in range(c + 1, N - c - g)):
                            continue            # the comparison supplies g-periodic heights on the middle
                        n += 1
                        if rho == 0:
                            assert t_ <= c and w - s_ <= c, (sorted(E), sorted(om.W), g, 'row', t_, s_)
                        else:
                            assert s_ <= c and w - t_ <= c, (sorted(E), sorted(om.W), g, 'column', t_, s_)
                        nbound += 1
                        A, B = words(S)
                        for word in (A, B):
                            for k in range(c + 1, N - c - 1 - p + 1):
                                assert word[k] == word[k + p], (sorted(E), sorted(om.W), g, rho, k)
                        nper += 1
    print(f"line charts {n}; phase bounds {nbound}; p-periodicity on the open middle {nper}")
    assert n > 0
    print("PASS")


if __name__ == "__main__":
    main()
