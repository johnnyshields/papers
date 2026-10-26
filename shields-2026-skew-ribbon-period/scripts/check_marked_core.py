r"""Paper section `sec:descent` (Strict descent and actual realization).

`lem:marked-core` (mark-sensitive core reduction), in the subsection on marks under core deletion.

For every actual proper chart `S = D o_omega E` with a legal positive-width mark on a small inner
`E` and small outers `D`, the zero-free cores are formed by deleting common betas from the beta
lists of `E` and of `S`.  Asserted: the core of `E` is a connected diagram of the same span and
carries a legal mark of the same period and width (found by searching every legal mark of the
core), and the core of `S` is literally the composition through such a mark of `D`, `AT(D)` or
`Core(D)`; the outer retained is `D` or `AT(D)` at positive distinct phases and `Core(D)` at
coincident phases, and the script reports which occur.  The statement's phase classification is
read from the mark's phases `(t, s)` of `eq:coding` (distinct when `t != s`).  Sampled: inners of
up to 7 cells, outers of up to 4 cells.
"""
from check_regroup_mixed import Mark, content, is_cskew, legal_marks, min_content, skew_shapes, span, translate
from verify_charts import beta_lists, from_betas
from verify_descent import normalize


def core(S):
    X, Y = beta_lists(S)
    common = set(X) & set(Y)
    Xc = tuple(x for x in X if x not in common)
    Yc = tuple(y for y in Y if y not in common)
    return from_betas(Xc, Yc) if Xc else frozenset()


def antitranspose(S):
    return normalize(frozenset((-j, -i) for i, j in S))


def main():
    outers = [D for D in skew_shapes(4, 3, 3) if len(D) >= 2]
    n = 0
    kinds = {}
    for E in skew_shapes(7, 4, 5):
        if len(E) < 2:
            continue
        Ec = core(E)
        for om in legal_marks(E):
            w, p = om.width(), om.period()
            if w == 0:
                continue
            c0 = min_content(E)
            cs = sorted(content(x) - c0 for x in om.middle())
            s_, t_ = cs[0], cs[-1] - p + 1
            coincident = (s_ == t_)
            assert Ec and is_cskew(Ec) and span(Ec) == span(E)
            marks_c = [m for m in legal_marks(Ec) if m.period() == p and m.width() == w]
            assert marks_c, ("core carries no legal mark of the same period and width", sorted(E), sorted(om.W))
            for D in outers:
                Sc = core(om.compose(D))
                if not Sc:
                    continue
                Dc = core(D) if core(D) else None
                found = None
                allnames = set()
                for m2 in marks_c:
                    for name, Dp in (('D', D), ('AT(D)', antitranspose(D)), ('Core(D)', Dc)):
                        if Dp and normalize(m2.compose(Dp)) == normalize(Sc):
                            found = found or name
                            allnames.add(name)
                assert found, ("core of the chart is not a composition through the core mark",
                               sorted(E), sorted(om.W), om.case, sorted(D))
                if coincident:
                    assert 'Core(D)' in allnames, (allnames, sorted(E), sorted(om.W), sorted(D))
                else:
                    assert allnames & {'D', 'AT(D)'}, allnames
                kinds[(found, 'coincident' if coincident else 'distinct')] = kinds.get((found, 'coincident' if coincident else 'distinct'), 0) + 1
                n += 1
    print(f"charts {n}; retained outer by phase: {kinds}")
    assert n > 0
    print("PASS")


if __name__ == "__main__":
    main()
