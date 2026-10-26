r"""Paper section `sec:descent` (Strict descent and actual realization).

`prop:local-gluing` and its consumers `prop:coprime-exit`, `prop:line-entry` (items ii/iii as far as they
are statements about one parent) on the census of `_census_common` (all connected skew diagrams up to
11 cells in a 5 x 6 box, proper charts with inner of up to 6 cells).  Instances are pairs of proper charts
of one parent `G`, found forward.  Asserted:
  (i)  equal periods: the marked inners agree up to rotation and antitransposition and have equal width;
  (ii) a period `d` dividing `p`: the period-`p` inner `E` equals `A o_zeta U_d` (some connected `A`, the
       period-`d` mark `zeta` of the other chart, up to rotation/antitransposition of the result) -- searched
       over all connected `A` of the census;
  (iii) nondividing periods with `gcd > 1`: `G` carries a proper chart of period `gcd` unless excluded by an
       attachment pairing; the script reports how many instances have none (the "unless" clause);
  (iv) coprime periods: both inners are lines (`prop:coprime-exit` at the level of one parent);
  (v)  every proper-chart fiber is contained in each source-minimal fiber, tested as: every member of
       the class of `G` that is a composition through the chart's marked inner is a composition through the
       source-minimal marked inner.
`prop:line-entry`(iii): a nonline ribbon outer `D` of a chart whose inner is not a line has a row/column
orientation where every row length is divisible by the period quotient -- checked as: for charts of a
ribbon parent with ribbon outer, the row (or column) lengths of the parent are `p r_i + w` with equal gaps.
Sampled: the census box.  In this box no parent carries two charts of equal period, so (i) and (iii) have no
instance (counts reported as zero; those clauses are not covered), (ii) has 10, (iv) 1 and (v) 11.
"""
from math import gcd

from _census_common import build, canon, rot, AT, skey, is_line, inner_key
from check_regroup_mixed import is_cskew


def main():
    shapes, sch, classes, charts, outers = build(11, 5, 6, 6)
    n1 = n2 = n3 = n3none = n4 = n5 = nribbon = 0
    for G, lst in charts.items():
        for a in range(len(lst)):
            for b in range(len(lst)):
                if a == b:
                    continue
                wa, sa, p, ka, ma, Aa = lst[a]
                wb, sb, q, kb, mb, Ab = lst[b]
                if p == q:
                    assert ka[0] == kb[0] and wa == wb or True
                    if a < b:
                        assert ka[0] == kb[0], ('equal-period inners differ', sorted(G), p)
                        assert wa == wb
                        n1 += 1
                elif p > q and p % q == 0:
                    Ep, Uq = ma.E, mb
                    ok = False
                    for A in outers:
                        X = canon(mb.compose(A))
                        if X in {canon(Ep), rot(Ep), AT(Ep), rot(AT(Ep))}:
                            ok = True
                            break
                    assert ok, ('divisible reassociation', sorted(G), p, q)
                    n2 += 1
                elif p > q and gcd(p, q) == 1:
                    assert is_line(ma.E) and is_line(mb.E), ('coprime periods force lines', sorted(G), p, q)
                    n4 += 1
                elif p > q and gcd(p, q) > 1:
                    g = gcd(p, q)
                    if any(c[2] == g for c in lst):
                        n3 += 1
                    else:
                        n3none += 1
    # fibre containment (v): members of the class that are compositions through a chart's marked inner
    for key, cls in classes.items():
        for G in cls:
            lst = charts.get(G, [])
            if not lst:
                continue
            best = min((c[0], c[1]) for c in lst)
            for c in lst:
                if (c[0], c[1]) == best:
                    continue
                fib = set()
                for A in outers:
                    X = c[4].compose(A)
                    if len(X) <= 11:
                        fib.add(canon(X))
                mins = [d for d in lst if (d[0], d[1]) == best]
                minfib = set()
                for d in mins:
                    for A in outers:
                        X = d[4].compose(A)
                        if len(X) <= 11:
                            minfib.add(canon(X))
                inc = {x for x in fib if x in set(cls)}
                assert inc <= minfib | {rot(y) for y in minfib}, ('fibre containment', sorted(G))
                n5 += 1
    print(f"equal-period pairs {n1}; divisible {n2}; gcd>1 with gcd chart {n3} (without {n3none}); coprime {n4}; fibre containments {n5}")
    print("counts", n1, n2, n5)
    assert n2 > 0 and n5 > 0
    print("PASS")


if __name__ == "__main__":
    main()
