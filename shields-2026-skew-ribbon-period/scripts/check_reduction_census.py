r"""Paper section `sec:reduction` (Reduction of the original comparison).

Consumer-step checks on the census of `_census_common` (all connected skew diagrams up to 12 cells in a
5 x 6 box; proper charts with inner of up to 7 cells) for `lem:strict-area`, `lem:oim`, `lem:fresh-descent`,
`prop:coprime-exit`, `prop:line-entry` and `cor:nonline-outer-exit`.

  * `lem:strict-area`: every proper chart has `|E| < |F|`, `|D| < |F|`, and every component of `F^-` smaller.
  * `lem:oim`: if `D o_omega E` is source-minimal with `E` not a line, then `A o_omega E` is source-minimal for
    every outer `A` of the census with `|A| >= 2` whose parent lies in the census, and every proper period
    of that parent is a multiple of `p`.
  * `prop:coprime-exit` / `lem:fresh-descent` (consumer form): in a class with no member carrying a proper
    line-inner chart, any two source-minimal charts of members have periods that are not coprime (both
    `>= 2`), and the least period of the class divides every source-minimal period.
  * `cor:nonline-outer-exit`, `prop:line-entry`: among pairs of source-minimal charts `F = D o E`, `H = C o U`
    of one such class with `p > q` nondividing, `gcd = g`, `A = p/g > B = q/g >= 2`, both marks positive and
    distinct-phase, count the pairs with `D` a nonline ribbon (the corollary says none exist) and those
    with `D` a line (then `C` is a line, `prop:line-entry`(i)).
The pair counts are reported; where a count is zero the clause has no instance in the box and that
part is not covered.  Sampled: the census box.
"""
from math import gcd

from _census_common import build, canon, is_line
from check_regroup_mixed import content, is_cskew, min_content


def phases(m):
    E = m.E
    c0 = min_content(E)
    cs = sorted(content(x) - c0 for x in m.middle())
    p = m.period()
    return cs[0], cs[-1] - p + 1


def main():
    shapes, sch, classes, charts, outers = build(12, 5, 6, 7)
    nstrict = noim = ncop = nmin = npairs = nnonline = nline = nlineC = 0
    for G, lst in charts.items():
        for (w, sp_, p, key, m, A) in lst:
            F = canon(m.compose(A))
            assert len(m.E) < len(F) and len(A) < len(F)
            comps = []
            Fm = frozenset(x for x in F if (x[0] + 1, x[1] + 1) in F)
            seen = set()
            for x in Fm:
                if x in seen:
                    continue
                st, comp = [x], {x}
                while st:
                    y = st.pop()
                    for d in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                        z = (y[0] + d[0], y[1] + d[1])
                        if z in Fm and z not in comp:
                            comp.add(z); st.append(z)
                seen |= comp
                assert len(comp) < len(F)
            nstrict += 1
    # lem:oim
    for G, lst in charts.items():
        best = min((c[0], c[1]) for c in lst)
        for (w, sp_, p, key, m, A) in lst:
            if (w, sp_) != best or is_line(m.E):
                continue
            for A2 in outers:
                G2 = canon(m.compose(A2))
                if G2 not in charts:
                    continue
                best2 = min((c[0], c[1]) for c in charts[G2])
                assert best2 == (w, sp_), ('lem:oim minimality', sorted(G2))
                assert all(c[2] % p == 0 for c in charts[G2]), ('lem:oim divisibility', sorted(G2), p)
                noim += 1
    for key, cls in classes.items():
        if not all(G in charts for G in cls):
            continue
        if any(is_line(c[4].E) for G in cls for c in charts[G]):
            continue
        mins = []
        for G in cls:
            best = min((c[0], c[1]) for c in charts[G])
            mins += [(G, c) for c in charts[G] if (c[0], c[1]) == best]
        pers = {c[2] for G, c in mins}
        least = min(c[2] for G in cls for c in charts[G])
        for p in pers:
            assert p % least == 0, ('least period divides', sorted(pers), least)
            for q in pers:
                assert not (p > 1 and q > 1 and gcd(p, q) == 1), ('coprime periods', sorted(pers))
        ncop += 1
        for G1, c1 in mins:
            for G2, c2 in mins:
                p, q = c1[2], c2[2]
                if p > q and p % q and gcd(p, q) > 1 and q // gcd(p, q) >= 2:
                    s1, t1 = phases(c1[4]) if c1[0] > 0 else (0, 0)
                    s2, t2 = phases(c2[4]) if c2[0] > 0 else (0, 0)
                    if c1[0] > 0 and c2[0] > 0 and s1 != t1 and s2 != t2:
                        npairs += 1
                        D = c1[5]
                        ribbon = len(D) == len({content(x) for x in D})
                        if ribbon and not is_line(D):
                            nnonline += 1
                        if ribbon and is_line(D):
                            nline += 1
                            nlineC += int(len(c2[5]) == len({content(x) for x in c2[5]}))
    print(f"strict-area charts {nstrict}; oim outer changes {noim}; classes without line chart checked {ncop}; "
          f"nondividing distinct-phase pairs {npairs} (nonline ribbon D: {nnonline}, line D: {nline}, with C ribbon: {nlineC})")
    assert nstrict > 0 and noim > 0 and ncop > 0
    assert nnonline == 0           # cor:nonline-outer-exit, on the instances found
    print("PASS")


if __name__ == "__main__":
    main()
