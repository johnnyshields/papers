r"""Paper section `sec:descent` (Strict descent and actual realization).

`prop:class-quotient` / `eq:class-quotient`, and the same statement consumed as `prop:aligned-reconstruction` /
`eq:aligned-reference` (the divisible case `p = k q`), and `cor:integer-exit`, on the census of
`_census_common` (all connected skew diagrams up to 12 cells in a 5 x 6 box; every proper chart whose
inner has at most 7 cells).

Instances are found forward: two Schur-equal diagrams `F`, `H` (same class) carrying proper charts
`F = D o_omega E`, `H = C o_eta U` with periods `p = k q`, `k >= 2`, and widths `w_s = b q + w_f`, `0 <= b < k`
(`b` is read from the widths, so instances with `q` not dividing `w_s - w_f` are excluded, as the
statement writes them).  The class is also required to be rooted (every member has a chart), the
census analogue of "full source-minimal fibers".  Asserted on every instance: some connected skew
diagram `J` of span `k + b` has `s_E = s_{J o_eta U}`.  For `cor:integer-exit` the same census asserts
that source-minimal charts (least `(width, span E)`) of two members of one class never have periods in
the ratio `p = k q`, `k >= 2` (the corollary excludes it for the original comparison; classes
containing a proper line-inner chart are excluded as in the main theorem).
Control: the count of instances whose widths violate the divisibility `q | w_s - w_f` (the hypothesis
`w_s = b q + w_f` is load-bearing exactly when this is positive and the conclusion fails there).
Sampled: the census box; the `J`-package and full-fiber hypotheses hold on the census only as far as
`check_package_census` verifies them.
"""
from _census_common import build, skey, is_line
from _schur_common import schur
from _census_common import HS


def main():
    shapes, sch, classes, charts, outers = build(12, 5, 6, 7)
    ninst = nfail_div = ncontrol = nexit = 0
    spans = {}
    for key, cls in classes.items():
        if not all(G in charts for G in cls):
            continue
        has_line = any(is_line(c[4].E) for G in cls for c in charts[G])
        allc = [(G, c) for G in cls for c in charts[G]]
        for G, cf in allc:
            for H, ch in allc:
                p, q = cf[2], ch[2]
                if not (p % q == 0 and p // q >= 2):
                    continue
                k = p // q
                ws, wf = cf[0], ch[0]
                E, U, eta = cf[4].E, ch[4].E, ch[4]
                if (ws - wf) % q or not 0 <= (ws - wf) // q < k:
                    ncontrol += 1
                    continue
                b = (ws - wf) // q
                target = tuple(schur(E, h) for h in HS)
                found = False
                for J in outers:
                    if len({x[1] - x[0] for x in J}) == k + b:
                        if tuple(schur(eta.compose(J), h) for h in HS) == target:
                            found = True
                            break
                assert found, ('class quotient', sorted(E), sorted(U), p, q, ws, wf)
                ninst += 1
        if not has_line:
            mins = []
            for G in cls:
                best = min((c[0], c[1]) for c in charts[G])
                mins += [c[2] for c in charts[G] if (c[0], c[1]) == best]
            for p in mins:
                for q in mins:
                    assert not (p % q == 0 and p // q >= 2), ('integer exit', mins)
            nexit += 1
    print(f"class-quotient instances {ninst}; widths outside the divisibility form {ncontrol}; classes without line-inner chart checked for integer-exit {nexit}")
    assert ninst > 0 and nexit > 0
    print("PASS")


if __name__ == "__main__":
    main()
