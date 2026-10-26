r"""Paper section `app:coincident` (Positive coincident attachment phases).

The three geometric clauses of the one-coincident band geometry, and the wide-side heights
(`app:coincident`, `lem:one-coincident-entry`; `CoincidentClassPeriodic`,
`CoincidentSeamLine` in `lean/SkewRibbonPeriod/Reduction/One/GeometryBands.lean`,
`CounterpartHeightsOne` and `CounterpartBandSingleOne` in
`lean/SkewRibbonPeriod/Reduction/CounterpartBand.lean`).

Coincident source `S = omega o D`, `omega` legal case (a), phases `0 < s = t < u`, period `A g`,
`D` a ribbon of `m >= 2` cells (not necessarily a line), with `P(g, u)` heights and one span-`u`
component per internal band.  Asserted: the set of component classes of band `i` equals that of
band `i + A` whenever `A` does not divide `i`; and a class occurring at every seam `t A`,
`1 <= t < m`, forces `D` to be a line.  Wide side `T = omega o Row_j`, `omega` ordinary case (a)
with phases `s = t + k g`, period `B g`, width `u + k g`: whenever it has `P(g, u)` heights (none
of the tested wide marks does, as the wide parent is not available outside an actual comparison),
height at least two and one span-`u` component on every internal band; and the height-profile
statement `LinePrimeHeights` over a line native.
"""

from check_band_single_component import components, interior
from check_line_charge import phases
from check_regroup_mixed import content, legal_marks, min_content, skew_shapes, sw, translate
from check_top_seam_form import heights_ok, jt


def row(m):
    return frozenset((0, j) for j in range(m))


def is_line(D):
    return len({x[0] for x in D}) == 1 or len({x[1] for x in D}) == 1


def band_comps(S, g, u, L):
    c0 = min_content(S)
    comps = components(interior(S))
    out = {}
    for i in range(1, L):
        lo, hi = c0 + i * g, c0 + i * g + u - 1
        out[i] = [C for C in comps if all(lo <= content(x) <= hi for x in C)]
    return out


def heights_two(S, g, u, L):
    c0 = min_content(S)
    for i in range(1, L):
        for c in range(c0 + i * g, c0 + i * g + u):
            if sum(1 for x in S if content(x) == c) < 2:
                return False
    return True


def source(stats):
    ribbons = [D for D in skew_shapes(5, 4, 5) if not interior(D)]
    for E in skew_shapes(12, 4, 7):
        for om in legal_marks(E):
            if om.case != 'a':
                continue
            u = om.width()
            s, t = phases(om)
            if not (s == t and 0 < s < u and u >= 2):
                continue
            P = om.period()
            for g in range(u + 1, P):
                if P % g or P // g < 2:
                    continue
                A = P // g
                for D in ribbons:
                    m = len(D)
                    if m < 2:
                        continue
                    S = om.compose(D)
                    L = m * A
                    if heights_ok(S, g, u) != L:
                        continue
                    bc = band_comps(S, g, u, L)
                    if any(len(bc[i]) != 1 or len({content(x) for x in bc[i][0]}) != u
                           for i in bc):
                        continue
                    stats['src'] += 1
                    cls = {i: {str(jt(bc[i][0]))} for i in bc}
                    for i in range(1, L - A):
                        if i % A:
                            assert cls[i] == cls[i + A], (sorted(E), sorted(om.W), g, sorted(D), i)
                            stats['per'] += 1
                    common = set.intersection(*[cls[t * A] for t in range(1, m)])
                    if common:
                        assert is_line(D), (sorted(E), sorted(om.W), g, sorted(D))
                        stats['seam'] += 1
                    if not is_line(D):
                        stats['nonline'] += 1
                        if not common:
                            stats['nonline_nocommon'] += 1


def wide(stats):
    for E in skew_shapes(13, 4, 9):
        for om in legal_marks(E):
            if om.case != 'a':
                continue
            w = om.width()
            s, t = phases(om)
            P = om.period()
            if s <= t:
                continue
            for g in range(3, P):
                if P % g or P // g < 2 or (s - t) % g:
                    continue
                B = P // g
                k = (s - t) // g
                u = w - k * g
                if k < 1 or not (2 <= u < g) or not (0 <= t <= u):
                    continue
                for j in (2, 3):
                    T = om.compose(row(j))
                    L = j * B + k
                    if heights_ok(T, g, u) != L:
                        stats['wide_noP'] += 1
                        continue
                    assert heights_two(T, g, u, L), (sorted(E), sorted(om.W), g, j)
                    bc = band_comps(T, g, u, L)
                    for i in range(1, L):
                        assert len(bc[i]) == 1, (sorted(E), sorted(om.W), g, j, i)
                        assert len({content(x) for x in bc[i][0]}) == u
                    stats['wide'] += 1


def profile(S):
    c0 = min_content(S)
    n = len({content(x) for x in S})
    return tuple(sum(1 for x in S if content(x) == c0 + k) for k in range(n))


def rotated(D):
    R = frozenset((-x[0], -x[1]) for x in D)
    s = sw(R)
    return translate((-s[0], -s[1]), R)


def line_transport(stats):
    """`LinePrimeHeights` in `lean/SkewRibbonPeriod/Reduction/One/PairHeights.lean`: a line native
    over two Schur-equal ribbon outers (a ribbon and its rotation) gives parents whose height
    profiles agree or are reversed."""
    ribbons = [D for D in skew_shapes(6, 5, 6) if not interior(D)]
    for n in range(3, 8):
        for E in (frozenset((0, j) for j in range(n)), frozenset((j, 0) for j in range(n))):
            for om in legal_marks(E):
                for D in ribbons:
                    a, b = profile(om.compose(D)), profile(om.compose(rotated(D)))
                    assert a == b or a == b[::-1], (n, om.case, sorted(om.W), om.v, sorted(D))
                    stats['line_prime'] += 1


def main():
    stats = dict(src=0, per=0, seam=0, nonline=0, nonline_nocommon=0, wide=0, wide_noP=0, line_prime=0)
    source(stats)
    wide(stats)
    line_transport(stats)
    print(stats)
    assert stats['src'] > 0 and stats['per'] > 0 and stats['line_prime'] > 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
