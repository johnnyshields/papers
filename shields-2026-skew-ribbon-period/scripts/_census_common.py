"""Census of connected skew diagrams and their proper charts, shared by the package checks.

`build(area, rows, cols, inner_cap)` returns the normalized connected skew diagrams of at most `area`
cells in a `rows x cols` box, their Schur classes (equal Jacobi--Trudi values at two seeded rational
alphabets), and every proper chart `G = A o_omega E` (`|A|, |E| >= 2`, `omega` any legal mark of any case or
the empty mark, composition built cell by cell) whose parent lies in the box, as
`charts[G] = [(width, span E, period, key, mark, outer)]`.
"""
from check_regroup_mixed import Mark, content, is_connected, legal_marks, skew_shapes, vH
from _schur_common import alphabet, schur

HS = (alphabet(61), alphabet(62))


def canon(S):
    mi = min(i for i, _ in S)
    mj = min(j for _, j in S)
    return frozenset((i - mi, j - mj) for i, j in S)


def rot(S):
    return canon(frozenset((-i, -j) for i, j in S))


def AT(S):
    return canon(frozenset((-j, -i) for i, j in S))


def skey(S):
    return tuple(schur(S, h) for h in HS)


def inner_key(E):
    orbit = {canon(E), rot(E), AT(E), rot(AT(E))}
    return min(tuple(sorted(x)) for x in orbit)


def is_line(S):
    return len({i for i, _ in S}) == 1 or len({j for _, j in S}) == 1


def build(area, rows, cols, inner_cap):
    shapes = [canon(S) for S in skew_shapes(area, rows, cols) if is_connected(S)]
    sch = {S: skey(S) for S in shapes}
    classes = {}
    for S in shapes:
        classes.setdefault(sch[S], []).append(S)
    inners = [E for E in shapes if 2 <= len(E) <= inner_cap]
    outers = [A for A in shapes if len(A) >= 2]
    charts = {}
    for E in inners:
        span = len({content(x) for x in E})
        for m in list(legal_marks(E)) + [Mark(E, frozenset(), vH(E), 'a')]:
            for A in outers:
                G = m.compose(A)
                if len(G) > area:
                    continue
                G = canon(G)
                if G not in sch:
                    continue
                charts.setdefault(G, []).append((m.width(), span, m.period(), (inner_key(E), m.period(), m.width()), m, A))
    return shapes, sch, classes, charts, outers
