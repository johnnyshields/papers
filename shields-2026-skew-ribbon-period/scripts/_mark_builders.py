"""Connected skew diagrams, legal marks, mark phases and beta lists for the sweeps in this directory.

Import-only; asserts nothing about the paper.  `diagrams` enumerates every connected skew diagram
of at most a given number of cells by its row-length and overlap profile, `marks` every legal mark
of a diagram (the empty mark included), `phases` the two middle phases of a mark, and `betas` the
decreasing row and column lists of a diagram normalized to start at content zero.
"""
from _gluing_common import content, empty_mark, from_profile, intersection_mark


def compositions(n):
    if n == 0:
        yield ()
        return
    for k in range(1, n + 1):
        for rest in compositions(n - k):
            yield (k,) + rest


def diagrams(max_cells, min_cells=2):
    seen = set()
    for n in range(min_cells, max_cells + 1):
        for lengths in compositions(n):
            def gaps_for(i):
                if i == len(lengths) - 1:
                    yield ()
                    return
                for g in range(min(lengths[i], lengths[i + 1])):
                    for rest in gaps_for(i + 1):
                        yield (g,) + rest
            for gaps in gaps_for(0):
                D = from_profile(list(lengths), list(gaps))
                if D not in seen:
                    seen.add(D)
                    yield D


def betas(D):
    rows = {}
    for i, j in D:
        rows.setdefault(i, []).append(j - i)
    m = min(content(c) for c in D)
    X = sorted((max(v) + 1 - m for v in rows.values()), reverse=True)
    Y = sorted((min(v) - m for v in rows.values()), reverse=True)
    return X, Y


def marks(E):
    yield empty_mark(E)
    for cell in E:
        try:
            mk = intersection_mark(E, cell)
        except AssertionError:
            continue
        yield mk


def phases(mk):
    """The middle phases (s, t) of a mark, (0, 0) for the empty mark."""
    if not mk.lower:
        return 0, 0
    E, q, w = mk.inner, mk.period, mk.width
    p = mk.displacement[0]
    m = min(content(c) for c in E)

    def lo(a):
        return min(i for i, j in E if j - i == m + a)

    def hi(a):
        return max(i for i, j in E if j - i == m + a)

    dlo = [lo(a + q) - p - lo(a) for a in range(w)]
    dhi = [hi(a + q) - p - hi(a) for a in range(w)]
    lower = [dlo[a] > 0 or dhi[a] < 0 for a in range(w)]
    upper = [dlo[a] < 0 or dhi[a] > 0 for a in range(w)]
    s = next((a for a in range(w) if lower[a]), w)
    t = next((a for a in range(w) if not upper[a]), w)
    assert all(lower[a] == (a >= s) for a in range(w))
    assert all(upper[a] == (a < t) for a in range(w))
    return s, t
