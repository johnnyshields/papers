r"""Paper section `sec:descent` (Strict descent and actual realization).

Check of `lem:ribbon-fiber` (sec:descent): the classification of ribbon Schur equality by
composition-factor reversal together with source-minimal domination.

For every ribbon F of weight <= NMAX, enumerate all proper legal charts (D, omega) of F
(omega a marked inner satisfying I-IV exactly as in SkewGluing/Mark.lean, D a ribbon with at
least two cells, F = translate of omega.compose D), take the source-minimal ones (least
(width, span E) lexicographically), and assert that every connected diagram H with the Schur
function of F lies in fiberClass(omega, s_D): H is a translate of A.compose omega or
A.compose omega.rotate for a connected A with s_A = s_D.  The converse (fiber inside class) is
asserted as well.  Connected diagrams with the Schur function of a ribbon are ribbons (the
class is read as the set of ribbons of the same weight with equal ribbon functions).

Usage: python3 check_ribbon_classification_fiber.py [NMAX]
"""
import sys
from itertools import combinations
from collections import defaultdict

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 8


# ---------------------------------------------------------------- diagrams
def content(x):
    return x[1] - x[0]


def tr(d, t):
    return frozenset((x[0] + t[0], x[1] + t[1]) for x in d)


def norm(d):
    if not d:
        return frozenset()
    a = min(x[0] for x in d)
    b = min(x[1] for x in d)
    return tr(d, (-a, -b))


def rot(d):
    return frozenset((-x[0], -x[1]) for x in d)


def is_skew(d):
    for x in d:
        for y in d:
            if x[0] <= y[0] and x[1] <= y[1]:
                for i in range(x[0], y[0] + 1):
                    for j in range(x[1], y[1] + 1):
                        if (i, j) not in d:
                            return False
    return True


def is_conn(d):
    if not d:
        return False
    seen = {next(iter(d))}
    st = list(seen)
    while st:
        x = st.pop()
        for y in ((x[0] + 1, x[1]), (x[0] - 1, x[1]), (x[0], x[1] + 1), (x[0], x[1] - 1)):
            if y in d and y not in seen:
                seen.add(y)
                st.append(y)
    return len(seen) == len(d)


def is_cs(d):
    return bool(d) and is_skew(d) and is_conn(d)


def contents(d):
    return {content(x) for x in d}


def min_c(d):
    return min(contents(d)) if d else 0


def max_c(d):
    return max(contents(d)) if d else 0


def diag_rows(d, k):
    return [x[0] for x in d if content(x) == k]


def diag_lo(d, k):
    r = diag_rows(d, k)
    return min(r) if r else 0


def diag_hi(d, k):
    r = diag_rows(d, k)
    return max(r) if r else 0


def sw(d):
    k = min_c(d)
    return (diag_lo(d, k), diag_lo(d, k) + k)


def ne(d):
    k = max_c(d)
    return (diag_lo(d, k), diag_lo(d, k) + k)


def span(d):
    return len(contents(d))


def interior(d):
    return [x for x in d if (x[0] + 1, x[1]) in d and (x[0], x[1] + 1) in d
            and (x[0] + 1, x[1] + 1) in d]


def ribbon_cells(comp):
    """Rows listed from the bottom row upward; each upper row starts above the last cell of
    the row below."""
    cells = set()
    row, col = 0, 0
    for k, r in enumerate(comp):
        for j in range(r):
            cells.add((row, col + j))
        col += r - 1
        row -= 1
    return frozenset(cells)


def compositions(n):
    if n == 0:
        yield ()
        return
    for a in range(1, n + 1):
        for rest in compositions(n - a):
            yield (a,) + rest


def comp_of_ribbon(d):
    rows = sorted({x[0] for x in d}, reverse=True)
    return tuple(sum(1 for x in d if x[0] == r) for r in rows)


# ------------------------------------------------------------ ribbon Schur
def ribbon_schur(comp):
    """Expansion of the ribbon function in the h-basis: a frozenset of (partition, coeff)."""
    n = len(comp)
    out = defaultdict(int)
    for mask in range(1 << (n - 1)):
        parts = []
        cur = comp[0]
        for i in range(1, n):
            if mask >> (i - 1) & 1:
                parts.append(cur)
                cur = comp[i]
            else:
                cur += comp[i]
        parts.append(cur)
        sign = (-1) ** (n - len(parts))
        out[tuple(sorted(parts, reverse=True))] += sign
    return frozenset((k, v) for k, v in out.items() if v)


# ------------------------------------------------------------ marked inners
def vH(E):
    a, b = ne(E), sw(E)
    return (a[0] - b[0], a[1] - b[1] + 1)


def smul(k, v):
    return (k * v[0], k * v[1])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


E1 = (1, 1)


class Mark:
    def __init__(self, E, W, v, case):
        self.E, self.W, self.v, self.case = E, W, v, case

    @property
    def upper(self):
        return tr(self.W, self.v)

    @property
    def width(self):
        return span(self.W)

    @property
    def period(self):
        return content(self.v)

    @property
    def middle(self):
        return self.E - (self.W | self.upper)

    def rotate(self):
        rc = {'a': 'a', 'b': 'b', 'c': 'd', 'd': 'c'}[self.case]
        return Mark(rot(self.E), rot(self.upper), self.v, rc)


def origin(w, D, d):
    c = content(d)
    if w.case == 'a':
        return add(smul(c, w.v), smul(d[0], E1))
    if w.case == 'b':
        return sub(smul(c, w.v), smul(d[0], E1))
    if w.case == 'c':
        return add(smul(c, w.v), smul(d[0] - diag_lo(D, c), E1))
    return sub(smul(c, w.v), smul(diag_hi(D, c) - d[0], E1))


def same_ribbon(w, D, d):
    if (d[0] - 1, d[1]) not in D:
        return False
    c = content(d)
    if w.case in ('a', 'b'):
        return False
    if w.case == 'c':
        return d[0] - diag_lo(D, c) == (d[0] - 1) - diag_lo(D, c + 1)
    return diag_hi(D, c) - d[0] == diag_hi(D, c + 1) - (d[0] - 1)


def compose(D, w):
    out = set()
    sh = E1 if w.case == 'c' else (-1, -1)
    for d in D:
        out |= tr(w.E, origin(w, D, d))
        if same_ribbon(w, D, d):
            out |= tr(w.upper, add(add(origin(w, D, d), sh), (0, 0)))
    return frozenset(out)


def adj(x, y):
    return abs(x[0] - y[0]) + abs(x[1] - y[1]) == 1


def attach_ok(w):
    O = w.middle
    if not O:
        return False
    lo = min_c(O)
    hi = max_c(O)
    lowH = any(content(x) == lo and (x[0], x[1] - 1) in w.W for x in O)
    lowV = any(content(x) == lo and (x[0] + 1, x[1]) in w.W for x in O)
    upH = any(content(x) == hi and (x[0], x[1] + 1) in w.upper for x in O)
    upV = any(content(x) == hi and (x[0] - 1, x[1]) in w.upper for x in O)
    return {'a': lowH and upH, 'b': lowV and upV, 'c': lowH and upV, 'd': lowV and upH}[w.case]


def is_maximal(w):
    rest = sorted(w.E - w.W)
    cw = contents(w.W)
    for r in range(1, len(rest) + 1):
        for extra in combinations(rest, r):
            Wp = w.W | frozenset(extra)
            if contents(Wp) != cw or not is_skew(Wp):
                continue
            for x in Wp:
                if tr(Wp, sub(ne(w.E), x)) <= w.E:
                    return False
    return True


def hat_clear(w):
    E = w.E
    win = E | tr(E, smul(-1, w.v))
    hat = {z for z in win if add(z, E1) in w.W} | {z for z in w.W if add(z, E1) in win}
    for k in (-1, 0):
        M = tr(w.middle, smul(k, w.v))
        for x in M:
            if add(x, E1) in M:
                for y in hat:
                    if adj(x, y):
                        return False
    return True


def legal_marks(E):
    """All legal marked inners on E (I-IV, well-formed)."""
    out = []
    # empty mark
    w = Mark(E, frozenset(), vH(E), 'a')
    if w.period > 0:
        out.append(w)
    cells = sorted(E)
    swE, neE = sw(E), ne(E)
    for r in range(1, len(cells) + 1):
        for sub_ in combinations(cells, r):
            W = frozenset(sub_)
            if swE not in W or not is_cs(W):
                continue
            for x in W:
                v = sub(neE, x)
                up = tr(W, v)
                if not up <= E:
                    continue
                for case in 'abcd':
                    w = Mark(E, W, v, case)
                    q = w.period
                    if not (0 <= w.width < q):
                        continue
                    if not attach_ok(w):
                        continue
                    if not (is_cs(E - W) and is_cs(E - up)):
                        continue
                    if not is_maximal(w) or not hat_clear(w):
                        continue
                    out.append(w)
    return out


# ------------------------------------------------------- composition cells
def cuts_of(comp):
    out, acc = set(), 0
    for r in comp[:-1]:
        acc += r
        out.add(acc)
    return out


def comp_from_cuts(cuts, n):
    pts = [0] + sorted(cuts) + [n]
    return tuple(pts[i + 1] - pts[i] for i in range(len(pts) - 1))


def product(g, e):
    """Composition product through its cuts: outer multiples, inner cuts repeated."""
    m, n = sum(g), sum(e)
    cg, ce = cuts_of(g), cuts_of(e)
    cuts = {x for x in range(1, m * n)
            if (x // n in cg if x % n == 0 else x % n in ce)}
    return comp_from_cuts(cuts, m * n)


def empty_mark(E):
    return Mark(E, frozenset(), vH(E), 'a')


def check_composition_cells(nmax):
    """Companions of the classification: the cells of the composition product are a
    translate of the empty-mark composite, the reversal is the rotation, and the empty mark
    of a rotated inner is the rotated mark."""
    count = 0
    for m in range(1, nmax + 1):
        for g in compositions(m):
            for n in range(1, nmax // m + 1):
                for e in compositions(n):
                    E = ribbon_cells(e)
                    w = empty_mark(E)
                    X = compose(ribbon_cells(g), w)
                    assert norm(X) == norm(ribbon_cells(product(g, e))), (g, e)
                    count += 1
    for n in range(1, nmax + 1):
        for e in compositions(n):
            E = ribbon_cells(e)
            assert norm(ribbon_cells(e[::-1])) == norm(rot(E)), e
            w, wr = empty_mark(E), empty_mark(rot(E))
            r = w.rotate()
            assert (wr.E, wr.W, wr.v, wr.case) == (r.E, r.W, r.v, r.case), e
    print("composition cells checked:", count)


# ------------------------------------------------------------------ main
def main():
    check_composition_cells(NMAX + 2)
    marks = []
    for m in range(2, NMAX):
        for c in compositions(m):
            marks.extend(legal_marks(ribbon_cells(c)))
    print("legal marks on ribbon inners:", len(marks))

    # charts of ribbons: (D composition, mark) -> normalized F
    charts = defaultdict(list)
    for w in marks:
        m = len(w.E)
        for r in range(2, NMAX + 1):
            if r * 1 + m > NMAX + m:  # no pruning beyond the size test below
                pass
            for c in compositions(r):
                D = ribbon_cells(c)
                if len(D) + len(w.E) - 1 > NMAX + 2 * len(w.E):
                    continue
                F = compose(D, w)
                if len(F) > NMAX or len(F) < 2:
                    continue
                if not is_cs(F) or interior(F):
                    continue
                charts[norm(F)].append((c, w))
    print("ribbons with a proper legal chart:", len(charts))

    by_size = defaultdict(list)
    for n in range(1, NMAX + 1):
        for c in compositions(n):
            by_size[n].append(c)
    schur = {c: ribbon_schur(c) for n in by_size for c in by_size[n]}
    cls = defaultdict(set)
    for n in by_size:
        for c in by_size[n]:
            cls[schur[c]].add(norm(ribbon_cells(c)))

    bad = 0
    tested = 0
    for F, lst in charts.items():
        best = min((w.width, span(w.E)) for _, w in lst)
        sm = [(c, w) for c, w in lst if (w.width, span(w.E)) == best]
        klass = cls[schur[comp_of_ribbon(F)]]
        for c, w in sm:
            Q = schur[c]
            fib = set()
            for A in cls[Q]:
                for ww in (w, w.rotate()):
                    fib.add(norm(compose(A, ww)))
            tested += 1
            if not klass <= fib:
                bad += 1
                miss = klass - fib
                print("FAIL class not in fiber: F =", comp_of_ribbon(F), "D =", c,
                      "mark(width, span E, case) =", (w.width, span(w.E), w.case),
                      "E =", comp_of_ribbon(w.E), "missing:", [comp_of_ribbon(x) for x in miss])
            if not fib <= klass:
                bad += 1
                print("FAIL fiber not in class: F =", comp_of_ribbon(F), "D =", c)
    print("source-minimal charts tested:", tested, "failures:", bad)
    assert bad == 0, "RibbonClassification fails as stated"
    print("PASS")


if __name__ == "__main__":
    main()
