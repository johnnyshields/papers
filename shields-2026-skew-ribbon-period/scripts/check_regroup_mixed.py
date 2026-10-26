r"""Paper section `sec:reduction` (Reduction of the original comparison).

Mixed-case regrouping (`lem:regroup`, cases (c) and (d)) on small boards.

For every legal mixed mark `omega` on a small connected skew `E`, every connected row or column
`V` of `B` cells and every small connected `D1`, checks that the mark
`omega_B = (V o_omega E, W_B, B v, case)` with `W_B = {x in G : x + B v in G}` is legal, has the
width of `omega`, and satisfies `omega o (D1 o_empty V) = omega_B o D1`.

Cells are `(i, j)` with rows increasing southward; `content (i, j) = j - i`; `e = (1, 1)`.
"""

import itertools
import sys

E_CELL = (1, 1)


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def sub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def smul(k, x):
    return (k * x[0], k * x[1])


def content(x):
    return x[1] - x[0]


def translate(v, D):
    return frozenset(add(x, v) for x in D)


def contents(D):
    return {content(x) for x in D}


def span(D):
    return len(contents(D))


def diag_rows(D, k):
    return [x[0] for x in D if content(x) == k]


def diag_lo(D, k):
    r = diag_rows(D, k)
    return min(r) if r else 0


def diag_hi(D, k):
    r = diag_rows(D, k)
    return max(r) if r else 0


def min_content(D):
    return min(contents(D)) if D else 0


def max_content(D):
    return max(contents(D)) if D else 0


def sw(D):
    c = min_content(D)
    return (diag_lo(D, c), diag_lo(D, c) + c)


def ne(D):
    c = max_content(D)
    return (diag_lo(D, c), diag_lo(D, c) + c)


def vH(D):
    return add(sub(ne(D), sw(D)), (0, 1))


def adj(x, y):
    return abs(x[0] - y[0]) + abs(x[1] - y[1]) == 1


def is_skew(D):
    for x in D:
        for y in D:
            if x[0] <= y[0] and x[1] <= y[1]:
                for i in range(x[0], y[0] + 1):
                    for j in range(x[1], y[1] + 1):
                        if (i, j) not in D:
                            return False
    return True


def is_connected(D):
    if not D:
        return False
    D = set(D)
    start = next(iter(D))
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for d in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            y = add(x, d)
            if y in D and y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == len(D)


def is_cskew(D):
    return is_skew(D) and is_connected(D)


class Mark:
    def __init__(self, E, W, v, case):
        self.E = frozenset(E)
        self.W = frozenset(W)
        self.v = v
        self.case = case

    def upper(self):
        return translate(self.v, self.W)

    def middle(self):
        return self.E - (self.W | self.upper())

    def period(self):
        return content(self.v)

    def width(self):
        return span(self.W)

    def origin(self, D, d):
        c = content(d)
        if self.case == 'a':
            return add(smul(c, self.v), smul(d[0], E_CELL))
        if self.case == 'b':
            return sub(smul(c, self.v), smul(d[0], E_CELL))
        if self.case == 'c':
            return add(smul(c, self.v), smul(d[0] - diag_lo(D, c), E_CELL))
        return sub(smul(c, self.v), smul(diag_hi(D, c) - d[0], E_CELL))

    def same_ribbon(self, D, d):
        if (d[0] - 1, d[1]) not in D:
            return False
        c = content(d)
        if self.case == 'c':
            return d[0] - diag_lo(D, c) == (d[0] - 1) - diag_lo(D, c + 1)
        if self.case == 'd':
            return diag_hi(D, c) - d[0] == diag_hi(D, c + 1) - (d[0] - 1)
        return False

    def supp(self):
        return E_CELL if self.case == 'c' else (-1, -1)

    def compose(self, D):
        if not D:
            return self.W
        out = set()
        for d in D:
            out |= translate(self.origin(D, d), self.E)
        for d in D:
            if self.same_ribbon(D, d):
                out |= translate(add(self.origin(D, d), self.supp()), self.upper())
        return frozenset(out)

    # legality
    def attach(self):
        O = self.middle()
        if not O:
            return set()
        mn = min_content(O)
        mx = max_content(O)
        lows = [x for x in O if content(x) == mn]
        ups = [x for x in O if content(x) == mx]
        U = self.upper()
        res = set()
        if any((x[0], x[1] - 1) in self.W for x in lows):
            res.add('LH')
        if any((x[0] + 1, x[1]) in self.W for x in lows):
            res.add('LV')
        if any((x[0], x[1] + 1) in U for x in ups):
            res.add('UH')
        if any((x[0] - 1, x[1]) in U for x in ups):
            res.add('UV')
        return res

    def attachment_matches(self):
        a = self.attach()
        need = {'a': {'LH', 'UH'}, 'b': {'LV', 'UV'}, 'c': {'LH', 'UV'}, 'd': {'LV', 'UH'}}
        return need[self.case] <= a

    def well_formed(self):
        if not is_cskew(self.E):
            return False
        if not self.W:
            return self.v == vH(self.E) and self.case == 'a'
        U = self.upper()
        return (is_cskew(self.W) and self.W <= self.E and U <= self.E and sw(self.E) in self.W
                and ne(self.E) in U and self.attachment_matches())

    def maximal(self):
        W = self.W
        cW = contents(W)
        rest = [x for x in self.E if x not in W and content(x) in cW]
        for r in range(1, len(rest) + 1):
            for extra in itertools.combinations(rest, r):
                Wp = W | frozenset(extra)
                if not is_skew(Wp):
                    continue
                for x in Wp:
                    if translate(sub(ne(self.E), x), Wp) <= self.E:
                        return False
        return True

    def narrow(self):
        return 0 <= self.width() < self.period()

    def removals(self):
        return is_cskew(self.E - self.W) and is_cskew(self.E - self.upper())

    def in_union(self, x, K=12):
        return any(sub(x, smul(k, self.v)) in self.E for k in range(-K, K + 1))

    def no_hat_adj(self):
        O = self.middle()
        hatO = [x for x in O if add(x, E_CELL) in O]
        for m in range(-4, 5):
            W1 = translate(smul(m, self.v), self.W)
            hatW = set()
            for x in W1:
                if self.in_union(add(x, E_CELL)):
                    hatW.add(x)
                y = sub(x, E_CELL)
                if self.in_union(y):
                    hatW.add(y)
            for x in hatO:
                for y in hatW:
                    if adj(x, y):
                        return False
        return True

    def legal(self):
        return (self.well_formed() and self.maximal() and self.narrow() and self.removals()
                and self.no_hat_adj())


def empty_mark_h(V):
    return Mark(V, frozenset(), vH(V), 'a')


def skew_shapes(max_cells, max_rows=4, max_cols=5):
    """Connected skew diagrams lam/mu inside a box, normalized up to translation."""
    seen = set()
    for rows in range(1, max_rows + 1):
        for lam in itertools.product(range(max_cols + 1), repeat=rows):
            if any(lam[i] < lam[i + 1] for i in range(rows - 1)):
                continue
            for mu in itertools.product(range(max_cols + 1), repeat=rows):
                if any(mu[i] < mu[i + 1] for i in range(rows - 1)):
                    continue
                if any(mu[i] > lam[i] for i in range(rows)):
                    continue
                D = frozenset((i, j) for i in range(rows) for j in range(mu[i], lam[i]))
                if not D or len(D) > max_cells or not is_connected(D):
                    continue
                s = sw(D)
                key = translate(smul(-1, s), D)
                if key not in seen:
                    seen.add(key)
                    yield key


def legal_marks(E):
    """All legal nonempty marks on `E`."""
    s = sw(E)
    n = ne(E)
    cells = sorted(E)
    for r in range(1, len(cells)):
        for Wl in itertools.combinations(cells, r):
            W = frozenset(Wl)
            if s not in W or not is_cskew(W):
                continue
            for x in W:
                v = sub(n, x)
                if not translate(v, W) <= E:
                    continue
                for case in 'abcd':
                    m = Mark(E, W, v, case)
                    if m.legal():
                        yield m


def regroup_mixed(om, V, B):
    G = om.compose(V)
    v = smul(B, om.v)
    W = frozenset(x for x in G if add(x, v) in G)
    return Mark(G, W, v, om.case)


def main():
    lines = []
    for B in (2, 3):
        lines.append(frozenset((0, j) for j in range(B)))
        lines.append(frozenset((j, 0) for j in range(B)))
    outers = list(skew_shapes(4, 3, 3))
    n_marks = n_checks = 0
    fails = 0
    for E in skew_shapes(int(sys.argv[1]) if len(sys.argv) > 1 else 7):
        for om in legal_marks(E):
            if om.case not in 'cd':
                continue
            n_marks += 1
            for V in lines:
                B = len(V)
                omB = regroup_mixed(om, V, B)
                ok_leg = omB.legal()
                ok_w = omB.width() == om.width()
                if not (ok_leg and ok_w):
                    fails += 1
                    if fails < 8:
                        print("FAIL legal/width", sorted(E), sorted(om.W), om.v, om.case,
                              sorted(V), ok_leg, ok_w, sorted(omB.W))
                for D1 in outers:
                    X = empty_mark_h(V).compose(D1)
                    lhs = om.compose(X)
                    rhs = omB.compose(D1)
                    n_checks += 1
                    if lhs != rhs:
                        fails += 1
                        if fails < 8:
                            print("FAIL identity", sorted(E), sorted(om.W), om.v, om.case,
                                  sorted(V), sorted(D1))
    print(f"mixed marks {n_marks}, identity checks {n_checks}, failures {fails}")
    assert n_marks > 0
    assert fails == 0
    print("PASS")


if __name__ == "__main__":
    main()
