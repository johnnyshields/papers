"""Independent exact checks for degree recovery and the two-component top tie.

Permutation expansion checks boards with and without unit entries, including all
common-beta deletions at once.  It also checks each of the three coefficient
extractions used for the general two-component lifting lemma.
"""
from collections import defaultdict
from itertools import combinations, permutations


def add(*polys):
    out = defaultdict(int)
    for p in polys:
        for mon, c in p.items():
            out[mon] += c
    return {mon: c for mon, c in out.items() if c}


def scale(p, c):
    return {mon: c*a for mon, a in p.items() if c*a}


def mul(p, q):
    out = defaultdict(int)
    for a, c in p.items():
        for b, d in q.items():
            out[tuple(sorted(a+b))] += c*d
    return {mon: c for mon, c in out.items() if c}


def coeff(p, j, power=1):
    return {tuple(k for k in mon if k != j): c for mon, c in p.items()
            if mon.count(j) == power}


def jt(x, y):
    out = defaultdict(int)
    for perm in permutations(range(len(x))):
        indices = [x[i]-y[j] for i, j in enumerate(perm)]
        if min(indices, default=0) < 0:
            continue
        inv = sum(perm[i] > perm[j] for i in range(len(x)) for j in range(i+1, len(x)))
        out[tuple(sorted(k for k in indices if k))] += (-1)**inv
    return {mon: c for mon, c in out.items() if c}


def delta(c, d, t):
    return add(jt((c[0]+t,)+c[1:], d), scale(jt(c, d[:-1]+(-t,)), -1))


def check_degrees():
    for n in range(1, 5):
        for xx in combinations(range(1, 8), n):
            x = xx[::-1]
            for yy in combinations(range(1, 7), n-1):
                y = yy[::-1] + (0,)
                if not all(x[i] > y[i] for i in range(n)):
                    continue
                if not all(x[i+1] >= y[i] for i in range(n-1)):
                    continue
                p = jt(x, y)
                common = set(x) & set(y)
                assert max(map(len, p)) == n
                assert min(map(len, p)) == n-len(common)
                residual = jt(tuple(a for a in x if a not in common),
                              tuple(b for b in y if b not in common))
                low = {mon: c for mon, c in p.items() if len(mon) == n-len(common)}
                assert low == residual or low == scale(residual, -1)
                assert (len(set(map(len, p))) == 1) == (not common)


def check_two_component_ties():
    for c, d in [((6, 4), (2, 0)), ((8, 6, 4), (3, 1, 0)),
                 ((9, 7, 3), (5, 1, 0))]:
        p = len(c)
        for e, f in [((8, 6, 4), (2, 1, 0)), ((9, 7, 5), (3, 1, 0))]:
            kappa = max(e[1], e[0]-f[-2])
            cr = coeff(delta(e, f, 1), kappa+1)
            assert cr
            for gap in (1, 2):
                t0 = kappa+gap+c[0]
                for u in (1, kappa+gap, kappa+gap+1):
                    large = c[0]+u
                    rows = (large,)+c
                    minors = [jt(rows[:i]+rows[i+1:], d) for i in range(p+1)]
                    polynomial = add(*(scale(mul(minors[i], delta(e, f, gap+c[i-1])),
                                             (-1)**(p-i)) for i in range(1, p+1)))
                    bq = jt(c[1:], d[:-1])
                    assert bq
                    assert coeff(minors[1], large) == scale(bq, (-1)**(p+1))
                    if t0 > large:
                        assert coeff(polynomial, t0) == scale(mul(minors[1], cr), (-1)**(p-1))
                    elif t0 == large:
                        assert coeff(polynomial, large, 2) == mul(bq, cr)
                    else:
                        assert coeff(coeff(polynomial, large), t0) == mul(bq, cr)


if __name__ == "__main__":
    check_degrees()
    check_two_component_ties()
    print("PASS: full-board degree recovery and all three two-component tie extractions")
