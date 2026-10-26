"""Exact Jacobi--Trudi diagnostics using independent permutation expansion.

Checks the displayed parent/marker identities, endpoint remainder, explicit
quartets, marked cell unions, and the non-dense resonance.  The finite examples
are diagnostics, not a substitute for the uniform proofs.  Standard library only.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import permutations, product


def add(*terms):
    out = defaultdict(int)
    for p in terms:
        for mon, c in p.items():
            out[mon] += c
    return {mon: c for mon, c in out.items() if c}


def scale(p, c):
    return {mon: c * a for mon, a in p.items() if c * a}


def mul(*terms):
    out = {(): 1}
    for p in terms:
        nxt = defaultdict(int)
        for a, c in out.items():
            for b, d in p.items():
                nxt[tuple(sorted(a + b))] += c * d
        out = {mon: c for mon, c in nxt.items() if c}
    return out


def h(j):
    return {} if j < 0 else ({(): 1} if j == 0 else {(j,): 1})


def coeff(p, j, power=1):
    return {tuple(k for k in mon if k != j): c for mon, c in p.items()
            if mon.count(j) == power}


def top(p):
    return max((max(mon, default=0) for mon in p), default=-1)


@lru_cache(None)
def jt(x, y):
    assert len(x) == len(y)
    out = defaultdict(int)
    for perm in permutations(range(len(x))):
        indices = tuple(x[i] - y[j] for i, j in enumerate(perm))
        if min(indices, default=0) < 0:
            continue
        sign = (-1) ** sum(perm[i] > perm[j]
                          for i in range(len(x)) for j in range(i + 1, len(x)))
        out[tuple(sorted(k for k in indices if k))] += sign
    return {mon: c for mon, c in out.items() if c}


def rotate(q):
    x, y = q
    return tuple(x[0] - t for t in y[::-1]), tuple(x[0] - t for t in x[::-1])


def up(q, t):
    x, y = q
    return jt((x[0] + t,) + x[1:], y)


def down(q, t):
    x, y = q
    return jt(x, y[:-1] + (y[-1] - t,))


def delta(q, t):
    return add(up(q, t), scale(down(q, t), -1))


def phi(q, u, v):
    x, y = q
    return jt((x[0] + u,) + x, y + (-v,))


def profile(q):
    x, y = q
    return (tuple(a - b for a, b in zip(x, y)),
            tuple(x[i + 1] - y[i] for i in range(len(x) - 1)))


def shape(q):
    x, y = q
    return tuple(c for c in reversed([sum(a < b for b in y) for a in x]) if c)


def forms(q, ell, m, g1, g2, u, v):
    c, d = q
    s, left, right = c[0], ell + g1, m + g2
    n = s + left + right + u + v
    end = ((n, n-u, s+right+v) + tuple(v+a for a in c),
           (n-u-ell, s+right+v-m) + tuple(v+a for a in d) + (0,))
    middle = ((n, n-u) + tuple(v+right+a for a in c) + (v+m,),
              (n-u-ell,) + tuple(v+right+a for a in d) + (v, 0))
    return end, middle, left, right, n


def check_dense():
    cores = [((9, 7, 6, 4), (3, 2, 1, 0)),
             ((10, 9, 8, 6), (4, 3, 1, 0)),
             ((8, 7, 6, 5), (3, 2, 1, 0))]
    cores += [rotate(cores[0])]
    fixtures = [(1, 2, 1, 2, 1, 3), (2, 1, 2, 1, 3, 1),
                (1, 2, 1, 1, 2, 2), (1, 1, 1, 1, 1, 3),
                (1, 2, 1, 1, 1, 4), (2, 1, 2, 1, 1, 2),
                (1, 1, 2, 1, 10, 11)]
    for q in cores:
        c, d = q
        s, kappa = c[0], max(c[1], c[0] - d[-2])
        f = jt(*q)
        if q != rotate(q):
            leading = None
            for t in (1, 2, 5):
                diff = delta(q, t)
                assert top(diff) == kappa + t
                cq = coeff(diff, kappa + t)
                assert cq
                assert leading is None or leading == cq
                leading = cq
                assert add(diff, scale(mul(h(kappa+t), cq), -1))
        else:
            assert not delta(q, 2)
        for ell, m, g1, g2, u, v in fixtures:
            end, middle, left, right, n = forms(q, ell, m, g1, g2, u, v)
            pe, pm = jt(*end), jt(*middle)
            al = add(mul(h(ell+u), h(m+left)),
                     scale(mul(h(ell), h(m+left+u)), -1))
            uq = add(mul(h(ell+u), up(q, left)),
                     scale(mul(h(ell), up(q, left+u)), -1))
            assert pe == add(mul(al, phi(q, right, v)),
                             scale(mul(h(m), h(ell+u), phi(q, left+right, v)), -1),
                             mul(h(ell), h(m), phi(q, left+right+u, v)))
            assert pm == add(mul(h(ell+u), h(m+v), phi(q, left, right)),
                             scale(mul(h(ell), h(m+v), phi(q, left+u, right)), -1),
                             scale(mul(h(ell+u), h(m), phi(q, left, right+v)), -1),
                             mul(h(ell), h(m), phi(q, left+u, right+v)))
            assert coeff(pe, n) == coeff(pm, n) == mul(h(ell), h(m), f)
            qe = min(u, v)
            if u < v:
                ce = cm = scale(mul(h(m), h(ell+u), f), -1)
            elif v < u:
                ce = scale(mul(h(ell), h(m), down(q, v)), -1)
                cm = scale(mul(h(ell), h(m+v), f), -1)
            else:
                ce = scale(mul(h(m), add(mul(h(ell+u), f),
                                          mul(h(ell), down(q, u)))), -1)
                cm = scale(mul(f, add(mul(h(m), h(ell+u)),
                                      mul(h(ell), h(m+u)))), -1)
            assert coeff(pe, n-qe) == ce
            assert coeff(pm, n-qe) == cm
            if u < v:
                common = mul(f, add(mul(h(ell), h(m), h(n)),
                                    scale(mul(h(m), h(ell+u), h(n-u)), -1)))
                re, rm = add(pe, scale(common, -1)), add(pm, scale(common, -1))
                k = max(n-v, n-u-left)
                e1 = scale(mul(h(ell), h(m), down(q, v)), -1)
                e2 = mul(al, f)
                m1 = scale(mul(h(ell), h(m+v), f), -1)
                m2 = mul(h(m), uq)
                ec = add(e1 if k == n-v else {}, e2 if k == n-u-left else {})
                mc = add(m1 if k == n-v else {}, m2 if k == n-u-left else {})
                assert top(re) == top(rm) == k
                assert coeff(re, k) == ec
                assert coeff(rm, k) == mc
            # A nonsymmetric core may only reverse by a whole-parent rotation.
            if q != rotate(q):
                end_r, middle_r, *_ = forms(rotate(q), ell, m, g1, g2, u, v)
                assert pe != jt(*end_r)
                assert (pm == jt(*middle_r)) == (middle == rotate(middle_r))


def check_quartets():
    for a, d in product(range(1, 3), range(2)):
        for b in (a+d+1, a+d+2):
            y = tuple(b*i for i in range(6, -1, -1))
            xf = (a+6*b+d, 6*b+d, a+5*b+d, 5*b+d, a+4*b+d, a+3*b+d, 3*b+d)
            xh = (a+6*b+d, 6*b+d, a+5*b+d, 5*b+d, a+4*b+d, 4*b+d, a+2*b+d)
            fq, hq = (xf, y), (xh, y)
            assert jt(*fq) == jt(*hq)
            assert shape(fq) == (3, 3, 2, 1, 1)
            assert shape(hq) == (4, 2, 2, 1, 1)
            assert len({fq, hq, rotate(fq), rotate(hq)}) == 4
            assert sum(profile(fq)[0]) == 4*a+11*b+7*d
            A, B, beta = a+d, b+d, b-1
            e = {(0, j) for j in range(beta, beta+A)} | {(1, j) for j in range(B)}
            wne = {(0, j) for j in range(beta, beta+A)}
            tau, eta = (-1, b-1), (1, 1)
            def translate(cells, i, j):
                return {(r+i*tau[0]+j*eta[0], c+i*tau[1]+j*eta[1]) for r, c in cells}
            base = set().union(*(translate(e, i, 0) for i in range(6)),
                               *(translate(e, i, 1) for i in range(1, 5)))
            unions = (base | translate(e, 2, 2) | translate(wne, 3, 2),
                      base | translate(e, 3, 2) | translate(wne, 1, 2))
            for cells, target in zip(unions, (fq, hq)):
                rows = [sorted(c for rr, c in cells if rr == r)
                        for r in sorted({r for r, c in cells})]
                assert all(row == list(range(row[0], row[-1]+1)) for row in rows)
                lengths = tuple(map(len, rows))
                overlaps = tuple(len(set(rows[i]) & set(rows[i+1]))-1 for i in range(6))
                assert (lengths, overlaps) == profile(target), (a, b, d, lengths, overlaps)
    for b in range(1, 4):
        for q in range(1, b+1):
            for g in (b+1, b+2):
                x = tuple(b+i*g for i in range(5, -1, -1))
                ys = [((3*g+q, 2*g, g+q, g, q, 0), (3*g, 2*g+q, g+q, g, q, 0)),
                      ((4*g+q, 2*g+q, g+q, g, q, 0), (3*g+q, 2*g+q, 2*g, g+q, q, 0)),
                      ((4*g+q, 3*g+q, g+q, g, q, 0), (3*g+q, 3*g, 2*g+q, g+q, q, 0))]
                expected = [((4, 2, 1), (4, 2, 1)),
                            ((4, 2, 1, 1), (4, 3, 1)),
                            ((4, 2, 2, 1), (4, 3, 2))]
                for pair, shapes in zip(ys, expected):
                    fs, hs = (x, pair[0]), (x, pair[1])
                    assert jt(*fs) == jt(*hs)
                    assert (shape(fs), shape(hs)) == shapes
                    assert len({fs, hs, rotate(fs), rotate(hs)}) == 4
                if q < b:
                    small = ((b+2*g, b+2*g-q, b+g-q), (2*g, g, 0))
                    # The matrix printed for Q determines these beta lists.
                    s = b-q
                    f = jt(*small)
                    assert add(mul(h(b), up(small, g-q)),
                               scale(mul(h(s+g), f), -1)) == mul(h(s), delta(small, g))
                    assert coeff(f, b+2*g) == mul(h(s), h(s))
                    diff = delta(small, g)
                    assert top(diff) == s+3*g
                    assert coeff(diff, s+3*g) == mul(h(b), h(s))
                    rem = add(diff, scale(mul(h(s+3*g), h(b), h(s)), -1))
                    assert top(rem) == b+2*g
                    assert coeff(rem, b+2*g) == scale(mul(h(s), h(s+g)), -1)


if __name__ == "__main__":
    check_dense()
    check_quartets()
    print("PASS: exact parent identities, marker tables, endpoint remainder, quartet geometry, and resonance diagnostics")
