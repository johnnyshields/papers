"""Paper sections `sec:profile-transport` (Profile transport) and
`sec:saturation-proof` (The repeated-block inverse); results
`lem:ribbon-endpoints`, `lem:total-contraction-inverse`,
`lem:inflation-lowering`, `cor:inflation-no-escape`.

Exact local checks of the two-residue decoder and its two-reading proof.

No mate-space census is used.  Sparse subset determinants are independently
checked by literal-cell complete permutation expansion on selected fixtures.
Controls reject weakening the bottom reading, ignoring endpoint orientation,
changing the decoder specialization, and reversing inflation no-escape.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, permutations, product
from time import monotonic

START = monotonic()


def progress(message):
    print(f"{monotonic()-START:.2f}s {message}", flush=True)


def normalize(x, y):
    t = min(y)
    return tuple(a-t for a in x), tuple(a-t for a in y)


def betas(profile):
    rows, gaps = profile
    y = [0] * len(rows)
    for i in range(len(rows)-2, -1, -1):
        y[i] = y[i+1] + rows[i+1] - gaps[i]
    return tuple(a+b for a, b in zip(rows, y)), tuple(y)


def connected(x, y):
    return (len(x) == len(y) > 0
            and all(a > b for a, b in zip(x, x[1:]))
            and all(a > b for a, b in zip(y, y[1:]))
            and all(a > b for a, b in zip(x, y))
            and all(a >= b for a, b in zip(x[1:], y)))


def profile(x, y):
    assert connected(x, y), (x, y)
    return (tuple(a-b for a, b in zip(x, y)),
            tuple(a-b for a, b in zip(x[1:], y)))


def cells(p):
    rows, gaps = p
    start, out = 0, set()
    for i, r in enumerate(rows):
        if i:
            start += gaps[i-1]+1-r
        out.update((i, j) for j in range(start, start+r))
    return out


def cell_betas(c):
    rs = sorted({i for i, j in c})
    x = tuple(max(j for ii, j in c if ii == i)+1-i for i in rs)
    y = tuple(min(j for ii, j in c if ii == i)-i for i in rs)
    return normalize(x, y)


def transpose(p):
    c = {(j, i) for i, j in cells(p)}
    return profile(*cell_betas(c))


def rotate(p):
    return p[0][::-1], p[1][::-1]


def layer(p, b, w):
    return tuple(b*x+w for x in p[0]), tuple(b*x+w for x in p[1])


def inflate(p, d):
    return tuple(x+d for x in p[0]), tuple(x+d for x in p[1])


def phi(p, b, w, d):
    a, z = betas(p)
    m = a[0]
    x = tuple(sorted([b*j+w for j in a]
                     + [b*j+d for j in range(m+1) if j not in z], reverse=True))
    y = tuple(b*j for j in range(m, -1, -1))
    assert connected(x, y)
    return profile(x, y)


@lru_cache(None)
def determinant(x, y):
    n = len(x)
    table = {0: {(): 1}}
    for i in range(n):
        nxt = {}
        for mask, terms in table.items():
            for j in range(n):
                a = x[i]-y[j]
                if mask >> j & 1 or a < 0:
                    continue
                sign = -1 if (mask >> (j+1)).bit_count() % 2 else 1
                out = nxt.setdefault(mask | 1 << j, defaultdict(int))
                for mon, coef in terms.items():
                    key = tuple(sorted(mon+(a,))) if a else mon
                    out[key] += sign*coef
        table = {mask: {m: c for m, c in terms.items() if c}
                 for mask, terms in nxt.items()}
    return tuple(sorted(table.get((1 << n)-1, {}).items()))


def poly(x, y):
    return dict(determinant(tuple(x), tuple(y)))


def cell_permutation(p):
    x, y = cell_betas(cells(p))
    out = defaultdict(int)
    for perm in permutations(range(len(x))):
        a = [x[i]-y[j] for i, j in enumerate(perm)]
        if min(a) < 0:
            continue
        sign = (-1)**sum(perm[i] > perm[j]
                         for i in range(len(x)) for j in range(i+1, len(x)))
        out[tuple(sorted(v for v in a if v))] += sign
    return {m: c for m, c in out.items() if c}


def proportional(p, q):
    return p == q or p == {m: -c for m, c in q.items()}


def top_child(x, y, w):
    sites = [(i, j) for i, a in enumerate(x) for j, b in enumerate(y) if a-b == w]
    ri, cj = {i for i, j in sites}, {j for i, j in sites}
    assert len(ri) == len(cj) == len(sites)
    assert all(i >= j for i, j in sites)
    left_r = [i for i in range(len(x)) if i not in ri]
    left_c = [j for j in range(len(y)) if j not in cj]
    assert all(i <= j for i, j in zip(left_r, left_c))
    r, s = tuple(x[i] for i in left_r), tuple(y[j] for j in left_c)
    assert all(a > b for a, b in zip(r, s))
    return len(sites), r, s, (-1)**sum(i+j for i, j in sites)


def coefficient(p, w, k):
    return {tuple(a for a in m if a != w): c for m, c in p.items() if m.count(w) == k}


def bottom(x, y):
    z = set(x) & set(y)
    a, b = tuple(v for v in x if v not in z), tuple(v for v in y if v not in z)
    assert connected(a, b)
    sign = (-1)**sum(x.index(t)+y.index(t) for t in z)
    return z, a, b, sign


def specialize(p, b, w, d, wrong=False):
    out = defaultdict(int)
    for mon, c in p.items():
        image = []
        for h in mon:
            if h % b == d:
                if h != d and not wrong:
                    break
            elif h % b == w:
                j = (h-w)//b
                if j:
                    image.append(j)
            else:
                raise AssertionError("third residue")
        else:
            out[tuple(sorted(image))] += c
    return {m: c for m, c in out.items() if c}


def lower(p, n, d):
    out = defaultdict(int)
    for m, c in p.items():
        if len(m) == n and min(m) >= d:
            out[tuple(a-d for a in m if a != d)] += c
    return {m: c for m, c in out.items() if c}


def profiles():
    for n in range(1, 6):
        for rows in product(range(1, 5), repeat=n):
            if sum(rows) > 10:
                continue
            for gaps in product(*(range(min(rows[i], rows[i+1])) for i in range(n-1))):
                yield rows, gaps


def verify_deletions():
    count = independent = 0
    for p in profiles():
        x, y = betas(p)
        assert connected(x, y) and cell_betas(cells(p)) == (x, y)
        s = poly(x, y)
        w = min(p[0])
        k, r, t, sign = top_child(x, y, w)
        assert max(m.count(w) for m in s) == k
        assert coefficient(s, w, k) == {m: sign*c for m, c in poly(r, t).items()}
        z, a, b, eps = bottom(x, y)
        q = len(a)
        assert min(map(len, s)) == q
        assert {m: c for m, c in s.items() if len(m) == q} == {
            m: eps*c for m, c in poly(a, b).items()}
        if count % 131 == 0:
            assert cell_permutation(p) == s
            independent += 1
        count += 1
    progress(f"arbitrary-profile deletion checks={count}; independent cell permutations={independent}")


def verify_decoder():
    count = control = 0
    for m in range(2, 5):
        for b in range(2, 5):
            y = tuple(b*j for j in range(m, -1, -1))
            for w in range(1, b):
                for d in range(w):
                    pool = sorted({b*j+r for j in range(m+1) for r in (d, w)}-{b*m+w})
                    for chosen in combinations(pool, m):
                        x = (b*m+w,)+tuple(sorted(chosen, reverse=True))
                        if not connected(x, y):
                            continue
                        a = tuple((v-w)//b for v in x if v % b == w)
                        u = {(v-d)//b for v in x if v % b == d}
                        z = tuple(j for j in range(m, -1, -1) if j not in u)
                        assert a[0] == m and z[-1] == 0 and m in u
                        assert 0 not in a and 0 not in u and connected(a, z)
                        q = profile(a, z)
                        assert betas(phi(q, b, w, d)) == (x, y)
                        assert proportional(specialize(poly(x, y), b, w, d), poly(a, z))
                        count += 1
                        if not proportional(specialize(poly(x, y), b, w, d, wrong=True), poly(a, z)):
                            control += 1
    assert control > 0
    progress(f"raw connected two-residue decoders={count}; wrong-specialization control rejects={control}")


def verify_readings():
    fixtures = [((2,), ()), ((1, 1, 1), (0, 0)), ((2, 3), (1,)),
                ((3, 2, 2), (1, 1)), ((2, 3, 3, 3), (1, 2, 2)),
                ((2, 3, 3), (0, 0)), ((3, 3, 2), (0, 0))]
    triples = [(2, 1, 0), (3, 1, 0), (3, 2, 0), (4, 3, 1),
               (4, 2, 0), (5, 3, 2), (6, 4, 2)]
    count = orientation_control = independent = 0
    for q, (b, w, d) in product(fixtures, triples):
        f = phi(q, b, w, d)
        x, y = betas(f)
        m, k, n = betas(q)[0][0], len(q[0]), len(x)
        assert n == m+1
        assert f[0].count(w) == 1 and f[0][0] == w and f[1][0] == d
        assert min(f[1]) == d and min(f[0]) == w
        assert x[0] == b*m+w
        assert sum(f[0]) == b*sum(q[0])+(w-d)*k+d*n
        s = poly(x, y)
        assert {sum(a % b == w for a in mon) for mon in s} == {k}
        kk, r, t, sign = top_child(x, y, w)
        assert kk == k
        assert coefficient(s, w, k) == {mon: sign*c for mon, c in poly(r, t).items()}
        qt = transpose(q)
        child_poly = poly(*betas(layer(qt, b, d)))
        assert poly(r, t) == child_poly
        for h in (f, rotate(f)):
            xx, yy = betas(h)
            kk, rr, ss, _ = top_child(xx, yy, w)
            u, v = xx[0]-max(rr), min(ss)
            assert u+v == w-d and (u == 0) != (v == 0)
            if u:
                assert h[0][0] == w
            if v:
                assert h[0][-1] == w
                orientation_control += any(t0 % b for t0 in ss)
                h = rotate(h)
                xx, yy = betas(h)
                kk, rr, ss, _ = top_child(xx, yy, w)
            assert min(ss) == 0 and xx[0] == b*m+w and yy[0] == b*m
            assert xx[1] == b*m+d
            assert all(a % b == d for a in rr) and all(a % b == 0 for a in ss)
            if d == 0:
                z, aa, bb, eps = bottom(xx, yy)
                assert len(z) == n-k
                assert poly(aa, bb) == poly(*betas(layer(q, b, w)))
                assert all(a % b == w for a in aa) and all(a % b == 0 for a in bb)
                assert set(rr) <= z and set(rr) == z
                assert set(yy) == set(range(0, b*m+1, b))
        base = phi(q, b, w-d, 0)
        assert inflate(base, d) == f
        if d:
            assert lower(s, n, d) == poly(*betas(base))
        if n <= 7:
            assert cell_permutation(f) == s
            independent += 1
        count += 1
        progress(f"source reading {count}/{len(fixtures)*len(triples)} done")
    assert orientation_control > 0
    progress(f"two-reading/orientation/lowering fixtures={count}; cell permutations={independent}; unoriented control={orientation_control}")


def verify_adversarial_controls():
    f = ((1, 2, 3, 3), (0, 1, 1))
    h = ((1, 3, 2, 3), (0, 1, 1))
    fp, hp = poly(*betas(f)), poly(*betas(h))
    assert coefficient(fp, 1, 3) == coefficient(hp, 1, 3)
    assert min(map(len, fp)) == 3 and min(map(len, hp)) == 2
    assert {sum(v % 2 for v in mon) for mon in fp} == {3}
    assert {sum(v % 2 for v in mon) for mon in hp} == {1, 3}
    assert len([mon for mon in hp if sum(v % 2 for v in mon) == 1]) == 5
    x, y = betas(h)
    _, r, _, _ = top_child(x, y, 1)
    z, _, _, _ = bottom(x, y)
    assert len(r) != len(z)
    h2 = ((1, 2, 3, 2), (0, 0, 1))
    f2 = ((1, 2, 2, 3), (0, 0, 1))
    x, y = betas(h2)
    z, a, bb, _ = bottom(x, y)
    _, r, _, _ = top_child(x, y, 1)
    h2p, f2p = poly(x, y), poly(*betas(f2))
    assert coefficient(h2p, 1, 2) == coefficient(f2p, 1, 2)
    assert min(map(len, h2p)) == min(map(len, f2p)) == 2
    assert len(r) == len(z)
    assert any(v % 2 != 1 for v in a) and any(v % 2 for v in bb)
    assert h2p != f2p
    # A complete equality can be lost by inflation: no-escape is not an iff.
    a = ((2, 3, 3), (0, 0))
    b = ((3, 2, 3), (0, 0))
    assert poly(*betas(a)) != poly(*betas(b))
    # The eight-cell four-row class supplies a nonrotation equality.
    a = ((1, 2, 2, 3), (0, 0, 1))
    b = ((1, 2, 3, 2), (0, 1, 0))
    assert poly(*betas(a)) == poly(*betas(b))
    assert a != b and a != rotate(b)
    split = None
    for d in range(1, 5):
        aa, bb = inflate(a, d), inflate(b, d)
        ap, bp = poly(*betas(aa)), poly(*betas(bb))
        assert lower(ap, len(a[0]), d) == poly(*betas(a))
        assert lower(bp, len(b[0]), d) == poly(*betas(b))
        if ap != bp:
            split = d
            break
    assert split is not None
    for p in (f, h, h2, a, b, inflate(a, split), inflate(b, split)):
        assert cell_permutation(p) == poly(*betas(p))
    # An exact finite set check of the deduction, independently of determinant code.
    set_tests = 0
    for b in range(2, 5):
        for w in range(1, b):
            universe = range(1, 2*b+1)
            for xx in combinations(universe, 4):
                for zz in combinations(xx, 2):
                    if not all(a % b == w for a in set(xx)-set(zz)):
                        continue
                    for rr in combinations(xx, 2):
                        if all(a % b == 0 for a in rr):
                            assert set(rr) == set(zz)
                            set_tests += 1
    assert set_tests > 0
    # Equicardinality and a grid retained set alone do not identify the sets.
    xx, zz, rr = {3, 4, 6, 7}, {4, 6}, {3, 6}
    assert rr <= xx and len(rr) == len(zz) and all(v % 3 == 0 for v in rr)
    assert rr != zz and any(v % 3 != 1 for v in xx-zz)
    progress(f"controls: wrong bottom degree, wrong bottom layer, equicardinality alone, residue-degree-one outsider, inflation splits at d={split}; set deduction cases={set_tests}")


if __name__ == "__main__":
    verify_deletions()
    verify_decoder()
    verify_readings()
    verify_adversarial_controls()
    progress("ALL PASS")
