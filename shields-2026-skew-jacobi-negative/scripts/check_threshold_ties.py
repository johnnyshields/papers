"""Exact attacks on tied coefficients and recovered-component assembly.

Determinants use a subset dynamic program, not permutation enumeration.  The
finite collision windows below are diagnostics only; they do not establish the
uniform rigidity theorems.  Each collision must be a literal whole rotation.
"""
from __future__ import annotations

from bisect import insort
from collections import defaultdict
from functools import lru_cache
from itertools import combinations, product


def add(*polynomials):
    out = defaultdict(int)
    for p in polynomials:
        for mon, c in p.items():
            out[mon] += c
    return {mon: c for mon, c in out.items() if c}


def scale(p, c):
    return {mon: c * value for mon, value in p.items() if c * value}


def mul(*polynomials):
    out = {(): 1}
    for p in polynomials:
        nxt = defaultdict(int)
        for a, c in out.items():
            for b, d in p.items():
                nxt[tuple(sorted(a + b))] += c * d
        out = {mon: c for mon, c in nxt.items() if c}
    return out


def h(j):
    return {} if j < 0 else ({(): 1} if j == 0 else {(j,): 1})


def coefficient(p, index, power=1):
    return {tuple(k for k in mon if k != index): c for mon, c in p.items()
            if mon.count(index) == power}


def largest(p):
    return max((max(mon, default=0) for mon in p), default=-1)


@lru_cache(maxsize=512)
def jt(x, y):
    """Signed matching DP: mask records columns already assigned to rows."""
    assert len(x) == len(y)
    n = len(x)
    layer = {0: {(): 1}}
    for i in range(n):
        following = {}
        for mask, polynomial in layer.items():
            for j in range(n):
                if mask & (1 << j):
                    continue
                index = x[i] - y[j]
                if index < 0:
                    continue
                sign = -1 if (mask >> (j + 1)).bit_count() % 2 else 1
                target = following.setdefault(mask | (1 << j), defaultdict(int))
                for mon, c in polynomial.items():
                    if index:
                        extended = list(mon)
                        insort(extended, index)
                        term = tuple(extended)
                    else:
                        term = mon
                    target[term] += sign * c
        layer = {mask: {mon: c for mon, c in p.items() if c}
                 for mask, p in following.items()}
    return layer.get((1 << n) - 1, {})


def rotation(q):
    x, y = q
    assert y[-1] == 0
    return tuple(x[0] - j for j in reversed(y)), tuple(x[0] - i for i in reversed(x))


def orbit(q):
    return min(q, rotation(q))


def up(q, t):
    x, y = q
    return jt((x[0] + t,) + x[1:], y)


def down(q, t):
    x, y = q
    return jt(x, y[:-1] + (-t,))


def delta(q, t):
    return add(up(q, t), scale(down(q, t), -1))


def validate(q):
    x, y = q
    assert len(x) == len(y) and y[-1] == 0
    assert all(a > b for a, b in zip(x, x[1:]))
    assert all(a > b for a, b in zip(y, y[1:]))
    assert not (set(x) & set(y))
    assert all(a > b for a, b in zip(x, y))
    assert all(x[i + 1] > y[i] for i in range(len(x) - 1))


def negative_count(q):
    x, y = q
    return sum(a < b for a in x for b in y)


def minimum_rows(q):
    x, y = q
    rho = [sum(a < b for b in y) for a in reversed(x)]
    return 1 + max((part + i for i, part in enumerate(rho, 1) if part), default=0)


def register(p, q, seen):
    key = tuple(sorted(p.items()))
    previous = seen.setdefault(key, orbit(q))
    assert previous == orbit(q), ("nonrotation polynomial collision", previous, q)


def triple(q, ell, m, g1, g2, u, v, middle):
    c, d = q
    s, left, right = c[0], ell + g1, m + g2
    n = s + left + right + u + v
    if middle:
        x = (n, n - u) + tuple(v + right + a for a in c) + (v + m,)
        y = (n - u - ell,) + tuple(v + right + b for b in d) + (v, 0)
    else:
        x = (n, n - u, s + right + v) + tuple(v + a for a in c)
        y = (n - u - ell, s + right + v - m) + tuple(v + b for b in d) + (0,)
    result = (x, y)
    validate(result)
    assert negative_count(result) == 9 and minimum_rows(result) == 7
    return result


def two_components(q, r, u, v, gap):
    c, d = q
    e, f = r
    z = v + e[0] + gap
    result = ((z + c[0] + u,) + tuple(z + a for a in c) + tuple(v + a for a in e),
              tuple(z + b for b in d) + tuple(v + b for b in f) + (0,))
    validate(result)
    assert negative_count(result) <= 9 and minimum_rows(result) == 7
    return result


def dense_four_cores():
    # Exactly all strict dense four-row lists of normalized span 7, 8, or 9.
    for span in range(7, 10):
        for rest in combinations(range(1, span), 6):
            ordered = tuple(reversed(rest))
            yield (span,) + ordered[:3], ordered[3:] + (0,)


def check_branching_identity():
    # x=1 leaves an exact univariate polynomial identity, including a=b=0.
    def complete(n):
        return {tuple([1] * k): 1 for k in range(n + 1)}
    for a, b, t in product(range(5), range(5), range(1, 5)):
        lhs = add(mul(complete(a + t), complete(a + b + 1)),
                  scale(mul(complete(a), complete(a + t + b + 1)), -1))
        rhs = mul({tuple([1] * (a + 1)): 1}, complete(t - 1), complete(b))
        assert lhs == rhs, (a, b, t)


def check_dense_remainders_and_last_ties():
    cores = list(dense_four_cores())
    nonsymmetric = tied_parents = 0
    for q in cores:
        if q == rotation(q):
            assert not delta(q, 1) and not delta(q, 2)
            continue
        nonsymmetric += 1
        c, d = q
        kappa = max(c[1], c[0] - d[-2])
        cq = coefficient(delta(q, 1), kappa + 1)
        assert cq and largest(cq) <= kappa
        for t in (1, 2, 3):
            diff = delta(q, t)
            assert largest(diff) == kappa + t
            assert coefficient(diff, kappa + t) == cq
            assert add(diff, scale(mul(h(kappa + t), cq), -1))
        for ell in (1, 2):
            # Equal singletons, unequal interior gaps, and the last top tie.
            left, right = ell + 2, ell + 1
            u, v = kappa + 1, kappa + 2
            p = kappa + left
            tm = add(mul(h(ell), h(ell + u), delta(q, left)),
                     scale(mul(h(ell), h(ell + v), delta(q, right)), -1))
            expected = mul(h(ell), add(mul(h(kappa + right), cq), scale(delta(q, right), -1)))
            assert expected
            assert coefficient(tm, p) == expected
            source = triple(q, ell, ell, 2, 1, u, v, True)
            mate = triple(rotation(q), ell, ell, 2, 1, u, v, True)
            assert orbit(source) != orbit(mate)
            difference = add(jt(*source), scale(jt(*mate), -1))
            assert difference
            assert coefficient(difference, c[0] + left + u) == tm
            tied_parents += 1
    print(f"PASS: dense endpoint window {len(cores)} cores, {nonsymmetric} nonsymmetric; {tied_parents} last-tie orientation attacks")


def check_triple_assembly_collisions():
    representatives = sorted({orbit(q) for q in dense_four_cores()})
    total = 0
    for q in representatives:
        seen = {}
        literal = set()
        for core in {q, rotation(q)}:
            for ell, m, g1, g2, u, v in product((1, 2), repeat=6):
                for middle in (False, True):
                    board = triple(core, ell, m, g1, g2, u, v, middle)
                    if board in literal:
                        continue
                    literal.add(board)
                    register(jt(*board), board, seen)
                    total += 1
        jt.cache_clear()
    print(f"PASS: {total} end/middle parents across {len(representatives)} dense-core rotation orbits; no nonrotation collision")


def check_two_component_collisions():
    q2 = ((5, 3), (1, 0))
    q3 = ((7, 5, 3), (2, 1, 0))
    r3 = ((8, 7, 4), (3, 1, 0))
    q4 = ((9, 7, 6, 4), (3, 2, 1, 0))
    r4 = ((10, 8, 6, 3), (4, 2, 1, 0))
    pairs = ((q3, q3), (r3, r3), (q3, r3), (q2, q4), (q2, r4))
    total = 0
    for first, second in pairs:
        seen = {}
        literal = set()
        for q0, r0 in {(first, second), (second, first)}:
            for q, r in product({q0, rotation(q0)}, {r0, rotation(r0)}):
                parameters = set(product(range(1, 4), repeat=3))
                kappa = max(r[0][1], r[0][0] - r[1][-2])
                for gap in (1, 2):
                    for u in (1, kappa + gap, kappa + gap + 1):
                        parameters.add((u, gap + q[0][0] + u, gap))
                for u, v, gap in sorted(parameters):
                    board = two_components(q, r, u, v, gap)
                    if board in literal:
                        continue
                    literal.add(board)
                    register(jt(*board), board, seen)
                    total += 1
        jt.cache_clear()
    print(f"PASS: {total} two-component parents; equal factors, equal orders, swapped orders, one-negative cores, and all three top-tie regimes")


def must_reject(name, action):
    try:
        action()
    except AssertionError:
        print("REJECTING CONTROL PASS:", name)
    else:
        raise AssertionError("control failed to reject: " + name)


def rejecting_controls():
    a = ((5, 3), (1, 0))
    b = ((6, 3), (1, 0))
    assert orbit(a) != orbit(b)
    artificial_collision = {}
    register(jt(*a), a, artificial_collision)
    must_reject("injected nonrotation equality", lambda: register(jt(*a), b, artificial_collision))
    actual = jt(*a)
    wrong = add(mul(h(4), h(3)), mul(h(5), h(2)))
    def check_bad_sign():
        assert actual == wrong, "wrong determinant sign"
    must_reject("wrong determinant sign", check_bad_sign)


def main():
    assert jt((), ()) == {(): 1}
    assert jt((0,), (0,)) == {(): 1}
    assert jt((0,), (1,)) == {}
    assert jt((5, 3), (1, 0)) == add(mul(h(4), h(3)), scale(mul(h(5), h(2)), -1))
    rejecting_controls()
    check_branching_identity()
    check_dense_remainders_and_last_ties()
    check_triple_assembly_collisions()
    check_two_component_collisions()
    print("ALL PASS: bounded exact threshold attacks; no claim of uniform computational proof")


if __name__ == "__main__":
    main()
