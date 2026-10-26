#!/usr/bin/env python3
"""Check zero-free-block exposure and separated-gap-support reconstruction.

All positive polynomial claims use complete integer polynomials.  Finite-field
values only reject candidates in complete row/gap invariant fibers.  Controls
retain the nonrotation ribbon class, the Hessenberg power example, and the
failure of rotation rigidity without nonempty disjoint gap supports.
"""
from itertools import permutations, product
from random import Random
import sys

sys.dont_write_bytecode = True
from check_r168_h_inventory import (
    betas, blocks, evaluate, join, near, polynomial, positive_compositions,
    rotate, sympy_polynomial, total_merge, valid, zero_free,
)


def power(e, m):
    p = e
    for _ in range(m - 1):
        p = near(p, e)
    return p


def composite(alpha, e):
    p = power(e, alpha[0])
    for a in alpha[1:]:
        p = join(p, power(e, a))
    return p


def cellset(p):
    r, g = p
    left = [0] * len(r)
    for i in reversed(range(len(g))):
        left[i] = left[i + 1] + r[i + 1] - g[i] - 1
    return frozenset((i, j) for i in range(len(r)) for j in range(left[i], left[i] + r[i]))


def normalize(c):
    a, b = min(i for i, _ in c), min(j for _, j in c)
    return frozenset((i - a, j - b) for i, j in c)


def chart(alpha, e, error=0):
    inner = cellset(e)
    n = len(e[0])
    right = max(j for i, j in inner if i == 0)
    delta = (1 - n, right + 1 + error)
    outer = cellset((alpha, (0,) * (len(alpha) - 1)))
    result = set()
    for i, j in outer:
        dr, dc = (j - i) * delta[0] + i, (j - i) * delta[1] + i
        result.update((a + dr, b + dc) for a, b in inner)
    return normalize(result)


def marked_word(p):
    r, g = p
    # Zero is a blank.  Positive gap labels are encoded as g+1, so gap zero
    # would be a genuine nonblank marker rather than an erased delimiter.
    word = []
    for i, length in enumerate(r):
        word.extend([0] * (length - 1))
        word.append(g[i] + 1 if i < len(g) else 0)
    assert len(word) == sum(r)
    return tuple(word)


def ribbon_poly(alpha):
    from collections import Counter
    answer = Counter()
    for mask in range(1 << (len(alpha) - 1)):
        running, parts = alpha[0], []
        for i, a in enumerate(alpha[1:]):
            if mask & (1 << i):
                parts.append(running)
                running = a
            else:
                running += a
        parts.append(running)
        answer[tuple(sorted(parts))] += (-1) ** (len(alpha) - len(parts))
    return tuple(sorted((m, c) for m, c in answer.items() if c))


def inverse_fiber(e, alpha):
    target = composite(alpha, e)
    target_poly = polynomial(target)
    expected = {composite(beta, e) for beta in set(permutations(alpha))
                if ribbon_poly(beta) == ribbon_poly(alpha)}
    expected |= {rotate(p) for p in tuple(expected)}
    modulus = 65521
    rng = Random(33271)
    span = betas(target)[0][0]
    values = [tuple(rng.randrange(1, modulus) for _ in range(span + 1)) for _ in range(2)]
    key = tuple(evaluate(target, a, modulus) for a in values)
    common = len(set(betas(target)[0]) & set(betas(target)[1]))
    count = unit_survivors = 0
    actual = set()
    for r in sorted(set(permutations(target[0]))):
        for g in sorted(set(permutations(target[1]))):
            p = (r, g)
            if not valid(p):
                continue
            count += 1
            x, y = betas(p)
            if len(set(x) & set(y)) != common:
                continue
            unit_survivors += 1
            if tuple(evaluate(p, a, modulus) for a in values) != key:
                continue
            if polynomial(p) == target_poly:
                actual.add(p)
    assert actual == expected
    assert len(actual) == 4
    assert sympy_polynomial(target) == target_poly
    for p in actual:
        assert all(zero_free(b) for b in blocks(p))
    for beta in set(permutations(alpha)):
        assert chart(beta, e) == cellset(composite(beta, e))
    assert chart(alpha, e, error=1) != cellset(target)
    print('COMPLETE INVARIANT FIBER:', e, alpha, 'area=', sum(target[0]),
          'profiles=', count, 'unit survivors=', unit_survivors, 'mates=', len(actual))


def check_separated_words():
    tested = 0
    for k in range(2, 6):
        letters = [((2 * i + 4, 2 * i + 6), (2 * i,)) for i in range(1, k + 1)]
        source = letters[0]
        merged = letters[0]
        for b in letters[1:]:
            source = join(source, b)
            merged = near(merged, b)
        assert all(zero_free(b) for b in letters)
        assert marked_word(merged) == sum((marked_word(b) for b in letters), ())
        for order in permutations(range(k)):
            for signs in product((False, True), repeat=k):
                choices = [rotate(letters[i]) if s else letters[i] for i, s in zip(order, signs)]
                candidate, contraction = choices[0], choices[0]
                for b in choices[1:]:
                    candidate = join(candidate, b)
                    contraction = near(contraction, b)
                if contraction == merged:
                    assert candidate == source
                if contraction == rotate(merged):
                    assert candidate == rotate(source)
                tested += 1

    # The order/reconstruction argument does not require block rigidity.
    # This first block has a genuine nonrotation mate with the same full
    # polynomial; the disjoint second gap alphabet still fixes its position.
    a = ((2, 4, 4, 5), (1, 1, 2))
    ap = ((2, 4, 5, 4), (1, 2, 1))
    b = ((7, 8), (4,))
    assert polynomial(a) == polynomial(ap) and ap not in (a, rotate(a))
    target, merged = join(a, b), near(a, b)
    for aa in (a, ap, rotate(a), rotate(ap)):
        for bb in (b, rotate(b)):
            for pair in ((aa, bb), (bb, aa)):
                if near(*pair) == merged:
                    assert join(*pair) == target
                if near(*pair) == rotate(merged):
                    assert join(*pair) == rotate(target)
                tested += 1
    print('SEPARATED GAP SUPPORTS: literal ordering and reconstruction in', tested, 'arrangements, including a nonrigid block')

    # Disjointness is needed for this rotation-rigidity conclusion.
    e = ((2, 3), (1,))
    p, q = e, power(e, 2)
    f, h = join(p, q), join(q, p)
    assert all(len(b[0]) >= 2 and zero_free(b) for b in (p, q))
    assert near(p, q) == near(q, p)
    assert polynomial(f) == polynomial(h) and h not in (f, rotate(f))
    assert set(p[1]) & set(q[1])
    print('CONTROL: shared internal gap alphabet permits the nonrotation commuting-power class.')


def check_explicit_families():
    cases = 0
    for k in range(2, 7):
        gap_values = (4, 2) + tuple(range(6, 2 * k + 1, 2))
        assert len(gap_values) == k
        for height in (2, 3, 5):
            first = ((4 * k + 1, 6, 6), (4, 4))
            letters = [first] + [((2 * g + 2,) * height, (g,) * (height - 1)) for g in gap_values[1:]]
            assert all(zero_free(b) for b in letters)
            assert all(set(a[1]).isdisjoint(b[1]) for i, a in enumerate(letters) for b in letters[i + 1:])
            source, merged = letters[0], letters[0]
            for b in letters[1:]:
                source = join(source, b)
                merged = near(merged, b)
            assert not (first[0][1] > sum(first[1]))
            assert zero_free(merged)
            # These are exactly the source clauses of the general private-
            # endpoint recognition theorem, not sampled power-rigidity tests.
            a = merged[0][0]
            assert a > 2 * max(merged[1]) and merged[0].count(a) == 1
            assert a % 2 == 1 and all(x % 2 == 0 for x in merged[0][1:] + merged[1])
            cases += 1
    for g in (4, 6, 8, 10):
        e = ((2 * g + 1, g + 2, g + 2), (g, g))
        assert zero_free(e) and e[0][1] < sum(e[1])
        assert e[0][0] > 2 * max(e[1])
        for m in range(1, 6):
            assert zero_free(power(e, m))
    print('EXPLICIT HETEROGENEOUS FAMILY: recognition and inventory hypotheses in', cases, 'parameter instances; proof is uniform.')

    strengthened = 0
    for k in range(2, 7):
        gap_values = (4, 2) + tuple(range(6, 2 * k + 1, 2))
        for height in (3, 4, 5):
            letters = [((4 * k + 1, 6, 5), (4, 4))]
            for i, g in enumerate(gap_values[1:], start=2):
                last = 2 * g + (2 if i == k else 3)
                letters.append(((2 * g + 1,) + (2 * g + 2,) * (height - 2) + (last,),
                                (g,) * (height - 1)))
            assert all(zero_free(b) for b in letters)
            assert all(set(a[1]).isdisjoint(b[1]) for i, a in enumerate(letters) for b in letters[i + 1:])
            source, merged = letters[0], letters[0]
            for b in letters[1:]:
                source, merged = join(source, b), near(merged, b)
            a = merged[0][0]
            assert a > 2 * max(merged[1]) and merged[0].count(a) == 1
            assert a % 2 == 1 and all(x % 2 == 0 for x in merged[0][1:] + merged[1])
            assert source[0].count(source[0][-1]) > 1
            if k >= 3:
                assert source[0].count(source[0][0]) > 1
            else:
                assert a == 9 and 5 + 6 - 2 == a
                assert 5 in source[0][1:-1] and 6 in source[0][1:-1] and 2 in source[1]
            strengthened += 1
    eight = [((13, 10, 5), (4, 4)), ((5, 7), (2,)), ((13, 14, 14), (6, 6))]
    d, c = eight[0], eight[0]
    for b in eight[1:]:
        d, c = join(d, b), near(c, b)
    assert len(d[0]) == 8 and all(d[0][i] > d[1][i - 1] + d[1][i] for i in range(1, 7))
    assert c == ((13, 10, 10, 20, 14, 14), (4, 4, 2, 6, 6))
    assert c[0][0] > 2 * max(c[1]) and all(x % 2 == 0 for x in c[0][1:] + c[1])
    assert d[0].count(d[0][0]) > 1 and d[0].count(d[0][-1]) > 1
    print('STRONGER APPLICATION CHECK:', strengthened, 'sources fail the direct private-endpoint test while their mergers pass it.')
    print('EIGHT-ROW HESSENBERG EXAMPLE:', d, 'rigid merger=', c)


def main():
    # Minimal boundary control: rigid blocks and a rigid merger do not force
    # empty-only generation when there are one-row blocks.
    f = ((1, 2, 2, 3), (0, 0, 1))
    h = ((1, 2, 3, 2), (0, 1, 0))
    assert polynomial(f) == polynomial(h) == sympy_polynomial(f) == sympy_polynomial(h)
    assert h not in (f, rotate(f))
    assert total_merge(h) == rotate(total_merge(f))
    assert betas(f)[0][0] == 7
    assert all(7 % d for d in range(2, 7))
    assert any(len(b[0]) == 1 for b in blocks(f))
    print('CONTROL: the eight-cell Hessenberg pair has rigid blocks and merger, but prime span seven excludes proper empty-overlap roots.')

    alpha = (1, 2, 1, 3, 2)
    rclass = {b for b in positive_compositions(9) if ribbon_poly(b) == ribbon_poly(alpha)}
    assert rclass == {(1, 2, 1, 3, 2), (1, 3, 2, 1, 2), (2, 1, 2, 3, 1), (2, 3, 1, 2, 1)}
    for beta in rclass:
        assert polynomial((beta, (0,) * (len(beta) - 1))) == ribbon_poly(alpha)
    assert len(rclass) > len({alpha, alpha[::-1]})
    print('RIBBON CONTROL: the full four-member class, not merely rotation, is retained.')

    inverse_fiber(((2, 3), (1,)), (1, 2))
    inverse_fiber(((9, 6, 6), (4, 4)), (1, 2))
    check_separated_words()
    check_explicit_families()
    print('ALL PASS')


if __name__ == '__main__':
    main()
