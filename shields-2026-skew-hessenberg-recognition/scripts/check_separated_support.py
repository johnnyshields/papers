"""Check reconstruction from disjoint nonempty block gap supports.

The word checks start with an aligned literal merger.  Complete row/gap fibers
also test an explicit source and its merger against arbitrary arrangements.
A nonrigid-block probe tests reconstruction, not rigidity of its merger.
"""
from itertools import permutations, product
from random import Random

from check_zero_cut_inventory import (
    betas, blocks, evaluate, join, near, permutation_polynomial, polynomial,
    rotate, total_merge, valid, zero_free,
)


def marked_word(profile):
    rows, gaps = profile
    answer = []
    for i, length in enumerate(rows):
        answer.extend([0] * (length - 1))
        answer.append(gaps[i] + 1 if i < len(gaps) else 0)
    assert len(answer) == sum(rows)
    return tuple(answer)


def combine(pieces, operation):
    answer = pieces[0]
    for piece in pieces[1:]:
        answer = operation(answer, piece)
    return answer


def check_hypotheses(source):
    pieces = blocks(source)
    assert len(pieces) >= 2 and all(len(b[0]) >= 2 and zero_free(b) for b in pieces)
    supports = [set(b[1]) for b in pieces]
    assert all(supports)
    assert all(a.isdisjoint(b) for i, a in enumerate(supports) for b in supports[i + 1:])
    return pieces


def rigidity_fiber(source):
    source_poly = polynomial(source)
    assert permutation_polynomial(source) == source_poly
    modulus = 65521
    rng = Random(48127)
    span = betas(source)[0][0]
    values = [(1,) + tuple(rng.randrange(1, modulus) for _ in range(span)) for _ in range(3)]
    source_values = tuple(evaluate(source, alphabet, modulus) for alphabet in values)
    count, survivors = 0, set()
    for rows in sorted(set(permutations(source[0]))):
        for gaps in sorted(set(permutations(source[1]))):
            candidate = rows, gaps
            if not valid(candidate):
                continue
            count += 1
            if tuple(evaluate(candidate, alphabet, modulus) for alphabet in values) != source_values:
                continue
            if polynomial(candidate) == source_poly:
                survivors.add(candidate)
    assert survivors == {source, rotate(source)}
    print(f'PASS: complete row/gap fiber at {sum(source[0])} cells: '
          f'{count} profiles, exactly the rotation orbit.')


def main():
    arrangements = 0
    for count in range(2, 6):
        letters = [((2 * i + 3, 2 * i + 1, 2 * i + 2), (2 * i, 2 * i))
                   for i in range(1, count + 1)]
        source = combine(letters, join)
        check_hypotheses(source)
        merger = combine(letters, near)
        assert marked_word(merger) == sum((marked_word(b) for b in letters), ())
        for order in permutations(range(count)):
            for signs in product((False, True), repeat=count):
                pieces = [rotate(letters[i]) if sign else letters[i] for i, sign in zip(order, signs)]
                candidate, contraction = combine(pieces, join), combine(pieces, near)
                if contraction == merger:
                    assert candidate == source
                if contraction == rotate(merger):
                    assert candidate == rotate(source)
                arrangements += 1

    first = ((2, 4, 4, 5), (1, 1, 2))
    partner = ((2, 4, 5, 4), (1, 2, 1))
    second = ((7, 8), (4,))
    assert polynomial(first) == polynomial(partner)
    assert partner not in (first, rotate(first))
    source, merger = join(first, second), near(first, second)
    check_hypotheses(source)
    for a in (first, partner, rotate(first), rotate(partner)):
        for b in (second, rotate(second)):
            for pieces in ((a, b), (b, a)):
                if near(*pieces) == merger:
                    assert join(*pieces) == source
                if near(*pieces) == rotate(merger):
                    assert join(*pieces) == rotate(source)
                arrangements += 1
    print(f'PASS: {arrangements} disjoint-support arrangements, including a nonrigid block.')

    pieces = [((13, 10, 5), (4, 4)), ((5, 7), (2,)), ((13, 14, 14), (6, 6))]
    source, merger = combine(pieces, join), combine(pieces, near)
    assert check_hypotheses(source) == tuple(pieces)
    assert len(source[0]) == 8
    assert all(source[0][i] > source[1][i - 1] + source[1][i] for i in range(1, 7))
    assert merger == ((13, 10, 10, 20, 14, 14), (4, 4, 2, 6, 6))
    assert merger[0].count(13) == 1 and 13 > 2 * max(merger[1])
    assert all(v % 2 == 0 for v in merger[0][1:] + merger[1])
    assert source[0].count(source[0][0]) > 1 and source[0].count(source[0][-1]) > 1
    print('PASS: the eight-row example has disjoint supports and a private merger endpoint; neither source endpoint is private.')

    small = ((9, 6, 5, 5, 6, 6), (4, 4, 0, 2, 2))
    check_hypotheses(small)
    rigidity_fiber(small)
    rigidity_fiber(total_merge(small))

    inner = ((2, 3), (1,))
    squared = near(inner, inner)
    f, h = join(inner, squared), join(squared, inner)
    assert all(zero_free(b) and len(b[0]) >= 2 for b in (inner, squared))
    assert set(inner[1]) & set(squared[1])
    assert near(inner, squared) == near(squared, inner)
    assert polynomial(f) == polynomial(h) and h not in (f, rotate(f))
    print('CONTROL: a shared gap support admits a nonrotation commuting-power equality.')

    f = ((1, 2, 2, 3), (0, 0, 1))
    h = ((1, 2, 3, 2), (0, 1, 0))
    assert polynomial(f) == polynomial(h) == permutation_polynomial(f)
    assert h not in (f, rotate(f))
    assert total_merge(h) == rotate(total_merge(f))
    assert any(len(b[0]) == 1 for b in blocks(f))
    print('CONTROL: one-row blocks admit the eight-cell nonrotation equality, despite a rotation-rigid merger.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
