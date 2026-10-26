"""Check general zero-free exposure and unequal-terminal inflation classes.

Row/gap invariant fibers are complete in each declared case.  Finite-field
values reject candidates only; all retained equalities use full integer
polynomials.  Permutation determinants independently check the source values.
"""
from collections import Counter
from itertools import permutations
from random import Random

from check_literal_charts import cells_of_profile, source_ribbon_chart
from check_zero_cut_inventory import (
    betas, blocks, evaluate, join, near, permutation_polynomial, polynomial,
    rotate, valid, zero_free,
)
from verify_hessenberg import compositions


def power(inner, copies):
    answer = inner
    for _ in range(copies - 1):
        answer = near(answer, inner)
    return answer


def composite(alpha, inner):
    answer = power(inner, alpha[0])
    for part in alpha[1:]:
        answer = join(answer, power(inner, part))
    return answer


def inflate(profile, time):
    return tuple(r + time for r in profile[0]), tuple(g + time for g in profile[1])


def ribbon_polynomial(alpha):
    answer = Counter()
    for mask in range(1 << (len(alpha) - 1)):
        current, pieces = alpha[0], []
        for i, value in enumerate(alpha[1:]):
            if mask & (1 << i):
                pieces.append(current)
                current = value
            else:
                current += value
        pieces.append(current)
        answer[tuple(sorted(pieces))] += (-1) ** (len(alpha) - len(pieces))
    return tuple(sorted((mon, c) for mon, c in answer.items() if c))


def composition(alpha, gamma):
    return composite(alpha, (gamma, (0,) * (len(gamma) - 1)))[0]


def invariant_fiber(inner, alpha, time):
    source = inflate(composite(alpha, inner), time)
    source_poly = polynomial(source)
    threshold = min(inner[0][0] - inner[1][0], inner[0][-1] - inner[1][-1])
    if time < threshold:
        expected = {inflate(composite(beta, inner), time) for beta in set(permutations(alpha))
                    if ribbon_polynomial(beta) == ribbon_polynomial(alpha)}
        expected |= {rotate(p) for p in tuple(expected)}
    else:
        assert inner[0][0] - inner[1][0] != inner[0][-1] - inner[1][-1]
        expected = {source, rotate(source)}
    modulus = 65521
    rng = Random(33271)
    span = betas(source)[0][0]
    values = [(1,) + tuple(rng.randrange(1, modulus) for _ in range(span)) for _ in range(2)]
    key = tuple(evaluate(source, alphabet, modulus) for alphabet in values)
    common = len(set(betas(source)[0]) & set(betas(source)[1]))
    count = unit_survivors = 0
    actual = set()
    for rows in sorted(set(permutations(source[0]))):
        for gaps in sorted(set(permutations(source[1]))):
            candidate = rows, gaps
            if not valid(candidate):
                continue
            count += 1
            x, y = betas(candidate)
            if len(set(x) & set(y)) != common:
                continue
            unit_survivors += 1
            if tuple(evaluate(candidate, alphabet, modulus) for alphabet in values) != key:
                continue
            if polynomial(candidate) == source_poly:
                actual.add(candidate)
    assert actual == expected
    assert permutation_polynomial(source) == source_poly
    if time == 0:
        assert all(zero_free(block) for mate in actual for block in blocks(mate))
    if time < threshold:
        inner_cells = cells_of_profile(*inflate(inner, time))
        for beta in set(permutations(alpha)):
            target = inflate(composite(beta, inner), time)
            assert source_ribbon_chart(beta, inner_cells, time) == cells_of_profile(*target)
        assert source_ribbon_chart(alpha, inner_cells, time, north_error=1) != cells_of_profile(*source)
        assert len(actual) == 4
        assert actual != {source, rotate(source)}
    else:
        assert len(actual) == 2
    print(f'PASS: inner {inner}, outer {alpha}, time {time}: '
          f'{count} profiles, {unit_survivors} unit-count survivors, {len(actual)} exact mates.')


def main():
    alpha = (1, 2, 1, 3, 2)
    ribbon_class = {beta for beta in compositions(9)
                    if ribbon_polynomial(beta) == ribbon_polynomial(alpha)}
    assert ribbon_class == {(1, 2, 1, 3, 2), (1, 3, 2, 1, 2),
                            (2, 1, 2, 3, 1), (2, 3, 1, 2, 1)}
    assert len(ribbon_class) > len({alpha, alpha[::-1]})
    for beta in ribbon_class:
        assert polynomial((beta, (0,) * (len(beta) - 1))) == ribbon_polynomial(alpha)
    print('CONTROL: the nonrotation four-member ribbon class is retained.')

    invariant_fiber(((2, 3), (1,)), (1, 2), 0)
    for time in range(4):
        invariant_fiber(((9, 6, 6), (4, 4)), (1, 2), time)

    for gap in (4, 6, 8, 10):
        inner = ((2 * gap + 1, gap + 2, gap + 2), (gap, gap))
        x, y = betas(inner)
        assert x == (2 * gap + 5, gap + 4, gap + 2) and y == (4, 2, 0)
        assert zero_free(inner) and x[2] - y[0] == gap - 2 > 0
        assert inner[0].count(inner[0][0]) == 1 and inner[0][0] > 2 * max(inner[1])
        assert inner[0][0] % 2 and all(v % 2 == 0 for v in inner[0][1:] + inner[1])
        for copies in range(1, 6):
            assert zero_free(power(inner, copies))

    base = ((9, 6, 6), (4, 4))
    gamma = (1, 1)
    assert {beta for beta in compositions(2) if ribbon_polynomial(beta) == ribbon_polynomial(gamma)} == {gamma}
    recoded = composite(gamma, base)
    assert 0 in recoded[1]
    recodings = 0
    for size in range(1, 5):
        for outer in compositions(size):
            for time in range(4):
                assert inflate(composite(outer, recoded), time) == inflate(composite(composition(outer, gamma), base), time)
                recodings += 1
    bad = composite((1, 2), base)
    partner = composite((2, 1), base)
    assert polynomial(bad) == polynomial(partner)
    assert partner not in (bad, rotate(bad))
    print(f'PASS: zero-free non-Hessenberg family hypotheses and {recodings} mixed-zero recoding identities.')
    print('CONTROLS: rotation-only recovery fails below the wall; a wrong chart displacement is rejected; dropping the recoding restriction gives an extra first-power mate.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
