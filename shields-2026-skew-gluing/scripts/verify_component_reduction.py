#!/usr/bin/env python3
"""Finite checks of score descent and the rotation-corrected graph reduction.

The integer sweep tests the modular inequalities, not existence of geometric
roots.  The graph sweep is abstract: it tests the implications from clique
components and rotation covariance, not a census of skew diagrams.
"""
from itertools import combinations
from math import gcd


def score(N, p):
    return N % p, p + N % p


def components(vertices, edges):
    unseen = set(vertices)
    result = []
    while unseen:
        start = unseen.pop()
        component, todo = {start}, [start]
        while todo:
            x = todo.pop()
            neighbors = {next(iter(edge - {x})) for edge in edges if x in edge}
            new = neighbors & unseen
            unseen -= new
            component |= new
            todo.extend(new)
        result.append(component)
    return result


def cluster(vertices, edges):
    return all(frozenset(pair) in edges
               for C in components(vertices, edges) for pair in combinations(C, 2))


def rotation_covariant(edges):
    for edge in edges:
        x, y = tuple(edge)
        for a, b in ((x, y), (x ^ 1, y), (x, y ^ 1), (x ^ 1, y ^ 1)):
            if a != b and frozenset((a, b)) not in edges:
                return False
    return True


def check_scores():
    divisors = folds = 0
    for N in range(4, 121):
        for p, q in combinations(range(2, N // 2 + 1), 2):
            if q % p == 0:
                assert N % p == (N % q) % p
                assert score(N, p) < score(N, q)
                divisors += 1
            elif gcd(p, q) > 1:
                g = gcd(p, q)
                assert score(N, g) < min(score(N, p), score(N, q))
                folds += 1
    # Raw period order is not lexicographic score order.
    assert score(10, 3) > score(10, 5)
    assert divisors and folds
    print(f'score descent: {divisors} divisor comparisons, {folds} nondividing-gcd comparisons')


def check_graphs():
    vertices = range(6)
    pairs = tuple(frozenset(pair) for pair in combinations(vertices, 2))
    rotations = {frozenset((i, i ^ 1)) for i in vertices}
    accepted = 0
    for mask in range(1 << len(pairs)):
        edges = {e for i, e in enumerate(pairs) if mask & (1 << i)}
        if not cluster(vertices, edges) or not rotation_covariant(edges):
            continue
        accepted += 1
        rooted = set().union(*edges) if edges else set()
        augmented = edges | rotations
        assert all(not (edge & rooted) for edge in rotations - edges)
        assert cluster(vertices, augmented)
        quotient = {frozenset(x // 2 for x in edge) for edge in augmented}
        quotient = {edge for edge in quotient if len(edge) == 2}
        assert cluster(range(3), quotient)
        quotient_connected = len(components(range(3), quotient)) == 1
        # A: every chartless vertex has no nonrotation mate in the class.
        A = all(set(vertices) <= {x, x ^ 1} for x in set(vertices) - rooted)
        # R: all rooted vertices have the same component key.
        keys = {x: k for k, C in enumerate(components(vertices, edges)) for x in C}
        R = len({keys[x] for x in rooted}) <= 1
        assert quotient_connected == (A and R)
    bad = {frozenset((0, 2))}
    assert cluster(vertices, bad) and not rotation_covariant(bad)
    assert not cluster(vertices, bad | rotations), 'covariance control did not fire'
    print(f'rotation reduction: all {accepted} covariant six-vertex cluster graphs pass')

    # This is an abstract graph, not a claimed skew Schur class.
    vertices8 = range(8)
    edges8 = {frozenset(pair) for block in (range(4), range(4, 8))
              for pair in combinations(block, 2)}
    assert cluster(vertices8, edges8) and rotation_covariant(edges8)
    assert all(any(x in e for e in edges8) for x in vertices8)
    assert len(components(vertices8, edges8)) == 2
    print('abstract K4 + K4: no isolated vertices, two rooted components; connectivity does not follow')


def main():
    check_scores()
    check_graphs()
    print('ALL PASS')


if __name__ == '__main__':
    main()
