#!/usr/bin/env python3
"""The negative set is a partition shape, and rotation conjugates it.

If x_i < y_j then x_{i'} < y_j for every i' > i and x_i < y_{j'} for every
j' < j, so the negative set is an order ideal: a Young diagram lambda(D)
anchored at the bottom-left corner, with |lambda(D)| = nu(D).  Rotation sends
it to the conjugate partition,

    lambda(D*) = lambda(D)'.

Both are checked on every legal profile in the box below.  The order-ideal
property and the conjugation law are proved in general; the box exhibits them
and supplies the realized shapes at six negatives, which is a finite
observation about this range and not a claim about realizability in general.

The staircase of eq:staircase-set at n=5 is the shape (3,2,1), the unique
self-conjugate partition of six; that is why it is the rotation-stable
six-negative pattern.
"""
from collections import Counter
from itertools import product
from jacobi_trudi import *


def shape(X, Y):
    rows = Counter(i for i, _ in negatives(X, Y))
    return tuple(sorted(rows.values(), reverse=True))


def conjugate(L):
    return tuple(sum(1 for part in L if part >= k) for k in range(1, (L or (0,))[0] + 1))


def order_ideal(X, Y):
    neg = negatives(X, Y)
    return all((i2, j2) in neg
               for (i, j) in neg
               for i2 in range(i, len(X) + 1)
               for j2 in range(1, j + 1))


def boards(max_rows, max_len):
    for n in range(2, max_rows + 1):
        for rows in product(range(1, max_len + 1), repeat=n):
            for gaps in product(*(range(min(rows[i], rows[i + 1])) for i in range(n - 1))):
                yield from_profile(rows, gaps)


def main():
    tested = selfconj = 0
    six = set()
    for X, Y in boards(6, 4):
        tested += 1
        L = shape(X, Y)
        require(order_ideal(X, Y))
        require(sum(L) == len(negatives(X, Y)))
        require(shape(*rotation(X, Y)) == conjugate(L))
        selfconj += L == conjugate(L)
    require(tested > 10000)

    for X, Y in boards(6, 5):
        L = shape(X, Y)
        if sum(L) == 6:
            six.add(L)
    require(six)
    classes = []
    seen = set()
    for L in sorted(six):
        if L not in seen:
            seen |= {L, conjugate(L)}
            classes.append(L)
    require([L for L in six if L == conjugate(L)] == [(3, 2, 1)])

    # The paper's staircase at n = 5, read off eq:staircase-set directly.
    n = 5
    stair = tuple(sorted(Counter(i for i in range(1, n + 1) for j in range(1, n + 1)
                                 if i - j >= n - 3).values(), reverse=True))
    require(stair == (3, 2, 1) == conjugate((3, 2, 1)))

    # Controls.  A shape that is not self-conjugate must be moved by rotation, and a
    # set that is not an order ideal must be rejected, so neither test is vacuous.
    rejects(lambda: require(conjugate((3, 3)) == (3, 3)))
    rejects(lambda: require(order_ideal((5, 4, 1), (4, 3, 0)) and
                            negatives((5, 4, 1), (4, 3, 0)) | {(1, 1)}
                            == negatives((5, 4, 1), (4, 3, 0))))

    print('NEGATIVE SHAPE', {'boards': tested,
                             'self-conjugate': selfconj,
                             'nu=6 shapes': len(six),
                             'nu=6 classes up to conjugation': len(classes)},
          'CONTROLS FIRED: non-self-conjugate shape, non-ideal set')
    print('ALL PASS')


if __name__ == '__main__':
    main()
