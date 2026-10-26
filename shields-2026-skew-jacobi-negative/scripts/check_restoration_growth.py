#!/usr/bin/env python3
"""The negative count is not stable under common-beta restoration.

The count nu is independent of area, but not of restoration.  Take the
four-row zero-free core

    A = (2a+1, 7, 5, 3),   B = (6, 4, 2, 0),    a >= 5,

which is Gamma(X,Y) for X = (a,3,2,1), Y = (3,2,1,0) under the homogenization
of lem:homogenization.  Restoring common beta entries gives

    no restoration      n = 4    nu = 3
    one restoration     n = 5    negative set is exactly the staircase
    k >= 2              n = 4+k  nu = binom(n-1, 2),  never a staircase

So the two regimes this paper classifies -- small nu, and the six-cell
staircase -- are the first two layers of the restoration cube of a single
three-negative core, and everything above leaves the axis.  Since
binom(n-1,2) is the ribbon hole count, those restorations sit at the maximum
negative count, where no classification organized by nu can reach them.

This delimits the scope of the negative-count parameter.  It states no
theorem about restorations themselves.
"""
from itertools import combinations
from jacobi_trudi import *


def core(a):
    return (2 * a + 1, 7, 5, 3), (6, 4, 2, 0)


def restore(X, Y, sites):
    return (tuple(sorted(X + tuple(sites), reverse=True)),
            tuple(sorted(Y + tuple(sites), reverse=True)))


def staircase(n):
    return frozenset((i, j) for i in range(1, n + 1) for j in range(1, n + 1)
                     if i - j >= n - 3)


def sites(X, Y):
    return [z for z in range(min(Y) + 1, max(X)) if z not in set(X) | set(Y)]


def connected(X, Y):
    rows, gaps = profile(X, Y)
    return (all(r > 0 for r in rows) and
            all(0 <= gaps[i] < min(rows[i], rows[i + 1]) for i in range(len(gaps))))


def main():
    tally = {'core': 0, 'one -> staircase': 0, 'k>=2 -> binom': 0}
    for a in (5, 6, 7):
        X, Y = core(a)
        require(profile(X, Y) == ((2 * a - 5, 3, 3, 3), (1, 1, 1)))
        require(gamma((a, 3, 2, 1), (3, 2, 1, 0)) == (X, Y))
        require(len(negatives(X, Y)) == 3)
        require(connected(X, Y))
        tally['core'] += 1

        omega = sites(X, Y)
        require(len(omega) == 2 * (a - 4) + 2)
        for k in range(1, len(omega) + 1):
            for chosen in combinations(omega, k):
                P, Q = restore(X, Y, chosen)
                require(connected(P, Q))
                n = len(P)
                neg = negatives(P, Q)
                if k == 1:
                    require(neg == staircase(n))
                    require(len(neg) == 6)
                    tally['one -> staircase'] += 1
                else:
                    require(len(neg) == (n - 1) * (n - 2) // 2)
                    require(neg != staircase(n))
                    require(len(neg) >= 10)
                    tally['k>=2 -> binom'] += 1

    # Controls.  The core must not already be a staircase, and a restored board must
    # not keep the core's count, or the growth statement would be vacuous.
    X, Y = core(6)
    rejects(lambda: require(negatives(X, Y) == staircase(4)))
    P, Q = restore(X, Y, (sites(X, Y)[0],))
    rejects(lambda: require(len(negatives(P, Q)) == 3))

    print('RESTORATION GROWTH', tally,
          'CONTROLS FIRED: core as staircase, count preserved by restoration')
    print('ALL PASS')


if __name__ == '__main__':
    main()
