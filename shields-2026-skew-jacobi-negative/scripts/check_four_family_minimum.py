#!/usr/bin/env python3
"""The four-row exceptional family at its smallest admissible parameters.

The three-negative exceptions have profiles F=(w,b,b,b+w-c; c,c,w) and
H=(w,b,b+w-c,b; c,w,c) with 0<=c<w and b>c+w.  The admissible point of least
area is (c,w,b)=(0,1,2), where the two members are the eight-cell diagrams
(4,4,3,3)/(3,2,1,0) and (4,4,4,2)/(3,2,1,0).

Checked here: the family identity, the three negatives, the four distinct
members, and that no admissible parameter point has smaller area.  The area
minimum is over the stated inequalities, which is a closed arithmetic
question; the sweep box only exhibits it.  This corroborates the identity and
the minimum; the classification itself is proved in the paper.
"""
from jacobi_trudi import *


def family(c, w, b):
    F = from_profile((w, b, b, b + w - c), (c, c, w))
    H = from_profile((w, b, b + w - c, b), (c, w, c))
    return F, H


def area(c, w, b):
    return 2 * w + 3 * b - c


def main():
    admissible = [(c, w, b)
                  for w in range(1, 5) for c in range(0, w)
                  for b in range(c + w + 1, 9)]
    require(admissible)

    for c, w, b in admissible:
        F, H = family(c, w, b)
        require(determinant(*F) == determinant(*H))
        require(len(negatives(*F)) == 3 and len(negatives(*H)) == 3)
        members = {normalize(*F), normalize(*rotation(*F)),
                   normalize(*H), normalize(*rotation(*H))}
        require(len(members) == 4)
        require(sum(profile(*F)[0]) == area(c, w, b))

    least = min(admissible, key=lambda t: area(*t))
    require(least == (0, 1, 2) and area(*least) == 8)
    require(sum(1 for t in admissible if area(*t) == 8) == 1)

    F, H = family(0, 1, 2)
    require(profile(*F) == ((1, 2, 2, 3), (0, 0, 1)))
    require(profile(*H) == ((1, 2, 3, 2), (0, 1, 0)))
    require(normalize(*F) == normalize((7, 6, 4, 3), (6, 4, 2, 0)))
    require(normalize(*H) == normalize((7, 6, 5, 2), (6, 4, 2, 0)))
    require(determinant(*F) == determinant(*H))
    require(normalize(*rotation(*F)) != normalize(*F))

    # Controls.  Outside the stated inequalities the identity must fail, so the
    # sweep above is testing the hypotheses and not an unconditional identity.
    rejects(lambda: require(determinant(*family(1, 1, 4)[0])
                            == determinant(*family(1, 1, 4)[1])))
    rejects(lambda: require(determinant(*family(0, 2, 2)[0])
                            == determinant(*family(0, 2, 2)[1])))

    print('FOUR-FAMILY MINIMUM', {'admissible points': len(admissible),
                                  'least area': area(*least),
                                  'attained at (c,w,b)': least},
          'CONTROLS FIRED: c=w, b=c+w')
    print('ALL PASS')


if __name__ == '__main__':
    main()
