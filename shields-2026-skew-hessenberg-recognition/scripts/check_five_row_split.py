"""Reconstruct the five-row pattern escapes and test their genuine extra mates."""
from itertools import permutations, product
from verify_hessenberg import interval


def legal(rows, c):
    return (rows[0] > c and rows[-1] > c
            and all(r > 2*c for r in rows[1:-1]))


def cg_plus(rows, c):
    a, b = rows[0], rows[-1]
    interior = rows[1:-1]
    return (a+b-c not in interior
            or (b, a) not in tuple(zip(interior, interior[1:])))


def extra_mates(rows, c):
    gaps = (c,)*(len(rows)-1)
    reference = interval(rows, gaps)
    return {order for order in set(permutations(rows))
            if legal(order, c) and interval(order, gaps) == reference} - {rows, rows[::-1]}


def main():
    escapes = [(rows, c) for c in range(1, 4)
               for rows in product(range(1, 15), repeat=5)
               if legal(rows, c) and not cg_plus(rows, c)]
    assert len(escapes) == 186
    balanced = [(r, c) for r, c in escapes if r[0] == r[-1]]
    unequal = [(r, c) for r, c in escapes if r[0] != r[-1]]
    assert (len(balanced), len(unequal)) == (22, 164)
    for rows, c in balanced:
        a = rows[0]
        assert a > 2*c
        assert rows in ((a, a, a, 2*a-c, a), (a, 2*a-c, a, a, a))
    for rows, c in unequal:
        assert extra_mates(rows, c), (rows, c)
    control = (3, 3, 4, 6, 4)
    assert cg_plus(control, 1) and not extra_mates(control, 1)
    assert ((3, 3, 3, 5, 3), 1) in balanced
    print('PASS: 186 escapes split into 22 balanced forms and 164 unequal-end forms.')
    print('PASS: every unequal-end escape has an exact nonrotation mate at power one.')
    print('PASS: the recognized control has no extra mate.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
