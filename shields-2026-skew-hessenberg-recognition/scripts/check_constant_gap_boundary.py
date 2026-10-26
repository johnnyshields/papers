"""Check the constant-gap pattern criterion and the boundary of its coverage.

An endpoint must exceed its one incident gap; an internal row must exceed
its two incident gaps.  Both conditions belong to profile legality.
"""
from itertools import product


def legal(rows, c):
    return (rows[0] > c and rows[-1] > c
            and all(r > 2*c for r in rows[1:-1]))


def cg_plus(rows, c):
    a, b = rows[0], rows[-1]
    internal = rows[1:-1]
    sum_absent = a+b-c not in internal
    pair_absent = (b, a) not in tuple(zip(internal, internal[1:]))
    return sum_absent or pair_absent


def main():
    maxrow = 14
    failures = {}
    expected = {2: 434, 3: 4436, 4: 46480, 5: 497984}
    assert not legal((1, 5, 5), 2)
    assert not legal((5, 5, 2), 2)
    assert not legal((5, 4, 5), 2)
    assert legal((3, 5, 3), 2)
    for n in range(2, 7):
        count = 0
        failures[n] = []
        for c in range(1, 4):
            ranges = [range(c+1, maxrow+1)]
            ranges += [range(2*c+1, maxrow+1)]*(n-2)
            ranges += [range(c+1, maxrow+1)]
            for rows in product(*ranges):
                assert legal(rows, c)
                count += 1
                if not cg_plus(rows, c):
                    failures[n].append((rows, c))
        formula = sum((maxrow-c)**2*(maxrow-2*c)**(n-2)
                      for c in range(1, 4))
        assert count == formula
        if n in expected:
            assert count == expected[n]
        if n <= 4:
            assert not failures[n]
        print(f'PASS: n={n}, legal profiles={count}, pattern escapes={len(failures[n])}')
    assert len(failures[5]) == 186
    assert len(failures[6]) == 5819
    assert min(failures[5], key=lambda t: (sum(t[0]), t[0])) == ((3, 3, 3, 5, 3), 1)
    assert cg_plus((3, 3, 4, 6, 4), 1)
    print('PASS: endpoint and internal-legality negative controls fire.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
