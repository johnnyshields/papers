"""Exact power checks for a balanced pattern escape and a recognized control."""
from itertools import permutations
from verify_hessenberg import interval, composite


def legal_order(rows, gaps):
    return (all(c < min(a, b) for a, b, c in zip(rows, rows[1:], gaps))
            and all(rows[i] > gaps[i-1]+gaps[i] for i in range(1, len(rows)-1)))


def power_mates(rows, gaps, m):
    r, g = composite(rows, gaps, (m,))
    reference = interval(r, g)
    return r, {order for order in set(permutations(r))
               if legal_order(order, g) and interval(order, g) == reference}


def main():
    for rows in ((3, 3, 3, 5, 3), (3, 3, 4, 6, 4)):
        for m in (1, 2):
            r, mates = power_mates(rows, (1,)*4, m)
            assert mates == {r, r[::-1]}, (rows, m, mates)
            print(f'PASS: {rows}, power {m}, exact mates={len(mates)}; rotation orbit only.')
    print('These finite checks corroborate the all-power proof; they do not replace it.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
