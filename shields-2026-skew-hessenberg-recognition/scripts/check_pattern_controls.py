"""Check that exact ribbon equality detects classes larger than reversal orbits."""
from collections import defaultdict
from verify_hessenberg import compositions, interval


def hypothesis(delta):
    return delta[0]+delta[-1] not in delta[1:-1]


def main():
    large = []
    eligible = 0
    for size in range(1, 13):
        groups = defaultdict(set)
        for delta in compositions(size):
            signature = tuple(sorted(interval(delta, (0,)*(len(delta)-1)).items()))
            groups[signature].add(delta)
        for members in groups.values():
            for delta in members:
                eligible += hypothesis(delta)
                if not members <= {delta, delta[::-1]}:
                    large.append((size, delta, members))
                    assert not hypothesis(delta), delta
    assert eligible == 2720
    assert len(large) == 20
    smallest = min(large, key=lambda t: (t[0], t[1]))
    classical = {(1, 2, 1, 3, 2), (1, 3, 2, 1, 2),
                 (2, 1, 2, 3, 1), (2, 3, 1, 2, 1)}
    assert smallest[0] == 9 and smallest[2] == classical
    print(f'PASS: {eligible} sum-exclusion compositions; {len(large)} larger-class memberships.')
    print('PASS: every larger-class membership violates the sum exclusion.')
    print('PASS: the smallest larger class is the classical four-member class:', sorted(classical))
    print('ALL PASS')


if __name__ == '__main__':
    main()
