#!/usr/bin/env python3
"""Check finite equality graphs and the mixed folded-height identity.

These finite checks corroborate the period arguments; they do not prove their
unbounded statements.  The proper-divisor counterexample is a domain control.
"""
from collections import defaultdict
from itertools import combinations
from math import gcd


def components(length, constraints):
    adjacency = {i: set() for i in range(1, length + 1)}
    for period, holes in constraints:
        groups = defaultdict(list)
        for i in adjacency:
            if i % period not in holes:
                groups[i % period].append(i)
        for group in groups.values():
            for i in group[1:]:
                adjacency[group[0]].add(i)
                adjacency[i].add(group[0])
    labels = {}
    for i in adjacency:
        if i in labels:
            continue
        todo = [i]
        labels[i] = i
        for j in todo:
            for k in adjacency[j]:
                if k not in labels:
                    labels[k] = i
                    todo.append(k)
    return labels


def forces_period(labels, period):
    groups = defaultdict(set)
    for position, component in labels.items():
        groups[position % period].add(component)
    return all(len(group) == 1 for group in groups.values())


def one_hole():
    checks = 0
    for a in range(2, 14):
        for b in range(2, 14):
            if a % b == 0 or b % a == 0:
                continue
            lengths = {2 * max(a, b)}
            if a < b:
                lengths.add(2 * b - 1)
            for length in lengths:
                for hole in range(b):
                    labels = components(length, ((a, set()), (b, {hole})))
                    assert forces_period(labels, gcd(a, b))
                    checks += 1
    word = tuple(map(int, '00010001'))
    assert all(word[i] == word[i + 4] for i in range(4))
    assert len({word[i - 1] for i in range(1, 9) if i % 2}) == 1
    assert word[1] != word[3]
    labels = components(8, ((4, set()), (2, {0})))
    assert not forces_period(labels, 2), "Dividing-period control did not fire"
    print(f"one-hole nondividing systems: {checks}")


def two_holes():
    checks = 0
    for p in range(2, 10):
        for q in range(p + 1, 12):
            for overlap in range(1, q):
                length = 2 * q + overlap - 1
                for holes in combinations(range(overlap + 1), 2):
                    labels = components(length, ((p, set()), (q, set(holes))))
                    assert forces_period(labels, gcd(p, q))
                    checks += 1
    print(f"ordered two-hole systems: {checks}")


def folded_heights():
    checks = changed_endpoint = 0
    for width in range(1, 13):
        for tau in range(width + 1):
            for sigma in range(width + 1):
                if tau == sigma:
                    continue
                alpha, beta = sorted((tau, sigma))
                for residue in range(width):
                    lower = int(tau > 0 and residue >= tau)
                    upper = int(tau > 0) - int(sigma < width and residue >= sigma)
                    expected = (int(tau > 0 and residue >= tau) - int(residue >= sigma)
                                if tau < sigma else 0)
                    assert lower - int(residue >= beta) == upper - int(residue < alpha) == expected
                    changed_endpoint += lower - int(residue >= beta) != upper - int(residue <= alpha)
                    checks += 1
    assert changed_endpoint > 0
    print(f"mixed folded-height identities: {checks}; changed-endpoint rejections: {changed_endpoint}")


def main():
    one_hole()
    two_holes()
    folded_heights()
    print("CONTROLS PASS: excluded proper-divisor case and changed folded endpoint")
    print("ALL PASS")


if __name__ == '__main__':
    main()
