#!/usr/bin/env python3
"""Cyclic gap sums, the maximal bin, and mask periodicity.

Paper sections `sec:dual` (Cyclic inventories and original coefficients) and
`sec:one-active` (From response functions to literal copies); targets
`lem:maximal-bin` (its averaging and periodicity statements), `lem:peeling`
(its counting step) and `lem:positive-support`/`cor:many-active` (the
periodicity used on equality).

Gaps are positive integer cycles of length B = r b whose total is q = b delta.
Asserted for every such cycle in the range: the cyclic n-window sums (n = r d)
have mean d delta; their maximum is at least the mean, with equality exactly when
every n-window sum is the mean, and then the cycle has period gcd(n, B) = r.  For
0/1 occurrence masks on a cycle of length B the same sliding argument is
checked on the completed word of length B = k n + m with n = r d, m = r s:
constant m-window counts force chi(i + m) = chi(i) and hence period gcd(m, B) = r.
The coprimality gcd(b, d) = 1 of the paper's domain is required and enumerated.  Controls: a cycle of mean
window sum with unequal windows exists and is not periodic.
"""
from collections import Counter
from itertools import product
from math import gcd


def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(1, total-parts+2):
        for rest in compositions(total-first, parts-1):
            yield (first,)+rest


def window_sums(cycle, n):
    B = len(cycle)
    return [sum(cycle[(i+a) % B] for a in range(n)) for i in range(B)]


def smallest_period(cycle):
    B = len(cycle)
    return next(p for p in range(1, B+1) if B % p == 0 and all(cycle[i] == cycle[(i+p) % B] for i in range(B)))


def main():
    counts = Counter()
    for b in range(3, 8):
        for d in range(1, b):
            if gcd(b, d) != 1:
                continue
            for r in (1, 2):
                n, B = r*d, r*b
                if B > 8:
                    continue
                for delta in (1, 2, 3):
                    q = b*delta
                    if q < B:
                        continue
                    for cycle in compositions(q, B):
                        sums = window_sums(cycle, n)
                        assert sum(sums)*1 == n*q            # each gap counted n times
                        assert n*q == B*d*delta               # mean is exactly d delta
                        M = max(sums)
                        assert M >= d*delta
                        counts['cycles'] += 1
                        if M == d*delta:
                            assert len(set(sums)) == 1
                            period = smallest_period(cycle)
                            assert gcd(n, B) == r
                            # equal n-window sums: cycle[i+n] = cycle[i], so period divides gcd(n, B)
                            assert all(cycle[i] == cycle[(i+n) % B] for i in range(B))
                            assert gcd(n, B) % period == 0
                            counts['equal windows, periodic with period dividing r'] += 1
                            counts['equal windows, minimal period < r'] += period < r
                        else:
                            assert M > d*delta
                            counts['strict maximum'] += 1
                        if M > d*delta and len(set(sums)) > 1 and smallest_period(cycle) == B:
                            counts['control: nonperiodic cycle has unequal windows'] += 1
    # counting step of lem:peeling: on the word l = P^k R of length B-1, constant m-window
    # counts of a 0/1 occurrence mask force chi(i+m) = chi(i), hence period gcd(m, n) = r on P
    for b in range(3, 10):
        for d in range(2, b):
            if gcd(b, d) != 1:
                continue
            for r in (1, 2):
                k, s = divmod(b, d)
                if s == 0:
                    k, s = k-1, d
                n, m = r*d, r*s
                if n > 12:
                    continue
                assert gcd(m, n) == r
                for P in product((0, 1), repeat=n):
                    word = P*k+P[:m-1]
                    assert len(word) == r*b-1
                    window_counts = {sum(word[i:i+m]) for i in range(len(word)-m+1)}
                    counts['masks'] += 1
                    if len(window_counts) == 1:
                        counts['masks with constant m-window count'] += 1
                        assert all(P[(i+m) % n] == P[i] for i in range(n))
                        assert all(P[(i+r) % n] == P[i] for i in range(n))
                        counts['... hence period r'] += 1
                    elif not all(P[(i+r) % n] == P[i] for i in range(n)):
                        counts['control: aperiodic masks have nonconstant window counts'] += 1
    for key in ('cycles', 'equal windows, periodic with period dividing r', 'strict maximum',
                'masks with constant m-window count', 'control: nonperiodic cycle has unequal windows'):
        assert counts[key], key
    print(dict(counts))
    print('check_gap_cycles: PASS')


if __name__ == '__main__':
    main()
