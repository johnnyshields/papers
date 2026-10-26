#!/usr/bin/env python3
"""Check the Hessenberg-membership lemma and the maximal-cofactor identity.

For a connected profile (rho; q) with normalized beta lists X, Y and
s_D = det(h_{x_i - y_j}), N_D = x_1, the script checks, on every connected
profile in a finite box:

  * (-1)^{n-1} [h_{N_D}] s_D = det(h_{x_{i+1} - y_j})_{i,j=1}^{n-1};
  * the entry of that cofactor at position (i+1, i) has index
    q_i + q_{i+1} - rho_{i+1};
  * the cofactor is nonzero, and it is a monomial exactly when
    rho_i > q_{i-1} + q_i for 2 <= i < n, exactly when every index strictly
    below the first subdiagonal of the full board is negative;
  * in that case the cofactor is prod_i h_{q_i}.

Determinants are expanded over permutations with h_0 = 1 and h_j = 0 for
j < 0; no other module in this directory is imported.  Three firing controls
show the comparisons can fail: a non-strict inequality, a test of the first
internal row only, and the unsigned coefficient.
"""
from collections import defaultdict
from itertools import permutations, product


def betas(rows, gaps):
    n = len(rows)
    x = [0] * n
    y = [0] * n
    x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return x, y


def sign(perm):
    s = 1
    for a in range(len(perm)):
        for b in range(a + 1, len(perm)):
            if perm[a] > perm[b]:
                s = -s
    return s


def det_h(index):
    """Determinant of (h_{index[i][j]}) as {sorted positive indices: coeff}."""
    k = len(index)
    poly = defaultdict(int)
    for perm in permutations(range(k)):
        labels = [index[i][perm[i]] for i in range(k)]
        if any(a < 0 for a in labels):
            continue
        poly[tuple(sorted(a for a in labels if a > 0))] += sign(perm)
    return {m: c for m, c in poly.items() if c}


def connected_profiles(n, top):
    for rows in product(range(1, top + 1), repeat=n):
        ranges = [range(min(rows[i], rows[i + 1])) for i in range(n - 1)]
        for gaps in product(*ranges):
            yield rows, gaps


def main():
    box = {1: 6, 2: 6, 3: 5, 4: 4, 5: 4}
    tested = monomial_cases = 0
    fired = {'non-strict inequality': 0, 'first internal row only': 0,
             'unsigned coefficient': 0}
    for n, top in box.items():
        for rows, gaps in connected_profiles(n, top):
            x, y = betas(rows, gaps)
            assert y[n - 1] == 0 and x[0] == sum(rows) - sum(gaps)
            N = x[0]
            full = det_h([[x[i] - y[j] for j in range(n)] for i in range(n)])
            assert all(m.count(N) <= 1 for m in full)
            lead = defaultdict(int)
            for m, c in full.items():
                if N in m:
                    rest = list(m)
                    rest.remove(N)
                    lead[tuple(rest)] += c
            lead = {m: c for m, c in lead.items() if c}
            signed = {m: (-1) ** (n - 1) * c for m, c in lead.items()}
            cof = det_h([[x[i + 1] - y[j] for j in range(n - 1)]
                         for i in range(n - 1)])
            assert signed == cof, (rows, gaps)
            assert cof, (rows, gaps)
            for i in range(n - 2):
                assert x[i + 2] - y[i] == gaps[i] + gaps[i + 1] - rows[i + 1]

            is_monomial = len(cof) == 1
            condition = all(rows[i] > gaps[i - 1] + gaps[i] for i in range(1, n - 1))
            board = all(x[i] - y[j] < 0
                        for i in range(n) for j in range(n) if i >= j + 2)
            assert is_monomial == condition == board, (rows, gaps)
            if condition:
                monomial_cases += 1
                assert cof == {tuple(sorted(g for g in gaps if g > 0)): 1}

            loose = all(rows[i] >= gaps[i - 1] + gaps[i] for i in range(1, n - 1))
            if loose != is_monomial:
                fired['non-strict inequality'] += 1
            first = n < 3 or rows[1] > gaps[0] + gaps[1]
            if first != is_monomial:
                fired['first internal row only'] += 1
            if lead != cof:
                fired['unsigned coefficient'] += 1
            tested += 1

    print(f'Connected profiles checked: {tested}; monomial maximal cofactors: '
          f'{monomial_cases}; non-monomial: {tested - monomial_cases}')
    for name, count in fired.items():
        print(f'Control ({name}) fails on {count} profiles')
        assert count > 0, name
    print('ALL PASS')


if __name__ == '__main__':
    main()
