"""`thm:cap-fixed-rigidity`: independent guard for the cap-fixed adjacent-edge rigidity theorem.

Generates every pair (A, B) of connected skew diagrams that meets the hypotheses
of the theorem -- a common inner boundary mu, a common top row (hence a common
cap grid), equal row-length multisets, and a nonzero cofactor defect -- and, on
each pair whose Floor antecedent alpha_0 > m_+ holds, asserts every clause of the
conclusion:

    M_i = {i+1, i+2}                for 0 <= i < v,
    T_0^+ = {d_1, d_2},
    G_j != 0                        for 1 <= j <= v+1,
    alpha_1 = alpha_2 < alpha_3 < ... < alpha_{v+1},
    alpha_j > alpha_{v+1}           for every supported j > v+1,

where v is the first changed row, alpha_j = nu(G_j) + d_j^2 for the square weight
nu(prod h_k) = sum k^2, m_+ = min_{j>0} alpha_j, T_0^+ = argmin_{j>0} alpha_j, and
M_i = argmin_j F_i(j) with F_i(j) = alpha_j + (d_j - A_i)^2 - d_j^2 the valuation
of the j-th summand of the common-row relation sum_j h_{d_j - A_i} G_j = 0.

Pairs failing the antecedent are counted separately; they are not counterexamples,
they are the alpha_0 = m_+ branch, on which the theorem asserts nothing.

Exact integer arithmetic on signed multisets of h-monomials throughout.
"""

import itertools
import sys
from collections import defaultdict

SIZE_CAP = 14
ROW_CAP = 6


def h(k):
    if k < 0:
        return {}
    if k == 0:
        return {(): 1}
    return {(k,): 1}


def padd(f, g):
    out = dict(f)
    for m, c in g.items():
        v = out.get(m, 0) + c
        if v:
            out[m] = v
        else:
            out.pop(m, None)
    return out


def psub(f, g):
    return padd(f, {m: -c for m, c in g.items()})


def pmul(f, g):
    out = defaultdict(int)
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            out[tuple(sorted(m1 + m2))] += c1 * c2
    return {m: c for m, c in out.items() if c}


def det(rows):
    n = len(rows)
    if n == 0:
        return {(): 1}
    if n == 1:
        return dict(rows[0][0])
    total = {}
    for j in range(n):
        e = rows[0][j]
        if not e:
            continue
        minor = [r[:j] + r[j + 1:] for r in rows[1:]]
        term = pmul(e, det(minor))
        total = padd(total, {m: ((-1) ** j) * c for m, c in term.items()})
    return total


def wt2(f):
    """Square-weight valuation; +infinity on the zero polynomial."""
    if not f:
        return None
    return min(sum(k * k for k in m) for m in f)


def connected_shapes(size_cap, row_cap):
    seen = set()
    for n in range(2, row_cap + 1):
        for rho in itertools.product(range(1, size_cap + 1), repeat=n):
            if sum(rho) > size_cap:
                continue
            for o in itertools.product(range(1, size_cap + 1), repeat=n - 1):
                if any(o[i] > min(rho[i], rho[i + 1]) for i in range(n - 1)):
                    continue
                mu = [0] * n
                lam = [0] * n
                lam[n - 1] = rho[n - 1]
                for i in range(n - 2, -1, -1):
                    mu[i] = lam[i + 1] - o[i]
                    lam[i] = mu[i] + rho[i]
                if any(v < 0 for v in mu):
                    continue
                if any(lam[i] < lam[i + 1] for i in range(n - 1)):
                    continue
                if any(mu[i] < mu[i + 1] for i in range(n - 1)):
                    continue
                key = (tuple(lam), tuple(mu))
                if key in seen:
                    continue
                seen.add(key)
                yield tuple(lam), tuple(mu)


def cofactors(lam, mu):
    n = len(lam)
    L = lam[0]
    a = [lam[i] - (i + 1) for i in range(n)]
    b = [L - 1] + [mu[j - 1] - j for j in range(1, n + 1)]
    M = [[h(a[i] - b[j]) for j in range(n + 1)] for i in range(n)]
    out = []
    for j in range(n + 1):
        cols = [t for t in range(n + 1) if t != j]
        D = det([[M[i][t] for t in cols] for i in range(n)])
        out.append({m: ((-1) ** j) * c for m, c in D.items()})
    A = [b[0] - a[i] for i in range(n)]
    d = [b[0] - b[j] for j in range(n + 1)]
    return out, A, d


def main():
    shapes = list(connected_shapes(SIZE_CAP, ROW_CAP))
    # bucket by the invariants the hypotheses fix
    buckets = defaultdict(list)
    for lam, mu in shapes:
        n = len(lam)
        key = (mu, lam[0], tuple(sorted(lam[i] - mu[i] for i in range(n))))
        buckets[key].append((lam, mu))

    n_pairs = 0
    n_antecedent = 0
    n_skipped_zero_defect = 0
    n_violations = 0
    changed_rows = defaultdict(int)
    for key, members in buckets.items():
        if len(members) < 2:
            continue
        cache = {}
        for X in members:
            cache[X] = cofactors(*X)
        for X, Y in itertools.combinations(members, 2):
            CX, AX, dX = cache[X]
            CY, AY, dY = cache[Y]
            assert dX == dY  # common cap grid
            d = dX
            n = len(X[0])
            G = [psub(CX[j], CY[j]) for j in range(n + 1)]
            if not any(G):
                n_skipped_zero_defect += 1
                continue
            n_pairs += 1

            v = next(i for i in range(n) if AX[i] != AY[i])
            assert v >= 1, (X, Y)   # common top row forces A_0 = 0 on both

            alpha = [None] * (n + 1)
            for j in range(n + 1):
                w = wt2(G[j])
                alpha[j] = None if w is None else w + d[j] * d[j]

            pos = [j for j in range(1, n + 1) if alpha[j] is not None]
            assert pos, (X, Y)
            m_plus = min(alpha[j] for j in pos)
            T0 = sorted(j for j in pos if alpha[j] == m_plus)

            if alpha[0] is not None and alpha[0] == m_plus:
                continue            # the other branch; the theorem asserts nothing
            n_antecedent += 1
            changed_rows[sum(1 for i in range(n) if AX[i] != AY[i])] += 1

            # (a) the adjacent minimizer chain
            for i in range(v):
                F = {}
                for j in range(n + 1):
                    if alpha[j] is None or d[j] < AX[i]:
                        continue
                    F[j] = alpha[j] + (d[j] - AX[i]) ** 2 - d[j] * d[j]
                assert F, (X, Y, i)
                mn = min(F.values())
                Mi = sorted(j for j in F if F[j] == mn)
                if Mi != [i + 1, i + 2]:
                    n_violations += 1
                    print("VIOLATION M_%d = %s on %s vs %s" % (i, Mi, X, Y))

            # (b) the floor set
            if T0 != [1, 2]:
                n_violations += 1
                print("VIOLATION T_0^+ = %s on %s vs %s" % (T0, X, Y))

            # (c) solid support prefix
            for j in range(1, v + 2):
                if alpha[j] is None:
                    n_violations += 1
                    print("VIOLATION G_%d = 0 on %s vs %s" % (j, X, Y))

            # (d) the exact prefix profile
            prof = [alpha[j] for j in range(1, v + 2)]
            if None not in prof:
                if not (prof[0] == prof[1] if len(prof) > 1 else True):
                    n_violations += 1
                    print("VIOLATION alpha_1 != alpha_2 on %s vs %s" % (X, Y))
                for k in range(1, len(prof) - 1):
                    if not prof[k] < prof[k + 1]:
                        n_violations += 1
                        print("VIOLATION profile not strict on %s vs %s" % (X, Y))

            # (e) the tail
            for j in range(v + 2, n + 1):
                if alpha[j] is not None and alpha[j] <= alpha[v + 1]:
                    n_violations += 1
                    print("VIOLATION tail alpha_%d on %s vs %s" % (j, X, Y))

    print("connected diagrams of size <= %d, rows <= %d : %d"
          % (SIZE_CAP, ROW_CAP, len(shapes)))
    print("hypothesis-meeting pairs with nonzero defect: %d" % n_pairs)
    print("  of these, on the Floor antecedent          : %d" % n_antecedent)
    print("  on the alpha_0 = m_+ branch (not asserted) : %d" % (n_pairs - n_antecedent))
    print("hypothesis-meeting pairs with zero defect    : %d" % n_skipped_zero_defect)
    print("  changed-row counts on the antecedent       : %s"
          % dict(sorted(changed_rows.items())))
    print("violations                                   : %d" % n_violations)
    assert n_violations == 0
    assert n_antecedent > 0
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
