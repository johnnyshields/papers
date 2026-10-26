"""`lem:starvation` and `prop:block-factorization` (`app:rank4`): passive-tail starvation and the block factorization of a minor.

For a defect G on a common cap grid, a column j is PASSIVE when d_j > e, where
e = max supp G, and ACTIVE otherwise; a row i is STARVED when it vanishes on
every active column, that is when d_j < A_i for every active j.  Write P for the
number of passive columns and R_high for the set of starved rows.

Asserts, over EVERY pair of distinct connected skew diagrams on a common cap grid -- a
common inner boundary mu, a common top row and a common number of rows, with no condition on
the row-length multisets or on how many rows differ:

  (i)   |R_high| <= P - 1, on each parent separately (`lem:starvation`);
  (ii)  how far the bound is from tight.  The deficiency P - 1 - |R_high| is tabulated per parent
        profile.  `cor:both-passive` carries |R_high| = P - 1 as a hypothesis because the paper
        does not prove it; the table is the record of the range over which it has been observed
        (every measured profile here), and the assert below pins that record, so a population in
        which it fails is reported rather than silently included;
  (iii) every square submatrix that uses all of R_high and whose passive columns
        number exactly |R_high| is block triangular WITHOUT any row or column
        permutation, and its determinant is det L . det H with no sign
        (`prop:block-factorization`);
  (iv)  deleting two passive columns leaves a matrix on which every square
        submatrix containing R_high has determinant zero (`cor:both-passive`).

Exact integer arithmetic on signed multisets of h-monomials throughout.
"""

import itertools
import sys
from collections import defaultdict

SIZE_CAP = 12
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


def grid(lam, mu):
    n = len(lam)
    L = lam[0]
    a = [lam[i] - (i + 1) for i in range(n)]
    b = [L - 1] + [mu[j - 1] - j for j in range(1, n + 1)]
    M = [[h(a[i] - b[j]) for j in range(n + 1)] for i in range(n)]
    A = [b[0] - a[i] for i in range(n)]
    d = [b[0] - b[j] for j in range(n + 1)]
    return M, A, d


def cofactor_vector(M, n):
    out = []
    for j in range(n + 1):
        cols = [t for t in range(n + 1) if t != j]
        D = det([[M[i][t] for t in cols] for i in range(n)])
        out.append({m: ((-1) ** j) * c for m, c in D.items()})
    return out


def main():
    shapes = list(connected_shapes(SIZE_CAP, ROW_CAP))
    buckets = defaultdict(list)
    for lam, mu in shapes:
        n = len(lam)
        buckets[(mu, lam[0], n)].append((lam, mu))

    n_pairs = 0
    n_tight = 0
    deficiency = defaultdict(int)
    n_profiles = 0
    n_transferred_starved = 0
    n_block = 0
    n_hall = 0
    n_two_row = 0
    for key, members in buckets.items():
        if len(members) < 2:
            continue
        cache = {X: grid(*X) for X in members}
        cof = {X: cofactor_vector(cache[X][0], len(X[0])) for X in members}
        for X, Y in itertools.combinations(members, 2):
            n = len(X[0])
            lamX, lamY = X[0], Y[0]
            diff = [i for i in range(n) if lamX[i] != lamY[i]]
            if len(diff) == 2 and diff[1] == diff[0] + 1:
                n_two_row += 1
            MX, AX, d = cache[X]
            MY, AY, _ = cache[Y]
            G = [psub(cof[X][j], cof[Y][j]) for j in range(n + 1)]
            supp = [j for j in range(n + 1) if G[j]]
            if not supp:
                continue
            n_pairs += 1
            e = d[max(supp)]
            j0 = min(j for j in range(n + 1) if d[j] > e) if d[n] > e else n + 1
            P = (n + 1) - j0
            if P == 0:
                continue
            for (M, A) in ((MX, AX), (MY, AY)):
                active = [j for j in range(n + 1) if d[j] <= e]
                passive = [j for j in range(n + 1) if d[j] > e]
                assert passive == list(range(j0, n + 1))
                Rhigh = [i for i in range(n) if all(not M[i][j] for j in active)]
                # starved rows are an upper segment of the row order
                assert Rhigh == list(range(n - len(Rhigh), n)), (X, Y, Rhigh)

                # (i) the forced bound
                assert len(Rhigh) <= P - 1, (X, Y, len(Rhigh), P)

                # (ii) how far from tight, measured
                n_profiles += 1
                deficiency[P - 1 - len(Rhigh)] += 1
                if len(Rhigh) == P - 1:
                    n_tight += 1
                if any(i in Rhigh for i in diff):
                    n_transferred_starved += 1

                # (iii) block factorization with no sign
                if Rhigh and len(Rhigh) <= len(passive):
                    k = len(Rhigh)
                    for Jp in itertools.combinations(passive, k):
                        for Ja in itertools.combinations(active, n - k):
                            R = list(range(n))
                            J = list(Ja) + list(Jp)
                            S = [[M[i][j] for j in J] for i in R]
                            Lblk = [[M[i][j] for j in Ja] for i in range(n - k)]
                            Hblk = [[M[i][j] for j in Jp] for i in Rhigh]
                            # the lower-left block is identically zero
                            assert all(not M[i][j] for i in Rhigh for j in Ja)
                            assert det(S) == pmul(det(Lblk), det(Hblk)), (X, Y)
                            n_block += 1

                # (iv) two passive columns deleted: R_high starves
                if len(Rhigh) > P - 2 >= 0 and len(passive) >= 2:
                    for pp in itertools.combinations(passive, 2):
                        rest = [j for j in range(n + 1) if j not in pp]
                        keep = [j for j in rest if d[j] > e]
                        if len(Rhigh) > len(keep):
                            for R in itertools.combinations(range(n), len(rest)):
                                if not set(Rhigh) <= set(R):
                                    continue
                                S = [[M[i][j] for j in rest] for i in R]
                                assert not det(S), (X, Y, pp, R)
                                n_hall += 1

    print("common-cap-grid pairs, size <= %d, rows <= %d : %d (of which two adjacent rows differ: %d)"
          % (SIZE_CAP, ROW_CAP, n_pairs, n_two_row))
    print("parent tail profiles measured                  : %d" % n_profiles)
    print("  of these tight, |R_high| = P - 1             : %d" % n_tight)
    print("  deficiency P - 1 - |R_high| histogram        : %s"
          % dict(sorted(deficiency.items())))
    print("  profiles with a starved transferred row      : %d" % n_transferred_starved)
    print("block factorizations det S = det L . det H     : %d" % n_block)
    print("both-passive vanishing minors                  : %d" % n_hall)
    assert n_pairs > 0 and n_block > 0
    # the observed range of the capacity hypothesis of `cor:both-passive`
    assert n_tight == n_profiles, dict(deficiency)
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
