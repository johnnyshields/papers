"""`lem:cofactor-factorization` and `prop:stable-cofactor`: capped cofactors as skew Schur functions, and what
the cofactor vector remembers.

Asserts, over every connected skew diagram of size at most SIZE_CAP with at most
ROW_CAP rows:

  (1) the capped cofactor matrix M_ij = h_{d_j - A_i} of `sec:coordinates` has, after
      deleting column j, exactly the Jacobi-Trudi matrix of lambda / nu^(j) with
        nu^(j) = (lambda_0, mu_0 + 1, ..., mu_{j-2} + 1, mu_j, ..., mu_{n-1})
      for j >= 1 and nu^(0) = mu,
      so that C_j(X) = (-1)^j s_{lambda / nu^(j)};
  (2) nu^(j) is a partition contained in lambda, connectedness entering only as
      lambda_i > mu_{i-1};
  (3) every cofactor of a connected diagram is nonzero;
  (4) the minimum-square-weight monomial of C_j is the single monomial
        prod_{1<=i<j} h_{o_{i-1} - 1} . prod_{i>=j} h_{rho_i},
      with coefficient +-1, where rho_i = lambda_i - mu_i and o_i = lambda_{i+1} - mu_i;
  (5) the ordered ratios of those monomials recover (rho, o), hence the diagram up
      to translation: the cofactor vector is injective on connected diagrams.

Exact integer arithmetic on signed multisets of h-monomials throughout.
"""

import itertools
import sys
from collections import Counter, defaultdict

SIZE_CAP = 11
ROW_CAP = 5

# ---------------------------------------------------------------- polynomials
# A polynomial in Z[h_1, h_2, ...] is a dict {monomial: coefficient} with a
# monomial a sorted tuple of positive indices.  h_0 = 1 contributes nothing.

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


def pmul(f, g):
    out = defaultdict(int)
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            out[tuple(sorted(m1 + m2))] += c1 * c2
    return {m: c for m, c in out.items() if c}


def pscal(c, f):
    return {m: c * v for m, v in f.items()} if c else {}


def det(rows):
    """Exact expansion by minors of a square matrix of polynomials."""
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
        total = padd(total, pscal((-1) ** j, term))
    return total


def wt2(mon):
    return sum(k * k for k in mon)


def initial_face(f):
    """The set of minimum-square-weight monomials of f, and that weight."""
    w = min(wt2(m) for m in f)
    return w, {m: c for m, c in f.items() if wt2(m) == w}


# ---------------------------------------------------------------- diagrams

def connected_shapes(size_cap, row_cap):
    """Connected skew diagrams lambda/mu, normalized so mu_{n-1} = 0 and every
    row nonempty.  Yields (lam, mu) as tuples of length n."""
    seen = set()
    for n in range(1, row_cap + 1):
        # rho_i >= 1 (nonempty rows), o_i >= 1 (connected), i = 0..n-2
        for rho in itertools.product(range(1, size_cap + 1), repeat=n):
            if sum(rho) > size_cap:
                continue
            for o in itertools.product(range(1, size_cap + 1), repeat=max(n - 1, 0)):
                if any(o[i] > min(rho[i], rho[i + 1]) for i in range(n - 1)):
                    continue
                # reconstruct from the profile: mu_{n-1} = 0
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


def jt(lam, nu):
    """Jacobi-Trudi matrix of lam/nu, zero-based rows and columns."""
    n = len(lam)
    return [[h(lam[i] - nu[t] - i + t) for t in range(n)] for i in range(n)]


def cap_matrix(lam, mu):
    """The n x (n+1) capped cofactor matrix M_ij = h_{d_j - A_i} of `sec:coordinates`."""
    n = len(lam)
    L = lam[0]
    a = [lam[i] - (i + 1) for i in range(n)]
    b = [L - 1] + [mu[j - 1] - j for j in range(1, n + 1)]
    return [[h(a[i] - b[j]) for j in range(n + 1)] for i in range(n)], a, b


def nu_j(lam, mu, j):
    """nu^(j) as read off the surviving columns."""
    n = len(lam)
    out = []
    for t in range(n):
        if t >= j:
            out.append(mu[t])
        elif t == 0:
            out.append(lam[0])
        else:
            out.append(mu[t - 1] + 1)
    return tuple(out)


def is_partition_inside(nu, lam):
    n = len(lam)
    if any(nu[t] < nu[t + 1] for t in range(n - 1)):
        return False
    return all(0 <= nu[t] <= lam[t] for t in range(n))


# ---------------------------------------------------------------- the checks

def main():
    shapes = list(connected_shapes(SIZE_CAP, ROW_CAP))
    n_shapes = 0
    n_cofactors = 0
    fingerprints = {}
    for lam, mu in shapes:
        n = len(lam)
        M, a, b = cap_matrix(lam, mu)
        rho = [lam[i] - mu[i] for i in range(n)]
        o = [lam[i + 1] - mu[i] for i in range(n - 1)]

        # the grid is strictly ordered (`lem:grid-order`) and diagonally feasible (`lem:diagonal-feasible`)
        A = [b[0] - a[i] for i in range(n)]
        d = [b[0] - b[j] for j in range(n + 1)]
        assert A == sorted(A) and len(set(A)) == n, (lam, mu, A)
        assert d == sorted(d) and len(set(d)) == n + 1, (lam, mu, d)
        assert A[0] == 0 and d[0] == 0, (lam, mu)
        assert all(A[i] <= d[i] for i in range(n)), (lam, mu, A, d)

        distinguished = []
        for j in range(n + 1):
            nu = nu_j(lam, mu, j)
            # (2) nu^(j) is a partition inside lambda
            assert is_partition_inside(nu, lam), (lam, mu, j, nu)

            cols = [t for t in range(n + 1) if t != j]
            minor = [[M[i][t] for t in cols] for i in range(n)]
            # (1) the surviving minor IS the Jacobi-Trudi matrix of lam/nu^(j)
            assert minor == jt(lam, nu), (lam, mu, j)

            Cj = pscal((-1) ** j, det(minor))
            s = det(jt(lam, nu))
            assert Cj == pscal((-1) ** j, s), (lam, mu, j)

            # (3) nonvanishing
            assert Cj, (lam, mu, j)
            n_cofactors += 1

            # (4) the minimum-square-weight face is one monomial with coefficient +-1
            w, face = initial_face(Cj)
            assert len(face) == 1, (lam, mu, j, face)
            mon, coef = next(iter(face.items()))
            assert coef in (1, -1), (lam, mu, j, coef)
            predicted = tuple(sorted(
                [o[i - 1] - 1 for i in range(1, j) if o[i - 1] - 1 > 0]
                + [rho[i] for i in range(j, n) if rho[i] > 0]))
            assert mon == predicted, (lam, mu, j, mon, predicted)
            assert w == sum(k * k for k in predicted)
            distinguished.append(predicted)

        # (5) the ordered distinguished monomials recover (rho, o).  Column j+1
        # trades h_{rho_j} for h_{o_{j-1} - 1}, and rho_j > o_{j-1} - 1 always,
        # since d_{j+1} - d_j = rho_j - o_{j-1} + 1 = mu_{j-1} - mu_j + 1 >= 1.
        for j in range(n):
            cj = Counter(distinguished[j])
            cj1 = Counter(distinguished[j + 1])
            gone = list((cj - cj1).elements())
            arrived = list((cj1 - cj).elements())
            assert len(gone) <= 1 and len(arrived) <= 1, (lam, mu, j, gone, arrived)
            assert (gone[0] if gone else 0) == rho[j], (lam, mu, j, gone, rho[j])
            if j >= 1:
                assert (arrived[0] if arrived else 0) + 1 == o[j - 1], \
                    (lam, mu, j, arrived, o[j - 1])
            else:
                assert not arrived, (lam, mu, j, arrived)
            assert d[j + 1] - d[j] == rho[j] - (o[j - 1] if j >= 1 else lam[0]) + 1 \
                if j >= 1 else True

        fp = tuple(tuple(sorted(c.items())) for c in
                   [pscal((-1) ** j, det([[M[i][t] for t in range(n + 1) if t != j]
                                          for i in range(n)]))
                    for j in range(n + 1)])
        assert fp not in fingerprints or fingerprints[fp] == (lam, mu), \
            (lam, mu, fingerprints.get(fp))
        fingerprints[fp] = (lam, mu)
        n_shapes += 1

    print("connected diagrams of size <= %d, rows <= %d : %d"
          % (SIZE_CAP, ROW_CAP, n_shapes))
    print("cofactors checked                          : %d" % n_cofactors)
    print("distinct cofactor vectors                  : %d" % len(fingerprints))
    assert len(fingerprints) == n_shapes
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
