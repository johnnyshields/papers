"""The first nonzero grade of the absolute adjugate difference (ph:first-grade).

Paper section `app:physical` (Whole currents and the first complete grade), ph:first-grade.

For every pair of distinct connected coequal diagrams V, V' of span M (3 <= M <= MMAX), with
R_0 = rho and R_l = eps x_l for l > 0, take the first grade mu of eps at which the absolute adjugate
difference Delta A(j, k) is nonzero, and check that some d = M - a >= ceil(M/2), 1 <= a <= M - 2,
satisfies the three assertions of the lemma:

* Delta A^[mu](d, 0) = -Delta A^[mu](M, M - d) = U_d != 0, and both boundary differences vanish
  for every D > d;
* the entire prefixes C_{b,D} = -sum_{j-k=D, k>=b} Delta A^[mu](j, k) satisfy
  C_{1,d} = C_{M-d,d} != 0 and C_{b,d} = 0 for b > M - d.

This is `FirstGradeStatement` in the Lean tree.  Coequality is equality of the Jacobi--Trudi
determinants in independent letters; diagrams are normalized (top row M, bottom column 0), so a
translate is the same diagram.  The number of ordered pairs is asserted, so a change in the
enumeration fails rather than silently checking fewer pairs.
"""
import itertools
import sys

import sympy as sp

MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
PAIRS = {3: 2, 4: 8, 5: 32, 6: 112}
eps, rho = sp.symbols('eps rho')
xs = sp.symbols('x1:20')
hs = sp.symbols('h1:20')


def profiles(M):
    """Connected skew diagrams of span M as beta lists (xi, zeta), from row lengths and overlaps."""
    out = []
    for n1 in range(1, M + 1):
        for r in itertools.product(range(1, M + 1), repeat=n1):
            n = n1 - 1
            for g in itertools.product(*[range(0, min(r[i], r[i + 1])) for i in range(n)]):
                zeta = [sum(r[k + 1] - g[k] for k in range(i, n)) for i in range(n + 1)]
                xi = [zeta[i] + r[i] for i in range(n + 1)]
                if xi[0] == M:
                    out.append((tuple(xi), tuple(zeta)))
    return out


def H(k):
    return 0 if k < 0 else (1 if k == 0 else hs[k - 1])


def R(k):
    return 0 if k < 0 else (rho if k == 0 else eps * xs[k - 1])


def schur(p):
    xi, ze = p
    return sp.expand(sp.Matrix(len(xi), len(xi), lambda i, j: H(xi[i] - ze[j])).det())


def absadj(p):
    """Absolute adjugate entries keyed by (row value, column value)."""
    xi, ze = p
    A = sp.Matrix(len(xi), len(xi), lambda i, j: R(xi[i] - ze[j])).adjugate()
    return {(x, z): sp.expand(A[j, i]) for i, x in enumerate(xi) for j, z in enumerate(ze)}


def grade(d, mu, jk):
    return sp.expand(d.get(jk, 0)).coeff(eps, mu)


def check(M):
    groups = {}
    for p in profiles(M):
        groups.setdefault(schur(p), []).append(p)
    pairs = 0
    for grp in groups.values():
        adjs = {p: absadj(p) for p in grp}
        for V, W in itertools.permutations(grp, 2):
            pairs += 1
            dV, dW = adjs[V], adjs[W]
            keys = set(dV) | set(dW)

            def gd(mu, j, k):
                return sp.expand(grade(dV, mu, (j, k)) - grade(dW, mu, (j, k)))

            mu = 0
            while all(gd(mu, j, k) == 0 for (j, k) in keys):
                mu += 1
                assert mu <= 2 * M, (V, W, 'adjugates agree at every grade')
            witnesses = []
            for d in range((M + 1) // 2, M):
                a = M - d
                if not 1 <= a <= M - 2:
                    continue
                U = gd(mu, d, 0)
                if U == 0 or sp.expand(U + gd(mu, M, M - d)) != 0:
                    continue
                if any(gd(mu, D, 0) != 0 or gd(mu, M, M - D) != 0 for D in range(d + 1, M + 1)):
                    continue

                def C(b, D):
                    return sp.expand(-sum(gd(mu, k + D, k) for k in range(b, M - D + 1)))

                if C(1, d) == 0 or sp.expand(C(1, d) - C(M - d, d)) != 0:
                    continue
                if any(C(b, d) != 0 for b in range(M - d + 1, M + 2)):
                    continue
                witnesses.append(d)
            assert witnesses, ('ph:first-grade fails', M, V, W, mu)
    return pairs


total = 0
for M in range(3, MMAX + 1):
    n = check(M)
    print(f'M = {M}: {n} ordered coequal pairs, every one has a first-grade witness d')
    if M in PAIRS:
        assert n == PAIRS[M], (M, n)
    total += n
if MMAX == 6:
    assert total == 154, total
print('check_first_grade: PASS')
