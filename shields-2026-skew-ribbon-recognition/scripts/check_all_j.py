"""The cutoff family J_a of two coequal coarse boards (ph:all-J).

Paper section `app:physical` (Whole currents and the first complete grade), ph:all-J.

Over generic letters R_0, R_1, ... (R_l = 0 for l < 0), for every pair of distinct connected
coequal diagrams V, V' of span M (3 <= M <= MMAX) with absolute adjugate difference
Delta A(j, k), build the prefixes C_{a,D} = -sum_{j-k=D, k>=a} Delta A(j, k) and
J_a = sum_D C_{a,D} R_{D+a-1} (`allJ` in the Lean tree), and check:

* some J_a, 2 <= a < M, is not divisible by the common whole polynomial e (the lemma);
* for every a with 2 <= a < M, J_a is divisible by e only when it is zero (`not_dvd_allJ`), so
  the lemma is equivalent to the nonvanishing of some J_a;
* the two divisibility tests agree: reduction modulo the principal ideal (e), where {e} is a
  Groebner basis, and substitution of the root in R_M, the unique top letter of e.

The pair count is asserted against `check_first_grade.py`, which enumerates the same pairs by a
different construction.
"""
import itertools
import sys

import sympy as sp

MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
PAIRS = {3: 2, 4: 8, 5: 32, 6: 112}
R = sp.symbols('R0:20')


def profiles(M):
    """Connected normalized beta pairs of span M: rows in (0, M] with M, columns in [0, M) with 0."""
    out = []
    for xm in range(1 << (M - 1)):
        X = [M] + [k for k in range(M - 1, 0, -1) if xm >> (k - 1) & 1]
        for ym in range(1 << (M - 1)):
            Y = [k for k in range(M - 1, 0, -1) if ym >> (k - 1) & 1] + [0]
            if len(X) != len(Y):
                continue
            n = len(X)
            if all(Y[i] < X[i] for i in range(n)) and all(Y[i] <= X[i + 1] for i in range(n - 1)):
                out.append((tuple(X), tuple(Y)))
    return out


def L(k):
    return 0 if k < 0 else R[k]


def mat(p):
    X, Y = p
    return sp.Matrix(len(X), len(X), lambda i, j: L(X[i] - Y[j]))


def adjdict(p):
    X, Y = p
    A = mat(p).adjugate()
    return {(x, y): sp.expand(A[j, i]) for i, x in enumerate(X) for j, y in enumerate(Y)}


def divisible_by_root(J, e, M):
    kap = sp.diff(e, R[M])
    assert kap != 0 and sp.diff(kap, R[M]) == 0, 'e is not linear in its top letter'
    e0 = sp.expand(e - kap * R[M])
    return sp.expand(sp.numer(sp.together(J.subs(R[M], -e0 / kap)))) == 0


def divisible_by_reduction(J, e, M):
    gens = R[:M + 1]
    _, rem = sp.reduced(J, [e], *gens)
    return sp.expand(rem) == 0


for M in range(3, MMAX + 1):
    groups = {}
    for p in profiles(M):
        groups.setdefault(sp.expand(mat(p).det()), []).append(p)
    pairs = nonzero = 0
    for e, grp in groups.items():
        ads = {p: adjdict(p) for p in grp}
        for V, W in itertools.permutations(grp, 2):
            pairs += 1

            def dA(j, k):
                return ads[V].get((j, k), 0) - ads[W].get((j, k), 0)

            good = []
            for a in range(2, M):
                J = sp.expand(-sum(dA(j, k) * L(j - k + a - 1)
                                   for k in range(a, M + 1) for j in range(0, M + 1)))
                d1 = divisible_by_root(J, e, M)
                if M <= 5:
                    assert d1 == divisible_by_reduction(J, e, M), (V, W, a)
                assert d1 == (J == 0), ('a nonzero J_a divisible by e', V, W, a)
                if J != 0:
                    nonzero += 1
                    good.append(a)
            assert good, ('ph:all-J fails', M, V, W)
    assert pairs == PAIRS[M], (M, pairs)
    print(f'M = {M}: {pairs} ordered coequal pairs, {nonzero} nonzero J_a, '
          f'each pair has one not divisible by e')
print('check_all_j: PASS')
