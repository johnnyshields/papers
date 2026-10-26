#!/usr/bin/env python3
"""Check the independent-alphabet inverse and the complete balanced-wall data."""
from itertools import product
import sympy as sp
from profile_tools import (add, betas, coefficient, component, compositions,
                           core_data, determinant, family, inner, scale,
                           schur, word_matrix)


def symbolic_word(delta, a, b, c):
    if not delta:
        return c
    xi = [0]
    for d in delta:
        xi.append(xi[-1]+d)
    L, M = len(delta), xi[-1]
    mat = sp.Matrix([[b[x] for x in xi[1:]]+[c]] + [
        [a[xi[j]-xi[i-1]] if j >= i else 0 for j in range(1, L+1)]
        + [b[M-xi[i-1]]] for i in range(1, L+1)])
    return mat.det(method='berkowitz').expand()


def word_checks():
    comparisons = 0
    for M in range(1, 8):
        a, b, c = {i:i for i in range(1, M+1)}, {i:M+i for i in range(1, M+1)}, 2*M+1
        classes = {}
        for delta in compositions(M):
            f = determinant(word_matrix(delta, a, b, c))
            key = tuple(sorted(f.items()))
            expected = min(delta, delta[::-1])
            assert classes.setdefault(key, expected) == expected, (M, delta)
            comparisons += 1
            d = min(delta[0], delta[-1])
            support = {j-M for mon in f for j in mon if M < j <= 2*M}
            assert min(support) == d
            assert max(mon.count(M+d) for mon in f) == (2 if delta[0] == delta[-1] else 1)
            if delta[0] < delta[-1]:
                tail = {mon: coeff for mon, coeff in f.items() if M+d in mon}
                seen = {j-M for mon in tail for j in mon if M < j <= 2*M and j != M+d}
                assert seen == {sum(delta[i:]) for i in range(len(delta))}
    shells = 0
    for d, gamma in ((1, ()), (1, (2,)), (1, (1, 2)), (2, (1, 3)), (1, (2, 1, 2)), (2, (1, 1))):
        delta = (d,)+gamma+(d,)
        M = sum(delta)
        a = dict(enumerate(sp.symbols(f'a0:{M+1}')))
        b = dict(enumerate(sp.symbols(f'b0:{M+1}')))
        c = sp.Symbol('c')
        mu = a[d]/b[d]
        bp = {j: a[d+j]-mu*b[d+j] for j in range(1, sum(gamma)+1)}
        cp = a[M]-2*mu*b[M]+mu**2*c
        assert sp.cancel(symbolic_word(delta, a, b, c)
                         - b[d]**2*symbolic_word(gamma, a, bp, cp)) == 0
        for j, value in bp.items():
            assert sp.cancel((a[d+j]-value)/mu-b[d+j]) == 0
        assert sp.cancel((cp-a[M]+2*mu*b[M])/mu**2-c) == 0
        shells += 1
    return comparisons, shells


def deletion_check(E, alpha):
    S, p, J, T, K, Z, U, V = core_data(E, alpha)
    x, y = betas(family(E, alpha))
    X = tuple(a+p for a in x)
    assert set(X) & set(y) == Z
    assert tuple(a for a in X if a not in Z) == U
    assert tuple(a for a in y if a not in Z) == V
    sign = (-1)**sum(X.index(z)+y.index(z) for z in Z)
    assert sign == 1
    assert all(X.index(z)-y.index(z) == 2 for z in Z)
    assert len(U) == sum(alpha)-len(alpha)+2
    marks = sorted({0, sum(alpha)} | K)
    delta = tuple(b-a for a, b in zip(marks, marks[1:]))[::-1]
    core = tuple(tuple(a-b for b in V) for a in U)
    word = word_matrix(delta, {j:j*S-p for j in range(1, sum(alpha)+1)},
                       {j:j*S for j in range(1, sum(alpha)+1)}, sum(alpha)*S+p)
    assert tuple(tuple(v if v > 0 else -1 for v in row) for row in core) == word
    return S, p, J, K, U, V, core


def correction_check(E, alpha):
    S, p, J, K, U, V, core = deletion_check(E, alpha)
    M, kappa = sum(alpha), len(U)
    Jstar = {S+p-j for j in J}
    assert J != Jstar and alpha != alpha[::-1]
    a = min(J ^ Jstar)
    lam = int(a in J)-int(a in Jstar)
    k = min(K-{M-v for v in K})
    A, B = a-p, k*S+p-a
    assert A > 0 and B > 0 and A != B
    assert A % S not in {0, p, S-p} and B % S not in {0, p, S-p}
    assert [(i, j) for i, row in enumerate(core) for j, v in enumerate(row) if v == k*S] == [(U.index(k*S), V.index(0))]
    i, j = U.index(k*S), V.index(0)
    minor = tuple(tuple(v for l, v in enumerate(row) if l != j)
                  for krow, row in enumerate(core) if krow != i)
    Dk = scale(determinant(minor), (-1)**(i+j))
    assert Dk
    f = schur(family(E, alpha), p, max_degree=kappa+1)
    r = schur(family(E, alpha[::-1]), p, max_degree=kappa+1)
    assert component(f, kappa) == determinant(core) == component(r, kappa)
    diff = add(component(f, kappa+1), scale(component(r, kappa+1), -1))
    assert coefficient(diff, (A, B)) == scale(Dk, lam), (E, alpha, A, B)


def main():
    words, shells = word_checks()
    deletions = corrections = equalities = 0
    for K in range(1, 5):
        for g in product((1, 2, 3), repeat=K):
            for p in (1, 2):
                E = inner(g, p)
                for M in range(1, 5):
                    for alpha in compositions(M):
                        deletion_check(E, alpha)
                        deletions += 1
    for g in ((1, 2), (1, 3, 2), (1, 2, 3, 1)):
        for p in (1, 2):
            for alpha in ((1, 2), (2, 1), (1, 3), (1, 1, 2)):
                correction_check(inner(g, p), alpha)
                corrections += 1
    # Entire polynomials, not only the separating correction, on small parents.
    for g in ((1,), (1, 1), (1, 2)):
        E = inner(g, 1)
        for M in range(1, 4):
            for t in (1, 2):
                fs = {a: schur(family(E, a), t) for a in compositions(M)}
                for a, f in fs.items():
                    for b, h in fs.items():
                        expected = b == a or (g == g[::-1] and b == a[::-1])
                        assert (f == h) == expected, (g, M, t, a, b)
                        equalities += 1
    print(f"Independent-alphabet words: {words}; faithful shell identities: {shells} PASS")
    print(f"Complete wall beta sets, deletion signs, and literal word boards: {deletions} PASS")
    print(f"First-correction separating coefficients: {corrections} PASS")
    print(f"Full wall/later equality comparisons: {equalities} PASS")
    print("ALL PASS")


if __name__ == '__main__':
    main()
