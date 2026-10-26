#!/usr/bin/env python3
"""Exact lowering, pre-wall coarsening, and unequal-terminal cut decoding."""
from profile_tools import (add, betas, component, compositions, determinant,
                           family, inner, monomial, mul, power, scale, schur)
from verify_class_exposure import coarsen


def lower(f, n, t):
    assert t > 0
    out = {}
    for m, c in f.items():
        if len(m) == n and min(m) >= t:
            key = tuple(a-t for a in m if a > t)
            out[key] = out.get(key, 0)+c
    return {m:c for m,c in out.items() if c}


def main():
    count = prewall = cutchecks = 0
    cases = (inner((1, 2), 2), ((3, 4, 5), (1, 2)),
             ((4, 3, 6), (2, 2)), ((3, 5), (1,)))
    for E in cases:
        X, Y = betas(E)
        S, u, v = X[0], X[0]-X[1], Y[-2]
        p = min(u, v)
        assert set(X).isdisjoint(Y)
        for M in range(1, 4):
            for alpha in compositions(M):
                D = family(E, alpha)
                for t in range(1, p+2):
                    assert lower(schur(D, t), len(D[0]), t) == schur(D)
                    count += 1
                for t in range(p):
                    rhs = {}
                    for beta in coarsen(alpha):
                        cuts = len(alpha)-len(beta)
                        term = monomial((t,)*cuts, (-1)**cuts)
                        for m in beta:
                            term = mul(term, schur(power(E, m), t))
                        rhs = add(rhs, term)
                    assert schur(D, t) == rhs
                    prewall += 1
                if u < v:
                    J = {x+p for x in X[2:]} & set(Y[:-1])
                    Q = set(Y[:-1])-J
                    P = {x+p for x in X[2:]}-J
                    T = {sum(alpha[i:]) for i in range(1, len(alpha))}
                    Z = {j*S+z for j in range(M) for z in J} | {j*S for j in T}
                    U0 = {M*S+p} | {j*S for j in range(1, M+1)} | {j*S+x for j in range(M) for x in P}
                    U = tuple(sorted((U0-{j*S for j in T}) | {j*S+p for j in T}, reverse=True))
                    V = tuple(sorted({0} | {j*S+y for j in range(M) for y in Q}, reverse=True))
                    x, y = betas(D)
                    x = tuple(a+p for a in x)
                    assert set(x) & set(y) == Z
                    assert tuple(a for a in x if a not in Z) == U
                    assert tuple(a for a in y if a not in Z) == V
                    epsilon = (-1)**sum(x.index(z)+y.index(z) for z in Z)
                    f = component(schur(D, p), len(U))
                    assert f == scale(determinant(tuple(tuple(a-b for b in V) for a in U)), epsilon)
                    support = {a for mon in f for a in mon}
                    assert {k for k in range(1, M) if k*S+p in support} == T
                    cutchecks += 1
    print(f"Lowering identities: {count}; pre-wall coarsenings: {prewall} PASS")
    print(f"Asymmetric complete-deletion and private-cut decoders: {cutchecks} PASS")
    print("ALL PASS")


if __name__ == '__main__':
    main()
