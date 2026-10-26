"""Free complete-function polynomials whose subscripts are integer linear forms."""
from collections import Counter
from itertools import permutations
import sympy as sp


def monomial(labels):
    return tuple(sorted((sp.expand(k) for k in labels), key=sp.default_sort_key))


def profile_betas(rows,gaps):
    Y=[sp.Integer(0)]*len(rows)
    for i in range(len(rows)-2,-1,-1):
        Y[i]=sp.expand(Y[i+1]+rows[i+1]-gaps[i])
    return tuple(sp.expand(r+y) for r,y in zip(rows,Y)),tuple(Y)


def determinant(X,Y,negative_sites):
    out=Counter()
    for p in permutations(range(len(X))):
        if any((i+1,j+1) in negative_sites for i,j in enumerate(p)):
            continue
        sign=(-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
        out[monomial(X[i]-Y[j] for i,j in enumerate(p))]+=sign
    return {m:c for m,c in out.items() if c}


def specialize(P,values):
    out=Counter()
    for mon,c in P.items():
        labels=[k.subs(values) for k in mon]
        assert all(k.is_Integer and k>=0 for k in labels)
        out[tuple(sorted((int(k) for k in labels if k),reverse=True))]+=c
    return {m:c for m,c in out.items() if c}
