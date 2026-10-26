#!/usr/bin/env python3
"""Full-board readings and homogenization; rows 2--4, lengths 1--4.

Every legal gap word in this rectangular row-length box is included.  This
checks the identities, not an unbounded classification by a finite census.
"""
from collections import Counter
from itertools import product
from jacobi_trudi import *


def main():
    counts=Counter()
    for n in range(2,5):
        for rows in product(range(1,5),repeat=n):
            for gaps in product(*(range(min(rows[i],rows[i+1])) for i in range(n-1))):
                X,Y=from_profile(rows,gaps)
                P=determinant(X,Y)
                assert P==permutation_determinant(X,Y)
                assert profile(X,Y)==(rows,gaps)
                assert P==determinant(*rotation(X,Y))
                assert max(map(len,P))==n
                assert min(map(len,P))==n-len(set(X)&set(Y))
                initial=min(P,key=lambda m:sum(k*k for k in m))
                assert initial==tuple(sorted(rows,reverse=True)) and P[initial]==1
                assert largest(P)==X[0]
                Q=determinant(X[1:],Y[:-1])
                assert coefficient(P,X[0])=={m:(-1)**(n-1)*c for m,c in Q.items()}
                diagonal=min(Q,key=lambda m:sum(k*k for k in m))
                assert tuple(sorted(diagonal+(0,)*(n-1-len(diagonal))))==tuple(sorted(gaps))
                G=gamma(X,Y)
                validate(*G)
                assert negatives(*G)==negatives(X,Y) and not(set(G[0])&set(G[1]))
                assert determinant(*G)==homogenize(P,n)
                assert rotation(*G)==gamma(*rotation(X,Y))
                counts['boards']+=1
                counts['units' if set(X)&set(Y) else 'zero_free']+=1
    assert counts['boards']>0 and counts['units']>0 and counts['zero_free']>0
    X,Y=from_profile((1,2,2,3),(0,0,1))
    assert set(X)&set(Y)
    rejects(lambda: require(len(negatives(X,Y))==sum(x<=y for x in X for y in Y)))
    rejects(lambda: validate((2,1),(2,0)))
    print('BOARDS',dict(counts),'CONTROLS FIRED: unit counted as negative, empty row')
    print('ALL PASS')


if __name__=='__main__':
    main()
