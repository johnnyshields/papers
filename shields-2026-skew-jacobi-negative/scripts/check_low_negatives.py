#!/usr/bin/env python3
"""Low-negative formulas, singleton contexts, square units, and four-row identities.

Four-row parameters c=0..2, w=c+1..c+3, b=c+w+1..c+w+3.
Singleton contexts use three stated blocks, with margins 1..3 plus the
reflected equal-endpoint control.  These are finite formula checks.
"""
from collections import Counter
from itertools import product
import sympy as sp
from jacobi_trudi import *
import formal_polynomial as formal


def context(Q,s,u,v,g):
    C,D=Q
    z=v+C[0]+g
    return (z+s+u,z+s)+tuple(v+c for c in C),(z,)+tuple(v+d for d in D)+(0,)


def main():
    counts=Counter()
    c,w,b=sp.symbols('c w b')
    profiles=(((w,b,b,b+w-c),(c,c,w)),((w,b,b+w-c,b),(c,w,c)))
    neg=frozenset(((3,1),(4,1),(4,2)))
    symbolic=[formal.determinant(*formal.profile_betas(*p),neg) for p in profiles]
    assert symbolic[0] and symbolic[0]==symbolic[1]
    for cc in range(3):
        for ww in range(cc+1,cc+4):
            for bb in range(cc+ww+1,cc+ww+4):
                pairs=[from_profile(tuple(int(x.subs({c:cc,w:ww,b:bb})) for x in r),
                                    tuple(int(x.subs({c:cc,w:ww,b:bb})) for x in g)) for r,g in profiles]
                F,H=pairs
                assert determinant(*F)==determinant(*H)
                assert determinant(*F)==formal.specialize(symbolic[0],{c:cc,w:ww,b:bb})
                assert len({F,H,rotation(*F),rotation(*H)})==4
                assert negatives(*F)==neg and negatives(*H)==neg
                if cc>0:
                    t=bb-cc; d=ww-cc; M=4*t+ww; T=3*bb-2*cc
                    diff=add((1,determinant(*border(*F,t,t))),(-1,determinant(*border(*H,t,t))))
                    actual=coefficient(coefficient(diff,M),T)
                    want=multiply(h(ww),add((-1,multiply(h(cc),h(bb+d))),(1,multiply(h(ww),h(bb)))))
                    assert actual==want and actual
                    counts['tied_corner']+=1
                counts['four_row_pairs']+=1
    # Different ordinary degrees on a genuine-unit square cofactor.
    X=(13,12,9,6,5); Y=(9,7,4,2,0)
    Q=determinant(X[1:],Y[:-1])
    assert set(map(len,Q))=={3,4}
    want=multiply(add((1,multiply(h(3),h(2))),(-1,h(5))),
                  add((1,multiply(h(2),h(3))),(-1,multiply(h(4),h(1)))))
    assert Q==want
    rejects(lambda: require(all(len(m)==4 for m in Q)))
    blocks=[((6,4),(2,0)),((7,5,3),(4,1,0)),((9,7,6,3),(4,2,1,0))]
    for Q in blocks:
        validate(*Q)
        for s,u,v,g in product(range(1,4),repeat=4):
            F=context(Q,s,u,v,g); validate(*F)
            P=determinant(*F); a=s+g
            formula=add((1,multiply(h(s+u),determinant(*border(*Q,a,v)))),
                        (-1,multiply(h(s),determinant(*border(*Q,a+u,v)))))
            assert P==formula==permutation_determinant(*F)
            M=F[0][0]-min(u,v); q=min(u,v); eps=(-1)**(len(Q[0])+1)
            top=multiply(h(s+q),determinant(*Q))
            bottom=multiply(h(s),determinant(*extend(*Q,q,False)))
            marker=top if u<v else bottom if v<u else add((1,top),(1,bottom))
            assert coefficient(P,M)=={m:-eps*c for m,c in marker.items()}
            counts['singleton_contexts']+=1
            counts['top' if u<v else 'bottom' if v<u else 'tie']+=1
    # Both border differences have doubled tops; their common-level separator survives.
    Q=((7,5,3),(4,1,0)); Qstar=rotation(*Q)
    F=context(Q,1,1,5,1); H=context(Qstar,1,1,5,1)
    first=add((1,determinant(*border(*Q,2,5))),(-1,determinant(*border(*Qstar,2,5))))
    second=add((1,determinant(*border(*Q,3,5))),(-1,determinant(*border(*Qstar,3,5))))
    assert largest(first)==largest(second)==12
    assert largest(multiply(h(2),first))==largest(multiply(h(1),second))==12
    rejects(lambda: require(largest(second)>largest(first)))
    diff=add((1,determinant(*F)),(-1,determinant(*H)))
    assert coefficient(coefficient(diff,12),9)==multiply(h(3),multiply(h(1),h(1)))
    rejects(lambda: require(determinant(*F)==determinant(*H)))
    for n in range(5,10):
        # Uniform profiles give symmetric endpoint controls at orders five through nine.
        rows=(n+2,)*n; gaps=(n,)*(n-1)
        X,Y=from_profile(rows,gaps)
        for t in (1,2):
            assert determinant(*extend(X,Y,t))==determinant(*extend(X,Y,t,False))
    assert all(counts[k]>0 for k in ('four_row_pairs','tied_corner','top','bottom','tie'))
    print('LOW_NEGATIVES',dict(counts),'CONTROLS FIRED: homogeneous cofactor, strictly larger second top, false hook equality')
    print('ALL PASS')


if __name__=='__main__':
    main()
