#!/usr/bin/env python3
"""Five-negative families and border separators.

Complete parameter box 2<=g<=4, 1<=q<=b<g, both families; endpoint
lengths 1..3 and all border margins 1..3.  Identities are also formal.
"""
from itertools import product
from collections import Counter
import sympy as sp
from jacobi_trudi import *
import formal_polynomial as formal


def main():
    b,g,q=sp.symbols('b g q')
    X=tuple(b+k*g for k in range(4,-1,-1))
    Ys=(((3*g,g+q,g,q,0),(2*g+q,2*g,g,q,0)),
        ((3*g+q,g+q,g,q,0),(2*g+q,2*g,g+q,q,0)))
    symbols=[]
    for kind,YY in enumerate(Ys,1):
        controls=five_family(kind,2,3,1)
        polys=[formal.determinant(X,Y,negatives(*seed)) for Y,seed in zip(YY,controls)]
        assert polys[0] and polys[0]==polys[1]
        symbols.append(polys[0])
        XB=(X[0]+g,)+X
        YB=[tuple(Y)+( -g,) for Y in YY]
        originals=[border(*seed,3,3) for seed in controls]
        formal_borders=[formal.determinant(XB,Y,negatives(*seed)) for Y,seed in zip(YB,originals)]
        diff=Counter(formal_borders[0]); diff.subtract(formal_borders[1])
        labels=(b,b,b,b+5*g,b+2*g-q,b+4*g-q) if kind==1 else (b,b,b+5*g,b+g-q,b+g-q,b+4*g-q)
        assert diff[formal.monomial(labels)]==(1 if kind==1 else -1)
    counts=Counter()
    for kind in (1,2):
        for gg in range(2,5):
            for bb in range(1,gg):
                for qq in range(1,bb+1):
                    F,H=five_family(kind,bb,gg,qq)
                    validate(*F); validate(*H)
                    assert len({F,H,rotation(*F),rotation(*H)})==4
                    assert len(negatives(*F))==len(negatives(*H))==5
                    assert determinant(*F)==determinant(*H)==formal.specialize(symbols[kind-1],{b:bb,g:gg,q:qq})
                    for t in range(1,4):
                        for first,second in product((True,False),repeat=2):
                            assert determinant(*extend(*F,t,first))!=determinant(*extend(*H,t,second))
                            counts['endpoint']+=1
                    for u,v in product(range(1,4),repeat=2):
                        for Q,R in product((F,rotation(*F)),(H,rotation(*H))):
                            for up,vp in {(u,v),(v,u)}:
                                assert determinant(*border(*Q,u,v))!=determinant(*border(*R,up,vp))
                                counts['border']+=1
                    diff=add((1,determinant(*border(*F,gg,gg))),(-1,determinant(*border(*H,gg,gg))))
                    labels=(bb,bb,bb,bb+5*gg,bb+2*gg-qq,bb+4*gg-qq) if kind==1 else (bb,bb,bb+5*gg,bb+gg-qq,bb+gg-qq,bb+4*gg-qq)
                    assert diff[tuple(sorted(labels,reverse=True))]==(1 if kind==1 else -1)
                    counts['units' if bb==qq else 'zero_free']+=1
    assert all(counts[k]>0 for k in ('endpoint','border','units','zero_free'))
    F,H=five_family(1,2,3,1)
    rejects(lambda: require(H in (F,rotation(*F))))
    F1=border(*F,1,2); H1=border(*H,1,2)
    assert coefficient(determinant(*F1),F1[0][0])==coefficient(determinant(*H1),H1[0][0])
    rejects(lambda: require(determinant(*F1)==determinant(*H1)))
    print('FIVE_BORDERS',dict(counts),'CONTROLS FIRED: false rigidity, equal cofactors imply equal parents')
    print('ALL PASS')


if __name__=='__main__':
    main()
