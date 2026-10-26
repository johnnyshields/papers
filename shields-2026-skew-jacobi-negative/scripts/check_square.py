#!/usr/bin/env python3
"""Square expansion and markers on blocks A,B,C,D=2..3, d,e=0..1.

Every u,v=1..3 and g=1..2 is tested.  Both unit and zero-free blocks,
equal and unequal factors, and all three margin regimes are populated.
"""
from itertools import product
from collections import Counter
from jacobi_trudi import *


def block(A,B,d):
    return (A+B-d,B),(B-d,0)


def main():
    counts=Counter()
    for A,B,C,D,d,e,u,v,g in product(range(2,4),range(2,4),range(2,4),range(2,4),range(2),range(2),range(1,4),range(1,4),range(1,3)):
        q=A+B-d; p=C+D-e; gamma=p+g; W=v+gamma
        X=(W+q+u,W+q,W+B,v+p,v+D)
        Y=(W+B-d,W,v+D-e,v,0)
        validate(X,Y)
        assert negatives(X,Y)=={(4,1),(4,2),(5,1),(5,2)}
        Q,R=block(A,B,d),block(C,D,e)
        fQ,fR=determinant(*Q),determinant(*R)
        sigma=determinant(*block(A+u,B,d))
        tau=determinant(*block(A+u,q,A))
        assert not add((1,multiply(h(A+u),fQ)),(-1,multiply(h(A),sigma)),(1,multiply(h(d),tau)))
        assert not add((1,multiply(h(q+u),fQ)),(-1,multiply(h(q),sigma)),(1,multiply(h(B),tau)))
        def phi(t):
            actual=determinant((q+u,q,B),(B-d,0,-t))
            formula=add((1,multiply(h(t+q+u),fQ)),(-1,multiply(h(t+q),sigma)),(1,multiply(h(t+B),tau)))
            assert actual==formula
            return actual
        expected=add((1,multiply(fR,phi(W))),
                     (-1,multiply(determinant(*block(C,D+v,e)),phi(gamma))),
                     (1,multiply(determinant(*block(p,D+v,D)),phi(gamma-(D-e)))))
        actual=determinant(X,Y)
        assert actual==expected==permutation_determinant(X,Y)
        N=X[0]; M=N-min(u,v)
        assert coefficient(actual,N)==multiply(fQ,fR)
        top=multiply(sigma,fR)
        bottom=multiply(fQ,determinant(*block(C,D+v,e)))
        want=top if u<v else bottom if v<u else add((1,top),(1,bottom))
        assert coefficient(actual,M)=={m:-c for m,c in want.items()}
        counts['top' if u<v else 'bottom' if v<u else 'tie']+=1
        counts['equal_factors' if fQ==fR else 'unequal_factors']+=1
        counts['units' if d==0 or e==0 else 'zero_free']+=1
    assert all(v>0 for v in counts.values())
    rejects(lambda: require(determinant(*block(3,2,1))==determinant(*block(4,2,1))))
    print('SQUARE',dict(counts),'CONTROL FIRED: false endpoint equality')
    print('ALL PASS')


if __name__=='__main__':
    main()
