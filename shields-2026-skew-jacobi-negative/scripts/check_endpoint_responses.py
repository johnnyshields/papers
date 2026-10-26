#!/usr/bin/env python3
"""Endpoint response coefficients, including tied outer data and genuine units.

Five-row box: b,c,d=0..2, a=b+1..b+3, and each of
x-b-c, y-c-d, z-b-d is 1..2; shifts are 1 and 3.
Three explicit one-negative components include a four-row top tie with
unequal inner data and equal endpoint rows.
"""
from collections import Counter
from itertools import product
from jacobi_trudi import *


def response(Q,t):
    return add((1,determinant(*extend(*Q,t))),(-1,determinant(*extend(*Q,t,False))))


def main():
    counts=Counter()
    for b,c,d,slack,xx,yy,zz in product(range(3),range(3),range(3),range(1,4),range(1,3),range(1,3),range(1,3)):
        a=b+slack; x=b+c+xx; y=c+d+yy; z=b+d+zz
        Q=from_profile((a,x,y,z,a),(b,c,d,b)); q=a-b
        X=x+y-c; Y=y+z-d
        K=lambda s:add((1,multiply(h(a),h(s))),(-1,multiply(h(b),h(s+q))))
        for t in (1,3):
            actual=response(Q,t)
            L=max(X,Y)+q+t
            if X>Y:
                want=multiply(multiply(h(b),h(c)),K(z)); regime='X>Y'
            elif Y>X:
                want={m:-v for m,v in multiply(multiply(h(b),h(d)),K(x)).items()}; regime='Y>X'
            else:
                want=multiply(h(b),add((1,multiply(h(c),K(z))),(-1,multiply(h(d),K(x)))))
                regime='X=Y'
            assert coefficient(actual,L)==want
            assert bool(actual)==(Q!=rotation(*Q))
            if actual:
                assert want and largest(actual)==L
                counts[regime]+=1
            else:
                counts['symmetric']+=1
            counts['units' if b*c*d==0 else 'zero_free']+=1
    for Q in (((7,5,3),(4,1,0)),((10,9,8,4),(6,3,1,0)),((10,9,7,4),(6,3,1,0))):
        validate(*Q)
        assert len(negatives(*Q))==1 and not(set(Q[0])&set(Q[1]))
        kappa=max(Q[0][1],Q[0][0]-Q[1][-2])
        previous=None
        for t in (1,2,7):
            P=response(Q,t)
            assert bool(P)==(Q!=rotation(*Q))
            if P:
                C=coefficient(P,kappa+t)
                assert C and largest(P)==kappa+t
                if previous is not None: assert C==previous
                previous=C
        counts['one_negative']+=1
    assert all(counts[k]>0 for k in ('X>Y','Y>X','X=Y','symmetric','units','zero_free','one_negative'))
    Q=from_profile((2,3,4,5,2),(1,1,1,1))
    P=response(Q,1)
    assert P
    rejects(lambda: require(not P))
    rejects(lambda: require(coefficient(P,largest(P))=={}))
    print('ENDPOINT_RESPONSES',dict(counts),'CONTROLS FIRED: false symmetry, deleted leader')
    print('ALL PASS')


if __name__=='__main__':
    main()
