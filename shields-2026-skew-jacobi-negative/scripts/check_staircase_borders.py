#!/usr/bin/env python3
"""Staircase family endpoints, critical tied coefficients, and larger borders.

M1/M2: d,t=0..1, a=t+d+i, b=a+j (i,j=1..2), both a/b orders.
M3/M4: d=0..1, a=1..2, b=a+d+j (j=1..2).  Tied margins include
q0-1,q0,q0+1 for each applicable q0, and b for M3/M4.
"""
from itertools import product
from collections import Counter
from jacobi_trudi import *


def main():
    cases=[]
    for kind in (1,2):
        for d,t,i,j in product(range(2),range(2),range(1,3),range(1,3)):
            a=t+d+i; b=a+j
            cases.extend(((kind,a,b,d,t),(kind,b,a,d,t)))
    for kind in (3,4):
        for d,a,j in product(range(2),range(1,3),range(1,3)):
            cases.append((kind,a,a+d+j,d,0))
    counts=Counter()
    for kind,a,b,d,t in cases:
        F,H=staircase_family(kind,a,b,d,t)
        assert determinant(*F)==determinant(*H)
        assert len({F,H,rotation(*F),rotation(*H)})==4
        rows=profile(*F)[0]
        multiplicities=tuple(Counter(rows)[r] for r in sorted(set(rows)))
        assert multiplicities==((2,2,1) if kind<=2 else (1,3,1) if kind==3 else (1,2,2))
        assert len(negatives(*F))==len(negatives(*H))==6
        for Q in (F,H):
            assert gamma(*Q)==staircase_family(kind,2*a,2*b,2*d+1,2*t)[(F,H).index(Q)]
        A=h(a+d); B=h(b+d)
        if kind==1:
            c=d+t; ell=a+b+d-t; kappa=2*a+2*b+d-2*t; sigma=t
        elif kind==2:
            c=d; ell=a+b+d; kappa=2*a+2*b+d-t; sigma=0
        else:
            c=d; ell=a+b+d; kappa=a+3*b+d; sigma=0
        C=h(c); K=add((1,multiply(C,h(ell))),(-1,multiply(A,B)))
        assert K
        for z in (1,2,5):
            top=add((1,determinant(*extend(*F,z))),(-1,determinant(*extend(*H,z))))
            expected=multiply(multiply(C,C),K) if kind<=2 else multiply(multiply(h(d),h(d)),K) if kind==3 else multiply(multiply(A,h(d)),K)
            if kind>=3: expected={m:-c for m,c in expected.items()}
            assert largest(top)==kappa+z and coefficient(top,kappa+z)==expected
            for ep,eh in product((True,False),repeat=2):
                assert determinant(*extend(*F,z,ep))!=determinant(*extend(*H,z,eh))
                counts['endpoint_comparisons']+=1
        q0=min(a,b)-sigma
        margins={1,2,b,q0,q0+1}
        if q0>1: margins.add(q0-1)
        for q in sorted(margins):
            up=add((1,determinant(*extend(*F,q))),(-1,determinant(*extend(*H,q))))
            down=add((1,determinant(*extend(*F,q,False))),(-1,determinant(*extend(*H,q,False))))
            E=add((1,up),(1,down))
            FB,HB=border(*F,q,q),border(*H,q,q)
            diff=add((1,determinant(*FB)),(-1,determinant(*HB)))
            assert diff and coefficient(diff,F[0][0]+q)==E
            if kind<=2:
                if q<q0:
                    expected=multiply(multiply(C,C),add((1,multiply(h(a+d+q),B)),(-1,multiply(A,h(b+d+q)))))
                    regime='below'
                elif q>q0:
                    expected=multiply(multiply(B if a>b else A,C),K)
                    if a>b: expected={m:-c for m,c in expected.items()}
                    regime='above'
                elif a>b:
                    expected=multiply(multiply(A,C),add((1,multiply(B,B)),(-1,multiply(C,h(2*b+d-sigma)))))
                    regime='critical'
                else:
                    expected=multiply(multiply(B,C),add((1,multiply(C,h(2*a+d-sigma))),(-1,multiply(A,A))))
                    regime='critical'
                L=max(kappa,kappa+q-q0)
                assert largest(E)==L and coefficient(E,L)==expected and expected
                counts[regime+('_a>b' if a>b else '_a<b')]+=1
            elif q==b:
                expected=multiply(multiply(A,h(d)),K) if kind==3 else multiply(multiply(A,A),K)
                expected={m:-c for m,c in expected.items()}
                assert largest(E)==4*b+d and coefficient(E,4*b+d)==expected
                counts['M'+str(kind)+'_critical']+=1
            counts['tied_borders']+=1
        for u,v in product((1,2),repeat=2):
            for Q,R in product((F,rotation(*F)),(H,rotation(*H))):
                for up,vp in {(u,v),(v,u)}:
                    assert determinant(*border(*Q,u,v))!=determinant(*border(*R,up,vp))
                    counts['oriented_borders']+=1
        counts['unit_family' if d==0 else 'thick_family']+=1
    # Connected cofactor induction and endpoint recurrence through eight rows.
    for base in (from_profile((3,4,5,4,3),(1,1,1,1)),from_profile((3,4,5,6,4),(1,1,1,1))):
        Q=base
        for n in range(6,9):
            Q=border(*Q,1,2)
            assert negatives(*Q)=={(i,j) for i in range(1,n+1) for j in range(1,n+1) if i-j>=n-3}
            for shift in (1,2):
                diff=add((1,determinant(*extend(*Q,shift))),(-1,determinant(*extend(*Q,shift,False))))
                assert bool(diff)==(Q!=rotation(*Q))
            counts['induction']+=1
    assert all(v>0 for v in counts.values())
    assert all(counts[k]>0 for k in ('below_a>b','below_a<b','above_a>b','above_a<b','critical_a>b','critical_a<b','M3_critical','M4_critical'))
    F,H=staircase_family(1,2,3,0,0)
    rejects(lambda: require(determinant(*F)!=determinant(*H)))
    rejects(lambda: require(determinant(*border(*F,1,1))==determinant(*border(*H,1,1))))
    print('STAIRCASE_BORDERS',dict(counts),'CONTROLS FIRED: reject genuine equality, equal borders')
    print('ALL PASS')


if __name__=='__main__':
    main()
