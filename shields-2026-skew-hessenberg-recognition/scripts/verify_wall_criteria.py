"""Independent exact site, deletion, matching, and wall coefficient checks."""
from collections import Counter
from functools import lru_cache
from verify_hessenberg import betas, composite, data, core, determinant, coefficient, sorted_diagonal


def sites(S,p,P,Q,c):
    return {(a,b) for a in {0,p}|set(P) for b in {0,p}|set(Q)
            if (a-b)%S==c}


def target(x,y,mon):
    labels=tuple(sorted(set(mon)))
    start=tuple(mon.count(a) for a in labels)
    @lru_cache(None)
    def go(mask,left):
        i=mask.bit_count()
        if i==len(x):
            return int(not any(left))
        total=0
        for j,b in enumerate(y):
            if mask>>j&1:
                continue
            d=x[i]-b
            if d<0 or (d>0 and d not in labels):
                continue
            rem=list(left)
            if d:
                k=labels.index(d)
                if rem[k]==0:
                    continue
                rem[k]-=1
            total+=(-1)**((mask>>(j+1)).bit_count())*go(mask|1<<j,tuple(rem))
        return total
    return go(0,start)


def wrapped_check(rows,gaps,maxM=8):
    S,p,P,Q,J=data(rows,gaps)
    c=min(P)-p
    assert c==S-max(Q)
    R={(a,b) for a in P for b in Q if a-b==c}
    assert sites(S,p,P,Q,c)=={(p+c,p),(0,S-c)}|R
    A=P-{p+c}-{a for a,b in R}; B=Q-{S-c}-{b for a,b in R}
    assert A and B
    sorted_diagonal(A,B)
    Ps={S+p-b for b in Q}; Qs={S+p-a for a in P}
    a,b=min(A),S+p-max(B)
    assert a!=b
    count=0
    for M in range(3,maxM+1):
        for mask in range(1<<(M-1)):
            K={i+1 for i in range(M-1) if mask>>i&1}
            for k in K-{M-j for j in K}:
                monos=[]
                for P0,Q0 in ((P,Q),(Ps,Qs)):
                    U,V=core(S,p,P0,Q0,M,K)
                    U=set(U)-{k*S}; V=set(V)-{0}
                    actual={(u,v) for u in U for v in V if u-v==c}
                    assert len(actual)==len(R)*M+2*len(K)+1
                    assert len({u for u,v in actual})==len(actual)
                    assert len({v for u,v in actual})==len(actual)
                    U-= {u for u,v in actual}; V-={v for u,v in actual}
                    monos.append(sorted_diagonal(U,V))
                delta=monos[0].copy(); delta.subtract(monos[1])
                expect=Counter([a+c,b]); expect.subtract([b+c,a])
                assert +delta==+expect and +(-delta)==+(-expect)
                count+=1
    return count


def tests():
    checks=wrapped_check((4,6,7,4),(3,1,3))
    # Core-only and full-parent extraction have different site tests.
    core_examples=[((3,4,7,3),(1,2,1),1,((6,9,3),(4,1))),
                   ((3,4,5,4,4),(1,1,1,2),3,((3,4,8,4),(1,1,2)))]
    identities=0
    for rows,gaps,c,(rr,gg) in core_examples:
        S,p,P,Q,J=data(rows,gaps); ss,pp,PP,QQ,JJ=data(rr,gg)
        R=sites(S,p,P,Q,c)
        assert all(a in P and b in Q and a-b==c for a,b in R)
        assert ss==S and pp==p and JJ==J
        assert PP==P-{a for a,b in R} and QQ==Q-{b for a,b in R}
        for M,K in [(1,set()),(2,{1}),(3,{1})]:
            U,V=core(S,p,P,Q,M,K)
            f=coefficient(determinant(U,V),c,len(R)*M)
            h=determinant(*core(S,p,PP,QQ,M,K))
            assert f==h or f=={m:-v for m,v in h.items()}
            identities+=1
    # Mixed deletion retains a private boundary coefficient, not a whole core.
    E=((2,7,7,3),(1,3,2)); EE=((2,11,3),(1,2))
    S,p,P,Q,J=data(*E);_,_,PP,QQ,JJ=data(*EE)
    assert sites(S,p,P,Q,4)=={(4,0),(9,5)}
    for M,K in ((1,set()),(2,{1})):
        f=coefficient(determinant(*core(S,p,P,Q,M,K)),4,M+1)
        h=coefficient(determinant(*core(S,p,PP,QQ,M,K)),4)
        assert f==h or f=={mon:-v for mon,v in h.items()}
        identities+=1
    # Full-parent deletion must test the contact residues as well.
    E=((3,3,5,4,3),(1,1,2,1));EE=((5,9,6),(3,4))
    S,p,P,Q,J=data(*E)
    assert sites(S,p,P|J,Q|J,1)=={(5,4),(11,10)}
    for alpha in ((1,),(1,1)):
        r,g=composite(*E,alpha);X,Y=betas(r,g)
        rr,gg=composite(*EE,alpha);XX,YY=betas(rr,gg)
        f=coefficient(determinant(tuple(x+p for x in X),Y),1,2*sum(alpha))
        h=determinant(tuple(x+p for x in XX),YY)
        assert f==h or f=={mon:-v for mon,v in h.items()}
        identities+=1
    # All four fixed selected-layer witnesses, in the full parents.
    witnesses=[
        ((2,4,5,6,2),(1,1,1,1),[2]*9+[8,18,27],(-2,0)),
        ((2,4,6,5,2),(1,1,1,1),[2]*9+[7,18,28],(-1,0)),
        ((2,5,5,6,5,2),(1,2,1,2,1),[2]*6+[3]*6+[11,21,30],(1,0)),
        ((2,5,6,7,5,2),(1,2,2,2,1),[2]*4+[3]*8+[12,22,32],(1,0)),
        ((3,3,3,4,4),(1,1,1,2),[1]*8+[4,9,24,34],(0,-1)),
        ((2,3,6,4),(1,1,3),[2,4,5,8,9,14,14],(1,0)),
        ((3,9,4),(1,2),[3,6,9,9,11,26],(1,0)),
        ((3,5,5),(1,3),[1,1,5,5,18,25],(0,-1)),
    ]
    for r,g,mon,expected in witnesses:
        p=r[0]-g[0]
        got=[]
        for alpha in ((1,2),(2,1)):
            rr,gg=composite(r,g,alpha)
            X,Y=betas(rr,gg)
            got.append(target(tuple(x+p for x in X),Y,mon))
        assert tuple(got)==expected,(r,g,got,expected)
        print('PARENT',r,g,tuple(got))
    # Negative control: disjoint wrapped sites can destroy every matching.
    r,g=(2,5,7,5,2),(1,1,2,1)
    S,p,P,Q,J=data(r,g); U,V=core(S,p,P,Q,3,{1})
    R={(a,b) for a in U for b in V if a-b==9}
    assert len(R)==4
    UU=sorted(set(U)-{a for a,b in R}); VV=sorted(set(V)-{b for a,b in R})
    assert any(a<=b for a,b in zip(UU,VV))
    print(f'PASS: {checks} wrapped-cofactor matching/ratio checks; '
          f'{identities} full-polynomial core/mixed/parent deletions; {len(witnesses)} exact parent witnesses; '
          'wrapped-matching negative control fires.')
    print('ALL PASS')

if __name__=='__main__':
    tests()
