#!/usr/bin/env python3
"""Staircase task coverage and formal family identities.

The finite box has gaps 1..2 and slacks in (1..2,1..3,1..2,1..3,1..5).
It is not an area census.  Every equality within this box is checked against
the corrected task cover; the unbounded conclusion uses the full matcher.
"""
from itertools import permutations,product,combinations
from collections import defaultdict,Counter
import sympy as sp
import staircase_matching as M
from jacobi_trudi import *
import formal_polynomial as formal


def stratum(rows,gaps):
    L=sum(rows[:4])-sum(gaps[:3]); R=sum(rows[1:])-sum(gaps[1:]); T=sum(rows[2:])-sum(gaps[2:])
    assert R>=L
    return 'S4' if R==L else 'S3' if L==T else 'S1' if L>T else 'S2'


def rev(p):
    return p[0][::-1],p[1][::-1]


def covered(F,H,exchange=True):
    if H in (F,rev(F)):
        return True
    choices={s[0]:s[3] for s in M.strata()}
    directions=((F,H),(H,F)) if exchange else ((F,H),)
    for first,second in directions:
        for f,hp in product((first,rev(first)),(second,rev(second))):
            rows,gaps=f
            if sum(rows[1:])-sum(gaps[1:])<sum(rows[:4])-sum(gaps[:3]):
                continue
            for rp,gp in choices[stratum(*f)]:
                if (tuple(rows[i] for i in rp),tuple(gaps[i] for i in gp))==hp:
                    return True
    return False


def main():
    support=[]
    for p in permutations(range(5)):
        if all(j>=i-1 for i,j in enumerate(p)):
            support.append(p)
    assert len(support)==16
    independent=[]
    for fixed_r,fixed_g in (((0,4),(0,3)),((0,1),(0,1)),((0,),(0,)),((0,),(0,))):
        choices=[]
        rf=[i for i in range(5) if i not in fixed_r]; gf=[i for i in range(4) if i not in fixed_g]
        for rr,gg in product(permutations(rf),permutations(gf)):
            rp=list(range(5)); gp=list(range(4))
            for i,j in zip(rf,rr): rp[i]=j
            for i,j in zip(gf,gg): gp[i]=j
            if rp!=list(range(5)) or gp!=list(range(4)):
                choices.append((tuple(rp),tuple(gp)))
        independent.append(choices)
    assert independent==[s[3] for s in M.strata()]
    assert sum(map(len,independent))==308
    # Direct coordinate differences, independently of the run-weight helper.
    G=(-1,0,0,0,1,1,0,0,-1,0)  # w2345 - w1234
    H=(1,1,0,0,-1,-1,-1,0,1,0)  # w1234 - w345
    assert [(s[1],s[2]) for s in M.strata()]==[
        ([G,H],[]),([G,tuple(-c for c in H)],[]),([G],[H]),([],[tuple(-c for c in G)])]
    units=[M.var(i) for i in range(9)]
    for choices in independent:
        for rp,gp in choices:
            rr=[units[i] for i in rp]; gg=[units[i+5] for i in gp]
            expected=list(gg)
            for i,r in enumerate(rr):
                expected.append(tuple(r[j]-(gg[i-1][j] if i else 0)-(gg[i][j] if i<4 else 0) for j in range(10)))
            assert M.domain(rr,gg)==expected
    # All twelve oriented family charts carry the precise primitive margins.
    chart_count=0
    for tag,template,npar in M.family_templates():
        p0,m0,z0,w0=units[:4]
        parameters=(p0,m0,z0) if npar==3 else (p0,m0,z0,w0)
        primitive=(z0,M.sub(p0,z0),M.sub(M.sub(m0,p0),z0)) if npar==3 else (z0,w0,M.sub(M.sub(p0,z0),w0),M.sub(M.sub(m0,z0),w0))
        if npar==3:
            replacements=(M.add(units[0],units[1]),M.add(M.add(units[0],units[0]),M.add(units[1],units[2])),units[0])
        else:
            replacements=(M.add(M.add(units[0],units[1]),units[2]),M.add(M.add(units[0],units[1]),units[3]),units[0],units[1])
        for rr,gg in template(*parameters):
            margins=M.domain(rr,gg)
            assert all(f in margins for f in primitive)
            for f in margins:
                transformed=tuple(sum(f[i]*replacements[i][j] for i in range(npar)) for j in range(10))
                assert any(transformed) and all(c>=0 for c in transformed) and transformed[-1]==0
            chart_count+=1
    assert chart_count==12 and len(M.family_forms_sym(units[:5],units[5:]))==12
    bf,bh,_,_=M.family_templates()[2][1](units[0],units[0],units[1],units[2])
    assert (bf[0][::-1],bf[1][::-1])==bh
    p,m,z,w=sp.symbols('p m z w')
    families=[(((p,m,m,m,m+p-z),(z,z,z,p)),((p,m,m+p-z,m,m),(z,p,z,z))),
              (((p,m,m,m+p-z,m+p-z),(z,z,p,p)),((p,m,m+p-z,m+p-z,m),(z,p,p,z))),
              (((p,m,p,p+m-w,m),(z,w,z,z)),((p,p+m-w,m,p,m),(z,z,w,z)))]
    negative={(i,j) for i in range(1,6) for j in range(1,6) if i-j>=2}
    for F,H in families:
        a=formal.determinant(*formal.profile_betas(*F),negative)
        b=formal.determinant(*formal.profile_betas(*H),negative)
        assert a and a==b
    buckets=defaultdict(list); counts=Counter()
    for gaps in product(range(1,3),repeat=4):
        for slack in product(range(1,3),range(1,4),range(1,3),range(1,4),range(1,6)):
            rows=tuple(slack[i]+(gaps[i-1] if i else 0)+(gaps[i] if i<4 else 0) for i in range(5))
            X,Y=from_profile(rows,gaps)
            P=determinant(X,Y)
            assert P==permutation_determinant(X,Y)==hessenberg(rows,gaps)
            assert negatives(X,Y)==negative
            assert coefficient(P,largest(P))==multiply(multiply(h(gaps[0]),h(gaps[1])),multiply(h(gaps[2]),h(gaps[3])))
            buckets[tuple(sorted(P.items()))].append((rows,gaps))
            counts['profiles']+=1
            if sum(rows[1:])-sum(gaps[1:])>=sum(rows[:4])-sum(gaps[:3]):
                s=stratum(rows,gaps); counts[s]+=1
                if s!='S4':
                    top=sorted({k for mon in P for k in mon},reverse=True)
                    coeff=coefficient(P,top[2])
                    assert coeff and sum(coeff.values())==(0 if s=='S2' else -1)
    for members in buckets.values():
        for F,H in combinations(members,2):
            assert covered(F,H)
            counts['equal_pairs']+=1
            if H!=rev(F): counts['nonrotation']+=1
    F=((2,4,4,4,5),(1,1,1,2)); H=((2,4,5,4,4),(1,2,1,1))
    assert stratum(*F)=='S1' and stratum(*H)=='S3'
    assert determinant(*from_profile(*F))==determinant(*from_profile(*H))
    assert covered(F,H) and not covered(F,H,exchange=False)
    rejects(lambda: require(stratum(*F)==stratum(*H)))
    rejects(lambda: require(covered(F,H,exchange=False)))
    F=((2,5,3,3,4),(1,1,1,1)); H=((2,3,3,4,5),(1,1,1,1))
    assert stratum(*F)=='S1' and stratum(*H)=='S2'
    rejects(lambda: require(hessenberg(*F)==hessenberg(*H)))
    for k in ('profiles','S1','S2','S3','S4','equal_pairs','nonrotation'):
        assert counts[k]>0,(k,counts)
    print('STAIRCASE',dict(counts),'CONTROLS FIRED: same stratum, no exchange, mixed S1/S2 equality')
    print('ALL PASS')


if __name__=='__main__':
    main()
