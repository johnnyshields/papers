"""Break attempts from boundary words, not from known common inner factors.

The parent is generated from equality constraints and cap bits for two chart
periods.  Connectedness and literal I--IV charts are tested only afterward.
Cell geometry comes from check_gcd_fold_sweep.py; the word generation itself
has no knowledge of a gcd root.  Each actual pair also checks the restriction
to its supplied inner, native completion, generic fold, and aligned lift.
"""
from collections import Counter
from itertools import product
from math import gcd
from check_gcd_fold_sweep import (from_bits,roots_at,phases,prescribed_fold,
                                 profile,span,Mark,marks_at,compose,cells)
from check_native_word_folds import check_native_restriction


def words(N,p,q,hp,hq,fixed):
    parent=list(range(N))
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]];x=parent[x]
        return x
    def join(x,y):
        x,y=find(x),find(y)
        if x!=y:parent[y]=x
    for d,holes in ((p,hp),(q,hq)):
        for i in range(1,N-d):
            if i%d not in holes:join(i,i+d)
    vals={}
    for pos,val in fixed:
        if pos in (0,N):continue
        assert 0<pos<N,(N,pos)
        r=find(pos)
        if r in vals and vals[r]!=val:return ()
        vals[r]=val
    rr=sorted({find(i) for i in range(1,N)})
    free=[r for r in rr if r not in vals]
    ans=[]
    for assignment in product((0,1),repeat=len(free)):
        vv=vals|dict(zip(free,assignment))
        ans.append(tuple(vv[find(i)] for i in range(1,N)))
    return tuple(ans)


def constraints(N,p,t,s,typ,k):
    w=N%p
    if typ=='a':
        return ({t%p},[(t,1),(N-w+t,0)]) if k==0 else ({s%p},[(s,0),(N-w+s,1)])
    if typ=='b':
        return ({s%p},[(s,1),(N-w+s,0)]) if k==0 else ({t%p},[(t,0),(N-w+t,1)])
    assert typ=='d'
    return ({t%p,s%p},[(t,1),(s,1),(N-w+t,0),(N-w+s,0)]) if k==0 else (set(),[(w,1),(p,0)])


def phase_choices(w,typ):
    return [(t,s) for t in range(w) for s in range(1,w+1) if typ!='d' or t<s]


def run():
    count=Counter();seen=set();details=Counter()
    # True EMPTY returns: the words are generated before either chart is found.
    for p,q,N in ((4,6,12),(4,6,24),(6,9,18)):
        candidate_words=words(N,p,q,{0},{0},[])
        for A,B in product(candidate_words,repeat=2):
            F=from_bits(A,B)
            if F is None:continue
            for D,m in roots_at(F,p):
                for C,n in roots_at(F,q):
                    assert m.w==n.w==0
                    check_native_restriction(F,m,n)
                    check_native_restriction(F,n,m)
                    count['EMPTY native restrictions and aligned lifts']+=2
    assert count['EMPTY native restrictions and aligned lifts']>0
    # Both ordinary readings, and mixed roots.  Chosen spans include more than
    # a least-common-multiple block, so free internal simultaneous holes occur.
    boxes=[(6,9,20),(6,9,23),(6,9,38),
           (8,12,26),(8,12,27),(8,12,43),
           (10,15,32),(10,15,34),(10,15,53),
           (15,25,52)]
    for p,q,N in boxes:
        w,u=N%p,N%q;g=gcd(p,q)
        assert N//p>=2 and N//q>=2 and w>=2 and u>=2
        for typ,typ2 in (('a','a'),('a','b'),('d','d')):
            for (t,s),(T,S) in product(phase_choices(w,typ),phase_choices(u,typ2)):
                h1,f1=constraints(N,p,t,s,typ,0);h2,f2=constraints(N,q,T,S,typ2,0)
                AW=words(N,p,q,h1,h2,f1+f2)
                h1,f1=constraints(N,p,t,s,typ,1);h2,f2=constraints(N,q,T,S,typ2,1)
                BW=words(N,p,q,h1,h2,f1+f2)
                count['phase pairs']+=1
                for A,B in product(AW,BW):
                    if sum(A)!=sum(B):continue
                    count['balanced word pairs']+=1
                    F=from_bits(A,B)
                    if F is None:continue
                    count['connected word pairs']+=1
                    sig=(F,p,q,typ,typ2,t,s,T,S)
                    if sig in seen:continue
                    seen.add(sig)
                    r1=[(D,m) for D,m in roots_at(F,p) if m.case==typ and phases(m)==(t,s)]
                    r2=[(C,n) for C,n in roots_at(F,q) if n.case==typ2 and phases(n)==(T,S)]
                    if not r1 or not r2:continue
                    for D,m in r1:
                        for C,n in r2:
                            check_native_restriction(F,m,n)
                            check_native_restriction(F,n,m)
                            count['native restrictions and aligned lifts']+=2
                            result=prescribed_fold(F,m,n)
                            assert roots_at(F,g)
                            count['actual nondividing chart pairs']+=1
                            details[result]+=1
                            count['maximum parent cells']=max(count['maximum parent cells'],len(F))
        print('box',p,q,N,dict(count),flush=True)
    assert count['actual nondividing chart pairs']>0
    assert any(k[1]>=2 for k in details)
    print('PRESCRIBED FOLD BRANCHES',dict(details))
    # Actual-control mutation: the parent boundary has not been assumed to
    # satisfy chart validity merely because it satisfies the punctured words.
    assert count['connected word pairs']>count['actual nondividing chart pairs']
    print('word-code-is-not-legality control fired')
    print('ALL PASS',dict(count))


if __name__=='__main__':run()
