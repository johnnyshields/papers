"""Independent cell-set and exact polynomial checks for common-factor gluing.

No other script in this directory is imported, so the cell geometry shares no
code with the other checks.  Marks are searched from endpoint translations
and tested literally against I--IV.  Gcd inners are recovered only from the two
parent windows; the fold's prescribed mark and outer are then tested against
an independently searched legal chart.  Determinants are evaluated by signed
permutation enumeration in the elementary generators (dual Jacobi--Trudi).
"""
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from math import gcd
import argparse


def shift(S, v):
    return frozenset((i+v[0], j+v[1]) for i,j in S)


def norm(S):
    if not S:
        return frozenset()
    mi, mj = min(i for i,j in S), min(j for i,j in S)
    return shift(S, (-mi, -mj))


def rotate(S):
    return norm(frozenset((-i,-j) for i,j in S))


def transpose(S):
    return norm(frozenset((j,i) for i,j in S))


def at(S):
    return rotate(transpose(S))


def cells(lam, mu=()):
    return norm(frozenset((i,j) for i,r in enumerate(lam)
                         for j in range(mu[i] if i<len(mu) else 0, r)))


def endpoints(S):
    a=min(j-i for i,j in S); b=max(j-i for i,j in S)
    lo=[(i,j) for i,j in S if j-i==a]
    hi=[(i,j) for i,j in S if j-i==b]
    assert len(lo)==len(hi)==1, (S,lo,hi)
    return lo[0],hi[0]


def connected(S):
    if not S: return False
    todo=[next(iter(S))]; seen=set(todo)
    for i,j in todo:
        for q in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)):
            if q in S and q not in seen: seen.add(q); todo.append(q)
    return len(seen)==len(S)


def skew(S):
    if not connected(S): return False
    rows=sorted({i for i,j in S})
    if rows != list(range(rows[0],rows[-1]+1)): return False
    lr=[]
    for i in rows:
        js=sorted(j for k,j in S if k==i)
        if js!=list(range(js[0],js[-1]+1)): return False
        lr.append((js[0],js[-1]))
    return all(a[0]>=b[0] and a[1]>=b[1] for a,b in zip(lr,lr[1:]))


def span(S):
    return max(j-i for i,j in S)-min(j-i for i,j in S)+1 if S else 0


def diag(S):
    sw,_=endpoints(S)
    T=shift(S,(-sw[0],-sw[1]))
    N=span(T)
    return [(min(i for i,j in T if j-i==k),max(i for i,j in T if j-i==k)) for k in range(N)]


def bits(S):
    d=diag(S)
    return ([None]+[d[k-1][0]-d[k][0] for k in range(1,len(d))],
            [None]+[d[k-1][1]-d[k][1] for k in range(1,len(d))])


def from_bits(A,B):
    lo=hi=0; S={(0,0)}
    for k,(a,b) in enumerate(zip(A,B),1):
        if a not in (0,1) or b not in (0,1): return None
        lo-=a; hi-=b
        if hi<lo: return None
        S.update((i,i+k) for i in range(lo,hi+1))
    if hi!=lo: return None
    T=norm(S)
    return T if skew(T) else None


@dataclass(frozen=True)
class Mark:
    E: frozenset
    W: frozenset
    v: tuple
    case: str
    @property
    def p(self): return self.v[1]-self.v[0]
    @property
    def w(self): return span(self.W)


def rotate_mark(m):
    E0=frozenset((-i,-j) for i,j in m.E)
    W0=frozenset((-i,-j) for i,j in shift(m.W,m.v))
    v0=(-min(i for i,j in E0),-min(j for i,j in E0))
    return Mark(shift(E0,v0),shift(W0,v0),m.v,{'a':'a','b':'b','c':'d','d':'c'}[m.case])


def iv(E,W,v):
    O=E-W-shift(W,v)
    Oh={x for x in O if (x[0]+1,x[1]+1) in O}
    if not Oh:return True
    inf=frozenset().union(*(shift(E,(k*v[0],k*v[1])) for k in range(-3,4)))
    for k in range(-2,3):
        Wk=shift(W,(k*v[0],k*v[1]))
        Wh={x for x in inf if (x[0]+1,x[1]+1) in Wk} | {x for x in Wk if (x[0]+1,x[1]+1) in inf}
        if any((i+di,j+dj) in Oh for i,j in Wh for di,dj in ((1,0),(-1,0),(0,1),(0,-1))):return False
    return True


@lru_cache(maxsize=None)
def marks(E):
    return tuple(m for p in range(span(E)//2+1,span(E)+1) for m in marks_at(E,p))


@lru_cache(maxsize=2048)
def marks_at(E,period):
    assert skew(E)
    sw,ne=endpoints(E); N=span(E)
    if period==N:
        return (Mark(E,frozenset(),(ne[0]-sw[0],ne[1]-sw[1]+1),'a'),)
    out=[]
    for p in (period,):
        w=N-p; candidates=[]
        for y in E:
            if y[1]-y[0]-(sw[1]-sw[0])!=p:continue
            v=(y[0]-sw[0],y[1]-sw[1])
            W=E & shift(E,(-v[0],-v[1]))
            if sw not in W or ne not in shift(W,v) or span(W)!=w or not skew(W):continue
            candidates.append((W,v))
        for W,v in candidates:
            if any(W<W2 for W2,v2 in candidates):continue
            T=shift(W,v); O=E-W-T
            if not all(skew(S) for S in (E-W,E-T,O)):continue
            if not iv(E,W,v):continue
            x,y=endpoints(O)
            lows=[]; highs=[]
            if (x[0],x[1]-1) in W:lows.append('H')
            if (x[0]+1,x[1]) in W:lows.append('V')
            if (y[0],y[1]+1) in T:highs.append('H')
            if (y[0]-1,y[1]) in T:highs.append('V')
            for L,R in product(lows,highs):
                out.append(Mark(E,W,v,{('H','H'):'a',('V','V'):'b',('H','V'):'c',('V','H'):'d'}[L,R]))
    return tuple(out)


def compose(D,m):
    sw,_=endpoints(D); D=shift(D,(-sw[0],-sw[1]))
    intervals=diag(D)
    origins={}
    S=set()
    for i,j in D:
        t=j-i;lo,hi=intervals[t]
        z={'a':i,'b':-i,'c':i-lo,'d':i-hi}[m.case]
        v=(t*m.v[0]+z,t*m.v[1]+z)
        origins[i,j]=v
        S.update(shift(m.E,v))
    for i,j in D:
        if (i-1,j) not in D or m.case not in 'cd':continue
        t=j-i; lo,hi=intervals[t]; lo2,hi2=intervals[t+1]
        same=(i-lo==i-1-lo2) if m.case=='c' else (hi-i==hi2-(i-1))
        if same:
            o=origins[i,j];sgn=1 if m.case=='c' else -1
            S.update(shift(shift(m.W,m.v),(o[0]+sgn,o[1]+sgn)))
    R=norm(S)
    assert skew(R),(m,D,R)
    return R


def shapes(n):
    """All connected shapes with n cells, via compositions and adjacent overlap."""
    def comps(n):
        if not n: yield ();return
        for r in range(1,n+1):
            for tail in comps(n-r):yield (r,)+tail
    for rr in comps(n):
        for gg in product(*(range(1,min(a,b)+1) for a,b in zip(rr,rr[1:]))):
            left=[0]*len(rr)
            for i in range(len(rr)-2,-1,-1): left[i]=left[i+1]+rr[i+1]-gg[i]
            yield frozenset((i,j) for i,r in enumerate(rr) for j in range(left[i],left[i]+r))


def profile(S):
    T=norm(S); R=sorted({i for i,j in T});lr=[(min(j for k,j in T if k==i),max(j for k,j in T if k==i)) for i in R]
    return (tuple(b-a+1 for a,b in lr),tuple(min(b,d)-max(a,c) for (a,b),(c,d) in zip(lr,lr[1:])))


def dual_jt(S):
    """Full signed permutation expansion, pruning only zero matrix entries."""
    T=transpose(S); rows=sorted({i for i,j in T})
    lam=[max(j for k,j in T if k==i)+1 for i in rows]
    mu=[min(j for k,j in T if k==i) for i in rows]
    n=len(rows)
    @lru_cache(maxsize=None)
    def subdet(available):
        i=n-available.bit_count()
        if not available:return {():1}
        out=Counter();jj=0
        for j in range(n):
            if not available>>j&1:continue
            k=lam[i]-mu[j]-i+j
            sgn=-1 if jj%2 else 1;jj+=1
            if k<0:continue
            for tail,value in subdet(available^(1<<j)).items():
                out[tuple(sorted(tail+(k,))) if k else tail]+=sgn*value
        return {k:v for k,v in out.items() if v}
    return subdet((1<<n)-1)


def ordinary_jt(S):
    return dual_jt(transpose(S))


def mark(E,p,case):
    mm=[m for m in marks(E) if m.p==p and m.case==case]
    assert len(mm)==1,[(profile(m.E),m.p,m.w,m.case) for m in mm]
    return mm[0]


def root_inner(F,p):
    N=span(F); w=N%p
    if N//p<2 or w>=p:return None
    d=diag(F)
    if d[w][0]!=d[w][1] or d[N-p][0]!=d[N-p][1]:return None
    # Lower first-p window plus upper last-p window, aligning their pinches.
    sw,_=endpoints(F); T=shift(F,(-sw[0],-sw[1]))
    a={(i,j) for i,j in T if 0<=j-i<p}
    v=(d[N-p][0]-d[w][0],d[N-p][0]-d[w][0]+N-p-w)
    b=shift(frozenset((i,j) for i,j in T if N-p<=j-i<N),(-v[0],-v[1]))
    G=norm(a|b)
    return G if skew(G) and span(G)==p+w else None


def inverse(F,m):
    """Read private samples, solve both boundary steps, then recompose literally."""
    N=span(F);p=m.p;w=m.w
    if N%p!=w:return None
    r=N//p; d=diag(F); de=diag(m.E)
    if w:
        O=m.E-m.W-shift(m.W,m.v);c0=min(j-i for i,j in m.E)
        s=min(j-i for i,j in O)-c0;t=max(j-i for i,j in O)-c0-p+1
    else:t=s=0
    if m.case=='a':
        lo=[d[p*j+w][0]-j*m.v[0]-de[w][0] for j in range(r)]
        hi=[d[p*j+w][1]-j*m.v[0]-de[w][0] for j in range(r)]
        A=[lo[j-1]-lo[j] for j in range(1,r)];B=[hi[j-1]-hi[j] for j in range(1,r)]
    elif m.case=='b':
        lo=[j*m.v[0]+de[w][0]-d[p*j+w][1] for j in range(r)]
        hi=[j*m.v[0]+de[w][0]-d[p*j+w][0] for j in range(r)]
        A=[lo[j-1]-lo[j] for j in range(1,r)];B=[hi[j-1]-hi[j] for j in range(1,r)]
    else:
        # Recover M_j and S_j from diagonal cardinalities, not free-bit formulas.
        M=[d[p*j+w][1]-d[p*j+w][0]+1 for j in range(r)]
        h=lambda k:d[k][1]-d[k][0]+1
        if m.case=='d':
            z=t; c0=min(j-i for i,j in m.E)
            om=sum(j-i-c0==z for i,j in m.W)
            SS=[h(p*j+z)-om+1 for j in range(1,r)]
            A=[SS[j-1]-M[j-1] for j in range(1,r)];B=[SS[j-1]-M[j] for j in range(1,r)]
        else:
            Fr=rotate(F);mr=rotate_mark(m)
            Dr=inverse(Fr,mr)
            return rotate(Dr) if Dr is not None and compose(rotate(Dr),m)==F else None
    D=from_bits(A,B)
    return D if D is not None and len(D)>=2 and compose(D,m)==F else None


def roots_at(F,p):
    G=root_inner(F,p)
    if G is None or len(G)<2:return []
    rr=[]
    for m in marks_at(G,p):
        D=inverse(F,m)
        if D is not None:rr.append((D,m))
    return rr


def controls():
    H=cells((2,1));Hr=rotate(H); ss=list(shapes(3))
    cls=[S for S in ss if dual_jt(S)==dual_jt(H)]
    assert len(ss)==4 and set(cls)=={H,Hr}
    assert span(H)==3 and all(not roots_at(H,p) for p in range(2,span(H)//2+1))
    print('hook: 4 connected shapes; exactly 2 equal hooks; span excludes proper charts')
    E=cells((4,4,2),(2,));ma=mark(E,4,'a');mb=mark(E,4,'b')
    assert ma.W==frozenset({(1,0),(2,0)}) and mb.W==frozenset({(2,0),(2,1)})
    F=compose(cells((2,)),ma)
    assert F==compose(cells((1,1)),mb)
    assert dual_jt(cells((2,)))!=dual_jt(cells((1,1)))
    print('gauge: p=4,w=2; dual marks legal; same parent, unequal outer functions')
    R=cells((7,));r2=roots_at(R,2);r3=roots_at(R,3)
    assert r2 and r3 and gcd(2,3)==1
    print('row (7): legal proper period-2 and period-3 charts recovered independently')
    V=cells((4,1));om=mark(H,2,'d');mu=mark(V,4,'d')
    D=compose(H,mu);B=compose(V,om)
    Y=compose(D,om);X=compose(compose(H,rotate_mark(mu)),om)
    eta=mark(B,8,'d'); assert eta.W==frozenset({(4,0),(4,1),(5,0)})
    assert eta.v==(-4,4) and compose(H,eta)==Y
    fiber={compose(A,m) for A in cls for m in (eta,rotate_mark(eta))}
    assert len(fiber)==4 and X not in fiber
    assert len(X)==len(Y)==32 and span(X)==span(Y)==27 and X!=rotate(Y)
    f=dual_jt(X);ff=dual_jt(Y)
    assert f==ff and all(dual_jt(Z)==ff for Z in fiber)
    hx=ordinary_jt(X);hy=ordinary_jt(Y)
    assert hx==hy and len(hx)==1218
    assert profile(D)==((4,5,4,1),(0,1,0))
    assert profile(B)==((2,2,2,3,2,1),(0,0,0,1,0))
    print(f'coarse fiber: {len(fiber)} members excluding X; 32 cells, span 27; {len(hx)} h-terms; {len(f)} e-terms')
    print('ALL CONTROLS PASS')


def at_mark(m):
    E0=frozenset((-j,-i) for i,j in m.E)
    W0=frozenset((-j,-i) for i,j in m.W)
    v0=(-min(i for i,j in E0),-min(j for i,j in E0))
    return Mark(shift(E0,v0),shift(W0,v0),(-m.v[1],-m.v[0]),{'a':'b','b':'a','c':'d','d':'c'}[m.case])


def phases(m):
    if not m.W:return 0,0
    O=m.E-m.W-shift(m.W,m.v);c0=min(j-i for i,j in m.E)
    return max(j-i for i,j in O)-c0-m.p+1,min(j-i for i,j in O)-c0


def generic(F,m,n,g):
    A,B=bits(F);N=span(F)
    def holes(mm):
        t,s=phases(mm)
        return {'a':({t%mm.p},{s%mm.p}),'b':({s%mm.p},{t%mm.p}),
                'c':(set(),{t%mm.p,s%mm.p}),'d':({t%mm.p,s%mm.p},set())}[mm.case]
    hh,ii=holes(m),holes(n);out=[]
    for k,word in enumerate((A,B)):
        gg=[]
        for r in range(g):
            vals={word[j] for j in range(1,N) if j%g==r and not (j%m.p in hh[k] and j%n.p in ii[k])}
            assert len(vals)==1,('generic bits',m,n,r,k,vals)
            gg.append(next(iter(vals)))
        out.append(gg)
    return out


def prescribed_fold(F,m,n):
    if m.case in 'bc':
        F=at(F);m=at_mark(m);n=at_mark(n)
    assert m in marks_at(m.E,m.p) and n in marks_at(n.E,n.p)
    g=gcd(m.p,n.p);N=span(F);v=N%g
    assert g>1 and m.p% n.p and n.p%m.p
    if v<2:
        if v==1 and m.case=='a' and m.w>=2 and n.w>=2:
            A0,B0=generic(F,m,n,g)
            t,s=phases(m);e0=A0[0]-B0[0]
            assert (t,s,e0) in {(0,m.w,0),(1,m.w-1,1),(m.w-1,1,1)}, ('singleton table',m,n,t,s,e0)
        return (m.case,v,'small')
    A0,B0=generic(F,m,n,g);A,B=bits(F)
    assert sum(a-b for a,b in zip(A0,B0))==0
    d=diag(F)
    assert all(d[k][0]==d[k][1] for k in (v,g-1,N-g,N-v-1))
    G=root_inner(F,g);assert G is not None
    sw,_=endpoints(G);G0=shift(G,(-sw[0],-sw[1]))
    t,s=phases(m);tau=t%g;sigma=s%g
    if m.case=='a':
        assert n.case in 'ab'
        rho=A0[tau];assert rho==B0[sigma]
        typ='a' if rho or tau<sigma else 'b'
        W=set(x for x in G0 if 0<=x[1]-x[0]<v)
        T=set(x for x in G0 if g<=x[1]-x[0]<g+v)
        for r in range(v):
            ll=sorted(x for x in W if x[1]-x[0]==r)
            uu=sorted(x for x in T if x[1]-x[0]==g+r)
            if typ=='a':
                if r>=sigma:W.remove(ll[-1])
                if r<tau:T.remove(uu[0])
            else:
                if r>=tau:W.remove(ll[0])
                if r<sigma:T.remove(uu[-1])
        AA=[A[j*g+tau] if typ=='a' else 1-B[j*g+sigma] for j in range(1,N//g)]
        BB=[B[j*g+sigma] if typ=='a' else 1-A[j*g+tau] for j in range(1,N//g)]
        order='<' if tau<sigma else ('=' if tau==sigma else '>')
    else:
        assert m.case==n.case=='d'
        assert A0[tau]+A0[sigma]==1 and tau!=sigma
        z,o=(t,s) if A0[tau]==0 else (s,t)
        b=m.w//g;tau=z;sigma=o-b*g
        assert 0<=tau<=v and 0<=sigma<=v
        alpha,beta=sorted((tau,sigma));typ='d'
        W=set(x for x in G0 if 0<=x[1]-x[0]<v)
        T=set(x for x in G0 if g<=x[1]-x[0]<g+v)
        for r in range(v):
            ll=sorted(x for x in W if x[1]-x[0]==r)
            uu=sorted(x for x in T if x[1]-x[0]==g+r)
            if r>=beta:W.remove(ll[0])
            if r<alpha:T.remove(uu[0])
        AA=[A[j*g+alpha] for j in range(1,N//g)]
        BB=[1-A[j*g+beta] for j in range(1,N//g)]
        order='<' if tau<sigma else '>'
    assert skew(frozenset(W)) and skew(frozenset(T)) and norm(W)==norm(T)
    x,_=endpoints(frozenset(W));y,_=endpoints(frozenset(T));vv=(y[0]-x[0],y[1]-x[1])
    new=Mark(G,shift(frozenset(W),sw),vv,typ)
    assert new in marks_at(G,g),('fold illegal',profile(F),m,n,new)
    D=from_bits(AA,BB)
    assert D is not None and len(D)>1
    assert compose(D,new)==F,('fold does not recompose',profile(F),m,n,profile(D),new)
    return (m.case,v,order,typ,m.w//g==0,tau in (0,v),sigma in (0,v))


def sweep(max_inner):
    count=Counter();examples={}
    outers=[S for n in range(2,5) for S in shapes(n)]
    for n in range(2,max_inner+1):
        for G in shapes(n):
            for m in marks(G):
                for D in outers:
                    F=compose(D,m)
                    rr=roots_at(F,m.p)
                    assert any(mm==m and DD==D for DD,mm in rr),(profile(G),m,profile(D),rr)
                    count['supplied-chart reconstructions']+=1
                for R in (7,8,11,14,17):
                    D=cells((R,))
                    F=compose(D,m);N=span(F)
                    found={a:roots_at(F,a*m.p) for a in (2,3,4,5) if N//(a*m.p)>=2}
                    for a in found:
                        for c in found:
                            if a>=c or c%a==0 or gcd(a,c)>1:continue
                            for DD,mm in found[a]:
                                for CC,nn in found[c]:
                                    count['nondividing root pairs']+=1
                                    count[f'pair {mm.case}{nn.case}']+=1
                                    g=gcd(mm.p,nn.p);v=N%g
                                    count[f'fold remainder {v}']+=1
                                    assert roots_at(F,g),(profile(F),mm,nn,g)
                                    foldcase=prescribed_fold(F,mm,nn)
                                    count['prescribed fold checked']+=1
                                    count[f'fold details {foldcase}']+=1
                                    if mm.case in 'ab' and nn.case in 'ab':group='ordinary'
                                    elif mm.case==nn.case and mm.case in 'cd':group='mixed'
                                    else:raise AssertionError(('incompatible chart types',mm,nn))
                                    key=(group,v,g)
                                    examples.setdefault(key,(len(F),profile(G),m.p,m.w,R,a,c))
                    count['generated parents']+=1
        print('inner area',n,dict(count),flush=True)
    print('wide ordinary examples',[(k,v) for k,v in examples.items() if k[0]=='ordinary' and k[1]>=2][:8])
    print('wide mixed examples',[(k,v) for k,v in examples.items() if k[0]=='mixed' and k[1]>=2][:8])
    print('SWEEP PASS',dict(count),flush=True)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--controls',action='store_true');ap.add_argument('--sweep',type=int,default=0);args=ap.parse_args()
    if args.sweep:sweep(args.sweep)
    else:controls()


if __name__=='__main__':main()
