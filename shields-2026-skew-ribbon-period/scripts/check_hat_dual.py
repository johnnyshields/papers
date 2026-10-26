r"""Paper section `app:coincident` (Positive coincident attachment phases).

Brute-force check of lem:hat-dual (app:coincident, 'The full-hat gauge and zero-offset descent').

For every connected skew diagram E of area <= N, every legal case-(a) marked inner (E, W, v),
conditions I-IV exactly as in SkewGluing/Mark.lean: when the full hat is connected skew with the
span of W, the data (E, hat + e, v - e, case (b)) is again legal.  Asserts no failure and that
the hypothesis is exercised.
"""
import itertools, sys
from functools import lru_cache
def content(x): return x[1]-x[0]
def tr(v,D): return frozenset((x[0]+v[0],x[1]+v[1]) for x in D)
def span(D): return len({content(x) for x in D})
def skew(D):
    for x in D:
        for y in D:
            if x[0]<=y[0] and x[1]<=y[1]:
                for i in range(x[0],y[0]+1):
                    for j in range(x[1],y[1]+1):
                        if (i,j) not in D: return False
    return True
def adj(x,y): return abs(x[0]-y[0])+abs(x[1]-y[1])==1
def conn(D):
    if not D: return False
    D=set(D); s=next(iter(D)); seen={s}; st=[s]
    while st:
        a=st.pop()
        for b in ((a[0]+1,a[1]),(a[0]-1,a[1]),(a[0],a[1]+1),(a[0],a[1]-1)):
            if b in D and b not in seen: seen.add(b); st.append(b)
    return len(seen)==len(D)
def cs(D): return skew(D) and conn(D)
def diaglo(D,k): return min(x[0] for x in D if content(x)==k)
def sw(D):
    k=min(map(content,D)); return (diaglo(D,k),diaglo(D,k)+k)
def ne(D):
    k=max(map(content,D)); return (diaglo(D,k),diaglo(D,k)+k)
e=(1,1)
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def sub(a,b): return (a[0]-b[0],a[1]-b[1])
class M:
    def __init__(s,E,W,v,c): s.E,s.W,s.v,s.c=E,W,v,c
    @property
    def up(s): return tr(s.v,s.W)
    @property
    def mid(s): return s.E-(s.W|s.up)
def lowerH(m):
    O=m.mid
    if not O: return False
    k=min(map(content,O)); return any(content(x)==k and (x[0],x[1]-1) in m.W for x in O)
def lowerV(m):
    O=m.mid
    if not O: return False
    k=min(map(content,O)); return any(content(x)==k and (x[0]+1,x[1]) in m.W for x in O)
def upperH(m):
    O=m.mid
    if not O: return False
    k=max(map(content,O)); return any(content(x)==k and (x[0],x[1]+1) in m.up for x in O)
def upperV(m):
    O=m.mid
    if not O: return False
    k=max(map(content,O)); return any(content(x)==k and (x[0]-1,x[1]) in m.up for x in O)
def attach(m):
    return {'a':lambda:lowerH(m) and upperH(m),'b':lambda:lowerV(m) and upperV(m),'c':lambda:lowerH(m) and upperV(m),'d':lambda:lowerV(m) and upperH(m)}[m.c]()
def nonempty(m):
    return m.W and cs(m.W) and m.W<=m.E and m.up<=m.E and sw(m.E) in m.W and ne(m.E) in m.up and attach(m)
def maximal(m):
    E=m.E
    rest=sorted(E-m.W)
    ck=frozenset(map(content,m.W))
    # W' strictly larger subset of E, skew, same contents
    for r in range(1,len(rest)+1):
        for sub_ in itertools.combinations(rest,r):
            Wp=m.W|frozenset(sub_)
            if not skew(Wp): continue
            if frozenset(map(content,Wp))!=ck: continue
            for x in Wp:
                if tr(sub(ne(E),x),Wp)<=E: return False
    return True
def narrow(m): return 0<=span(m.W)<content(m.v)
def removals(m): return cs(m.E-m.W) and cs(m.E-m.up)
def hatwindow(m):
    win=m.E|tr((-m.v[0],-m.v[1]),m.E)
    return frozenset([x for x in win if add(x,e) in m.W]+[x for x in m.W if add(x,e) in win])
def hatclear(m):
    hw=hatwindow(m)
    for k in (-1,0):
        Ok=tr((k*m.v[0],k*m.v[1]),m.mid)
        for x in Ok:
            if add(x,e) in Ok:
                for y in hw:
                    if adj(x,y): return False
    return True
def legal(m):
    return cs(m.E) and nonempty(m) and maximal(m) and narrow(m) and removals(m) and hatclear(m)
def cdiagrams(n):
    # connected skew diagrams area<=n, normalized, via growth
    res=set(); frontier={frozenset([(0,0)])}
    allD=set(frontier)
    for _ in range(n-1):
        new=set()
        for D in frontier:
            for x in D:
                for b in ((x[0]+1,x[1]),(x[0]-1,x[1]),(x[0],x[1]+1),(x[0],x[1]-1)):
                    if b not in D:
                        D2=D|{b}
                        mr=min(a[0] for a in D2); mc=min(a[1] for a in D2)
                        D2=tr((-mr,-mc),D2)
                        new.add(D2)
        frontier=new; allD|=new
    return [D for D in allD if skew(D)]
n=int(sys.argv[1]) if len(sys.argv)>1 else 9
cnt=hyp=bad=0
for E in cdiagrams(n):
    s0=sw(E); n0=ne(E); cells=sorted(E)
    for mask in range(1,1<<len(cells)):
        W=frozenset(c for i,c in enumerate(cells) if mask>>i&1)
        if not (s0 in W and cs(W)): continue
        for x in W:
            v=sub(n0,x); m=M(E,W,v,'a')
            if not (m.up<=E and attach(m) and legal(m)): continue
            cnt+=1
            H=hatwindow(m)
            if H and cs(H) and span(H)==span(W):
                hyp+=1
                bad+= not legal(M(E,tr(e,H),sub(v,e),'b'))
print("legal case a",cnt,"hat hypothesis",hyp,"failures",bad)
assert hyp>0 and bad==0
print("PASS")
