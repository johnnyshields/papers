"""Check the exhaustive four-row branches and the full one-return polynomial.

The core comes from a literal repeated profile followed by inflation and
common-beta deletion.  A constrained Leibniz expansion extracts an entire
polynomial coefficient, not only its minimum-square monomial.  No parameter
classifier, selected-coefficient checker or mate census is imported.
"""
from collections import Counter
from functools import lru_cache
from itertools import product, permutations
import sympy as sp


def lists(profile):
    rows, gaps = profile
    left = [0]
    for i, gap in enumerate(gaps):
        left.append(left[-1] + gap + 1 - rows[i + 1])
    y = tuple(a - i for i, a in enumerate(left))
    x = tuple(a + b for a, b in zip(y, rows))
    return tuple(a - y[-1] for a in x), tuple(a - y[-1] for a in y)


def near(p, q):
    r, g = p
    s, h = q
    return r[:-1] + (r[-1] + s[0],) + s[1:], g + h


def join(profiles):
    r, g = profiles[0]
    for s, h in profiles[1:]:
        r, g = r + s, g + (0,) + h
    return r, g


def determinant(x, y):
    result = Counter()
    for perm in permutations(range(len(x))):
        labels = [a - y[j] for a, j in zip(x, perm)]
        if min(labels, default=0) < 0:
            continue
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(len(x)) for j in range(i + 1, len(x)))
        result[tuple(sorted(a for a in labels if a))] += sign
    return tuple(sorted((mon, c) for mon, c in result.items() if c))


def scale(polynomial, coefficient):
    return tuple((mon, coefficient * c) for mon, c in polynomial)


def profile(a,b,c,e,f,p):
    return (a+p,a+b+e,b+c+f,c+p),(a,b,c)


def residual_data(pars):
    a,b,c,e,f,p = pars
    x,y = lists(profile(*pars))
    S = x[0]
    A,B = {q+p for q in x[2:]},set(y[:-2])
    J = A&B
    assert S == a+b+c+e+f+2*p
    assert A=={c+2*p,b+c+f+2*p}
    assert B=={c+f+p,b+c+e+f+p}
    assert J==({c+2*p} if f==p or b+e+f==p else set())|({b+c+f+2*p} if e==p else set())
    return S,p,A-J,B-J,J


def pairs(S,p,P,Q,d):
    return {(x,y) for x in {0,p}|P for y in {0,p}|Q if (x-y)%S==d}


def private(S,p,x,y):
    actual=pairs(S,p,{x},{y},x)=={(x,0)}
    failed=x==S-p or x+y==S or x+y==S+p
    assert actual == (not failed)
    return actual


def contact_ok(S,p,P,Q,J,pair):
    W={(x-y)%S for x in {0,p}|P for y in {0,p}|Q}
    assert all(0<r<S and r not in W for r in pair)
    key=tuple(sorted(pair))
    count=lambda Z:sum(tuple(sorted((z,S-z)))==key for z in Z)
    assert count(J)!=count({S+p-z for z in J})


def branch(pars):
    a,b,c,e,f,p=pars
    S,p,P,Q,J=residual_data(pars)
    if a==c and e==f:
        return 'symmetric'
    if e==f==p:
        assert not P and not Q
        return 'constant-excess'
    if not J:
        assert len(P)==len(Q)==2
        assert min(P)+max(Q)-(S+p)==c-a
        if a!=c:
            return 'direct'
        d=a+p
        expected={(p+d,p),(0,S-d)}
        if b==a:
            expected.add((2*a+f+2*p,a+f+p))
        assert pairs(S,p,P,Q,d)==expected
        if b!=a:
            A=P-{p+d}
            B=Q-{S-d}
            assert A=={a+b+f+2*p} and B=={a+f+p}
            assert min(A)-min(B)==b+p>0
            assert min(A)-(S+p-max(B))==f-e!=0
            return 'wrapped'
        assert e!=f and e!=p and f!=p and a+e+f!=p
        return 'one-return'
    assert len(P)==len(Q)==len(J)==1
    x,y=next(iter(P)),next(iter(Q))
    assert 2*p<x<S and p<y<S-p
    xx,yy=S+p-y,S+p-x
    if x+y!=S+p:
        if private(S,p,x,y) or private(S,p,xx,yy):
            return 'private'
        assert (x,y)==(S-p,3*p) or (xx,yy)==(S-p,3*p)
        assert S>4*p
        if e==p:
            assert S==5*p-f<5*p
        elif f==p:
            assert S==5*p-e<5*p
        else:
            assert b+e+f==p and S==b+5*p>5*p
        x,y=S-p,3*p
        d=S-4*p
        assert pairs(S,p,{x},{y},d)=={(x,y)}
        assert (S-2*p) not in {0,p,S-p}
        assert (x,S-y)!=(x-p,S+p-y)
        return 'restored'
    # Normalize the single terminal-contact branch by reflection.
    if f==p:
        a,c,e,f=c,a,f,e
        S,p,P,Q,J=residual_data((a,b,c,e,f,p))
    W={(x-y)%S for x in {0,p}|P for y in {0,p}|Q}
    if e==p:
        assert f!=p and c==a+b+p
        assert S==2*c+f+2*p and J=={S-a-p}
        assert W=={0,p,S-p,c+p,c+2*p,(p-f)%S}
        pair=(a+2*p,S-a-2*p) if f==a+2*p else (S-a-p,a+p)
        contact_ok(S,p,P,Q,J,pair)
        return 'contact-terminal'
    assert b+e+f==p and e<p and f<p
    assert a-c==f-e and S==a+c+3*p and J=={c+2*p}
    assert W=={0,p,S-p,c+3*p-e,c+2*p-e,b+p}
    if a!=b:
        contact_ok(S,p,P,Q,J,(c+2*p,a+p))
    else:
        assert c!=b
        contact_ok(S,p,P,Q,J,(a+2*p,c+p))
    return 'contact-cross'


def power(e,m):
    answer=e
    for _ in range(m-1):
        answer=near(answer,e)
    return answer


def core_from_cells(a,e,f,p,M,T):
    # Suffix cuts are translated to ordinary prefix cut positions.
    cuts=[0]+sorted(M-t for t in T)+[M]
    alpha=tuple(v-u for u,v in zip(cuts,cuts[1:]))
    inner=profile(a,a,a,e,f,p)
    parent=join(tuple(power(inner,m) for m in alpha))
    inflated=tuple(r+p for r in parent[0]),tuple(g+p for g in parent[1])
    X,Y=lists(inflated)
    common=set(X)&set(Y)
    return tuple(x for x in X if x not in common),tuple(y for y in Y if y not in common)


def extract(X,Y,targets):
    """Complete coefficient of the designated variables by Leibniz expansion."""
    labels=tuple(sorted(targets))
    indices={a:i for i,a in enumerate(labels)}
    goal=tuple(targets[a] for a in labels)
    n=len(X)
    @lru_cache(None)
    def rec(i,used,remaining):
        if sum(remaining)>n-i:
            return ()
        # Every designated variable needs an available matrix site.  This
        # upper bound only prunes; it never infers equality.
        for a,need in zip(labels,remaining):
            available=sum(any(not used>>j&1 and X[r]-y==a for j,y in enumerate(Y)) for r in range(i,n))
            if need>available:
                return ()
        if i==n:
            return (((),1),) if not any(remaining) else ()
        out=Counter()
        for j,y in enumerate(Y):
            if used>>j&1:
                continue
            a=X[i]-y
            if a<0:
                continue
            rem=list(remaining)
            if a in indices:
                k=indices[a]
                if rem[k]==0:
                    continue
                rem[k]-=1
                append=()
            else:
                append=(a,) if a else ()
            sign=(-1)**((used>>(j+1)).bit_count())
            for mon,c in rec(i+1,used|1<<j,tuple(rem)):
                out[tuple(sorted(mon+append))]+=sign*c
        return tuple(sorted((mon,c) for mon,c in out.items() if c))
    return rec(0,0,goal)


def full_coefficient(a,e,f,p,M,T):
    S=3*a+e+f+2*p
    assert e!=f and e!=p and f!=p and a+e+f!=p
    k=min(T-{M-t for t in T})
    K=set(range(1,M))-T
    d=a+p
    X,Y=core_from_cells(a,e,f,p,M,T)
    actual=[(i,j) for i,x in enumerate(X) for j,y in enumerate(Y) if x-y==d]
    N=M+2*(len(K)+1)
    assert len(actual)==N==len({i for i,j in actual})==len({j for i,j in actual})
    I,J={i for i,j in actual},{j for i,j in actual}
    L=tuple(x for i,x in enumerate(X) if i not in I)
    V=tuple(y for j,y in enumerate(Y) if j not in J)
    assert set(L)=={M*S+p}|{t*S+p+d for t in T}
    assert set(V)=={0}|{t*S-d for t in T}
    underlying=k*S+p+d
    site=[(i,j) for i,x in enumerate(L) for j,y in enumerate(V) if x-y==underlying]
    assert len(site)==1 and (L[site[0][0]],V[site[0][1]])==(underlying,0)
    i,j=site[0]
    cofactor=scale(determinant(L[:i]+L[i+1:],V[:j]+V[j+1:]),(-1)**(i+j))
    assert cofactor
    u,z=2*a+f+2*p,k*S+p-f
    W={p%S,(p+d)%S,(p+2*d)%S}
    assert u%S not in W|{0,d} and z%S not in W|{0,d}
    targets=Counter({d:N-1})
    targets[u]+=1
    targets[z]+=1
    value=extract(X,Y,targets)
    reflected=extract(*core_from_cells(a,f,e,p,M,T),targets)
    multiplicity=2 if f==a+e+p and k>1 else 1
    expected=scale(cofactor,multiplicity)
    assert value in (expected,scale(expected,-1)),(a,e,f,p,M,T,k,value,expected)
    assert not reflected
    if multiplicity==2:
        assert value not in (cofactor,scale(cofactor,-1))
    if u==z:
        assert k==1 and multiplicity==1
        assert value not in (scale(cofactor,2),scale(cofactor,-2))
    return multiplicity,u==z


def main():
    # Symbolic beta/contact equations independently simplify from the profile.
    a,b,c,e,f,p=sp.symbols('a b c e f p',positive=True)
    rr,gg=profile(a,b,c,e,f,p)
    left=[sp.Integer(0)]
    for i,g in enumerate(gg):
        left.append(left[-1]+g+1-rr[i+1])
    yy=tuple(v-i for i,v in enumerate(left))
    x=tuple(yy[i]+rr[i]-yy[-1] for i in range(4))
    assert sp.expand(x[0]-(a+b+c+e+f+2*p))==0
    A=(c+2*p,b+c+f+2*p)
    B=(c+f+p,b+c+e+f+p)
    assert [[sp.expand(q-r) for r in B] for q in A]==[[p-f,p-b-e-f],[b+p,p-e]]
    print('PASS symbolic contact matrix: the three stated contact equations are exhaustive.')
    counts=Counter(branch(pars) for pars in product((1,2,4,7),repeat=6))
    assert all(counts[k] for k in ('symmetric','constant-excess','direct','wrapped','one-return','private','restored','contact-terminal','contact-cross'))
    print('PASS range-stressing six-parameter branches:',dict(counts))
    samples=((1,2,3,1),(1,2,4,1),(2,3,6,1),(3,1,2,12),(2,7,3,4),(5,9,2,3))
    tests=((3,{1}),(3,{2}),(4,{1}),(4,{1,2}),(4,{2,3}),
           (5,{1,2}),(5,{1,3}),(5,{1,2,3}),(6,{1,2,4}),(6,{2,5}),(6,{1,2,3,4}))
    n=double=square=0
    for pars in samples:
        for M,T in tests:
            multiplicity,equal=full_coefficient(*pars,M,T)
            n+=1
            double+=multiplicity==2
            square+=equal
    assert double and square
    print('PASS',n,'entire one-return coefficient polynomials, not just one monomial;',double,'multiplicity-two and',square,'equal-label cases.')
    print('CONTROLS: replacing the resonance factor by one fails; doubling an equal-label return fails; reflected coefficients vanish.')
    # Exact determinant sign calibration in SymPy, separate from extraction.
    t,u,v=sp.symbols('t u v')
    assert sp.Matrix([[u,v],[t,u]]).det().expand()==u*u-t*v
    assert extract((5,3),(1,0),{4:1})==(((3,),1),)
    assert extract((5,3),(1,0),{5:1})==(((2,),-1),)
    print('ALL PASS')


if __name__=='__main__':
    main()
