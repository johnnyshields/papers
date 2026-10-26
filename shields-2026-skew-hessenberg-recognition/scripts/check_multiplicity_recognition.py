"""All-power multiplicity recognition: exact finite checks and firing control.

Nonzero finite-field evaluations reject equality only.  Every surviving equality
is compared as a full polynomial, by both interval and determinant routes.
"""
from collections import Counter
from hashlib import sha256
from math import gcd, prod
from verify_hessenberg import composite, interval, determinant, betas

PRIME=2**61-1


def unique_orders(rows):
    counts=Counter(rows); labels=sorted(counts); word=[]
    def go():
        if len(word)==len(rows):
            yield tuple(word)
            return
        for a in labels:
            if counts[a]:
                counts[a]-=1;word.append(a)
                yield from go()
                word.pop();counts[a]+=1
    yield from go()


def values(limit,seed):
    return [1]+[int.from_bytes(sha256(f'{seed}:{i}'.encode()).digest(),'big')%PRIME
                for i in range(1,limit+1)]


def evaluate(rows,c,h):
    n=len(rows);D=[1]
    for j in range(1,n+1):
        total=0;span=0;factor=1
        for i in range(j-1,-1,-1):
            span+=rows[i]-(c if i<j-1 else 0)
            total=(total+factor*h[span]*D[i])%PRIME
            factor=-factor*h[c]%PRIME
        D.append(total)
    return D[-1]


def condition(rows,c):
    a,b=rows[0],rows[-1];counts=Counter(rows[1:-1]);d=0
    for r,k in counts.items():
        if r not in {a,b,a+b-c,a+b}:
            d=gcd(d,k)
    if not d:
        return False
    q=d;z=counts[a+b]+1;p=2
    while p*p<=q:
        if q%p==0:
            if z%p:
                return False
            while q%p==0:q//=p
        p+=1
    return q==1 or z%q==0


def census(rows,c,m):
    r,g=composite(rows,(c,)*(len(rows)-1),(m,))
    h=values(sum(r),73);hh=values(sum(r),193)
    val=evaluate(r,c,h);val2=evaluate(r,c,hh)
    ref=interval(r,g);assert ref
    assert val==sum(coef*prod(h[a] for a in mon)
                    for mon,coef in ref.items())%PRIME
    assert determinant(*betas(r,g))==ref
    count=survivors=0;mates=[]
    for order in unique_orders(r):
        if any(order[i]<=2*c for i in range(1,len(order)-1)):
            continue
        count+=1
        if evaluate(order,c,h)!=val or evaluate(order,c,hh)!=val2:
            continue
        survivors+=1
        f=interval(order,g)
        if f==ref:
            assert determinant(*betas(order,g))==ref
            mates.append(order)
    return r,count,survivors,mates


def tests():
    rows,c=(3,4,3,6,5,4),1
    assert condition(rows,c)
    assert rows[0]+rows[-1]-c in rows[1:-1]
    assert (rows[-1],rows[0]) in tuple(zip(rows[1:-1],rows[2:-1]))
    for m in (1,2):
        r,n,survivors,mates=census(rows,c,m)
        assert set(mates)=={r,r[::-1]}
        print('PASS: multiplicity-only inner, power',m,'legal orders',n,
              'evaluation survivors',survivors,'exact mates',len(mates))
    for r in range(1,21):
        family=(3,)+(4,3,6)*r+(5,4)
        assert len(family)==3*r+3 and condition(family,1)
        assert 6 in family[1:-1] and (4,3) in tuple(zip(family[1:-1],family[2:-1]))
    print('PASS: 20 parameter checks of the unbounded-height multiplicity-only family.')
    # Rad(d) need not be one: the merger-label multiplicity matters.
    family=(3,4,3,6,5,5,7,4)
    assert condition(family,1)
    counts=Counter(family[1:-1]);assert counts[5]==2 and counts[7]+1==2
    for m in range(1,101):
        assert gcd(2*m,2*m-1)==1
    # This is the established nonrotation constant-gap pair; the new condition rejects it.
    bad=(3,4,3,6,4)
    assert not condition(bad,1)
    r,n,survivors,mates=census(bad,1,1)
    assert len(mates)>2
    print('PASS: rejected constant-gap control has',len(mates),'exact mates; '
          'the equality engine sees more than a rotation orbit.')
    print('ALL PASS')

if __name__=='__main__':
    tests()
