"""Literal whole-inner overlap charts, checked without a composition engine.

Case-(c) ribbon composition uses amalgamation at each path step and adds
one southeast translate of the mark at each north step.  The independent
comparison applies the linear empty-horizontal cell map to the small pair.
"""
from itertools import product
import sympy as sp
from check_r169_rev_h_o_proofs import valid, lists, near, join


def shift(cells, v):
    return frozenset((i+v[0],j+v[1]) for i,j in cells)


def norm(cells):
    return shift(cells,(-min(i for i,j in cells),-min(j for i,j in cells)))


def cells(p):
    r,g = p
    assert valid(p)
    left = [0]*len(r)
    for i in range(len(r)-2,-1,-1):
        left[i] = left[i+1]+r[i+1]-g[i]-1
    return frozenset((i,j) for i,a in enumerate(r) for j in range(left[i],left[i]+a))


def skew(c):
    if not c:
        return False
    rows = sorted({i for i,j in c})
    if rows != list(range(min(rows),max(rows)+1)):
        return False
    intervals = []
    for i in rows:
        js = {j for a,j in c if a==i}
        if len(js) != max(js)-min(js)+1:
            return False
        intervals.append((min(js),max(js)))
    return all(a>=c and b>=d and a<=d for (a,b),(c,d) in zip(intervals,intervals[1:]))


def content(c):
    return {j-i for i,j in c}


def adjacent(a,b):
    return any((i+di,j+dj) in b for i,j in a for di,dj in ((1,0),(-1,0),(0,1),(0,-1)))


def erosion(c):
    return frozenset((i,j) for i,j in c if (i+1,j+1) in c)


def literal_mixed(outer,e,mark,delta):
    ribbon = cells((outer,(0,)*(len(outer)-1)))
    path = sorted(ribbon,key=lambda q:q[1]-q[0])
    result = set(e)
    for k,(previous,current) in enumerate(zip(path,path[1:]),1):
        step = current[0]-previous[0],current[1]-previous[1]
        assert step in ((-1,0),(0,1))
        off = k*delta[0],k*delta[1]
        result.update(shift(e,off))
        if step==(-1,0):
            result.update(shift(mark,(off[0]+1,off[1]+1)))
    return norm(result)


def lift(p,r):
    root = cells(r)
    n,S = len(r[0]),lists(r)[0][0]
    v = 1-n,S-n+1
    u = v[0]-1,v[1]-1
    ans = set()
    for i,j in cells(p):
        ans.update(shift(root,(j*v[0]-i*u[0],j*v[1]-i*u[1])))
    return norm(ans)


def check_chart(r):
    root = cells(r)
    n,S = len(r[0]),lists(r)[0][0]
    v = 1-n,S-n+1
    u = v[0]-1,v[1]-1
    delta = v[0]+u[0],v[1]+u[1]
    middle,ne = shift(root,v),shift(root,delta)
    e = root|middle|ne
    assert norm(e) == norm(cells(join((r,near(r,r)))))
    assert len(e)==3*len(root)
    # I: the whole mark is the complete content-band restriction.
    for mark in (root,ne):
        assert frozenset(q for q in e if q[1]-q[0] in content(mark)) == mark
    assert min(content(ne))-max(content(root)) == S+1 >= 2
    assert skew(e-root) and skew(e-ne)
    # The southwest corner of the middle is horizontally attached; its
    # northeast corner is vertically attached.  Both are literal cells.
    sw = max(middle,key=lambda q:(q[0],-q[1]))
    northeast = min(middle,key=lambda q:(q[0],-q[1]))
    assert (sw[0],sw[1]-1) in root
    assert (northeast[0]-1,northeast[1]) in ne
    for piece in (root,middle,ne):
        lo,hi = min(content(piece)),max(content(piece))
        assert all(lo < j-i < hi for i,j in erosion(piece))
    # Exact central barred overlap in a chain.  Disjoint content bands
    # exclude contributions from every omitted translate, not just these.
    chain = frozenset().union(*(shift(e,(k*delta[0],k*delta[1])) for k in range(-2,3)))
    bar = frozenset(q for q in chain if (q[0]+1,q[1]+1) in root) | frozenset(
        q for q in root if (q[0]+1,q[1]+1) in chain)
    assert bar == erosion(root)
    for k in range(-2,3):
        assert not adjacent(bar,shift(erosion(middle),(k*delta[0],k*delta[1])))
    assert (v[0]-u[0],v[1]-u[1]) == (1,1)
    f = ((1,2,2,3),(0,0,1))
    h = ((1,2,3,2),(0,1,0))
    actual = {literal_mixed(alpha,e,root,delta) for alpha in ((2,1),(1,2))}
    assert actual == {lift(f,r),lift(h,r)}
    # A wrong diagonal supplement changes the actual cell union.
    alpha=(2,1)
    wrong = norm(e|shift(e,delta)|shift(e,(2*delta[0],2*delta[1]))|shift(root,(delta[0],delta[1]+1)))
    assert wrong != literal_mixed(alpha,e,root,delta)
    # Removing the middle band and using consecutive root copies fails II.
    assert min(content(middle))-max(content(root)) == 1


def main():
    count = 0
    for n in range(1,4):
        for r in product(range(1,5),repeat=n):
            for g in product(*(range(min(a,b)) for a,b in zip(r,r[1:]))):
                check_chart((r,g))
                count += 1
    for r in (((5,3,4,5),(2,2,3)),((4,4,4,4),(3,3,3))):
        check_chart(r)
        count += 1
    print('PASS',count,'connected-inner literal I-IV charts, including zero gaps and internal units.')
    print('PASS both ribbon reversals agree with independent affine cell substitution.')
    print('CONTROLS: wrong supplemental displacement changes the union; removing the separating band fails II.')
    h,w = sp.symbols('h w',integer=True,positive=True)
    c_area = (h-1)*w+2*w+(h-1)*(w+1)+2*w+(h-2)*w+2*w+(h-1)*w
    assert sp.expand(c_area-(4*h*w+h+w-1)) == 0
    assert sp.expand((h+(2*h-1)+(4*h-2))-(7*h-3)) == 0
    assert sp.expand(4*h*h-(2*h-1)*(2*h+1)) == 1
    # Exact zero-gap count leaves only the two forms used by the obstruction.
    cases=[]
    for M in range(2,20):
        for z in range(4):
            for length in range(1,M+1):
                if M*z+length-1==2:
                    assert (z==0 and length==3) or (M,z,length)==(2,1,1)
                    cases.append((M,z,length))
    assert (2,1,1) in cases and (3,0,3) in cases
    assert sp.isprime(31)
    print('PASS symbolic rectangular area/height identities, Bezout obstruction and zero-gap case split.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
