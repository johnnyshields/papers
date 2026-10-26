"""Independent checks of area cuts, span cases and primitive profile words.

This module uses cell-endpoint Jacobi--Trudi boards and full permutation
expansion.  It does not import the proposed classifiers or their checks.
Finite fibers corroborate the retained-end proof, not merger rigidity.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, permutations, product
import sympy as sp


def valid(p):
    r, g = p
    return bool(r) and len(g) == len(r)-1 and all(a > 0 for a in r) and all(
        0 <= a < min(r[i],r[i+1]) for i,a in enumerate(g))


def lists(p):
    r,g = p
    assert valid(p)
    left = [0]
    for i,a in enumerate(g):
        left.append(left[-1]+a+1-r[i+1])
    y = tuple(a-i for i,a in enumerate(left))
    x = tuple(a+b for a,b in zip(y,r))
    return tuple(a-y[-1] for a in x),tuple(a-y[-1] for a in y)


def free(p):
    x,y = lists(p)
    return not set(x)&set(y)


def near(p,q):
    r,g = p
    s,h = q
    return r[:-1]+(r[-1]+s[0],)+s[1:],g+h


def fold(ps):
    ans = ps[0]
    for p in ps[1:]:
        ans = near(ans,p)
    return ans


def join(ps):
    r,g = ps[0]
    for s,h in ps[1:]:
        r,g = r+s,g+(0,)+h
    return r,g


def rotate(p):
    return p[0][::-1],p[1][::-1]


def word(p):
    r,g = p
    ans = [None]*sum(r)
    at = 0
    for i,a in enumerate(r[:-1]):
        at += a
        ans[at-1] = g[i]
    return tuple(ans)


def decode(w):
    if not w or w[-1] is not None:
        return None
    prev,r,g = 0,[],[]
    for i,a in enumerate(w,1):
        if a is not None:
            r.append(i-prev)
            prev = i
            g.append(a)
    r.append(len(w)-prev)
    p = tuple(r),tuple(g)
    return p if valid(p) else None


def primitive(w):
    return next(w[:d] for d in range(1,len(w)+1)
                if len(w)%d == 0 and w == w[:d]*(len(w)//d))


@lru_cache(None)
def determinant(x,y):
    ans = Counter()
    for perm in permutations(range(len(x))):
        labels = [a-y[j] for a,j in zip(x,perm)]
        if min(labels,default=0)<0:
            continue
        sign = (-1)**sum(perm[i]>perm[j] for i in range(len(x)) for j in range(i+1,len(x)))
        ans[tuple(sorted(a for a in labels if a))] += sign
    return tuple(sorted((m,c) for m,c in ans.items() if c))


def poly(p):
    return determinant(*lists(p))


def add(*polys):
    ans = Counter()
    for p in polys:
        for m,c in p:
            ans[m] += c
    return tuple(sorted((m,c) for m,c in ans.items() if c))


def mul(p,q):
    ans = Counter()
    for m,c in p:
        for n,d in q:
            ans[tuple(sorted(m+n))] += c*d
    return tuple(sorted((m,c) for m,c in ans.items() if c))


def scale(p,c):
    return tuple((m,c*v) for m,v in p)


def coeff(p,j):
    return tuple((m[:m.index(j)]+m[m.index(j)+1:],c) for m,c in p if m.count(j)==1)


def middle(ps):
    a,b,c = ps
    return add(mul(poly(near(a,b)),poly(c)),mul(poly(a),poly(near(b,c))))


def cuts(p):
    w = word(p)
    for i,j in combinations(range(1,len(w)),2):
        ps = tuple(decode(v) for v in (w[:i],w[i:j],w[j:]))
        if all(q is not None and free(q) for q in ps):
            assert fold(ps) == p
            yield ps


def area_fibers():
    base = ((3,4),(2,))
    mergers = [fold((base,)*4), ((4,5,3),(2,1)), ((5,3,4,2),(2,2,1)),
               ((4,3,6,4),(2,2,3)), ((2,4,4),(1,2)), ((4,4),(3,))]
    counts = Counter()
    for merger in mergers:
        assert valid(merger) and free(merger), merger
        groups = defaultdict(list)
        for ps in cuts(merger):
            inventory = tuple(sorted(poly(p) for p in ps))
            groups[inventory,middle(ps)].append(ps)
            counts['cuts'] += 1
        for group in groups.values():
            assert len(group)<=2
            counts['fibers'] += 1
            for a,b in product(group,repeat=2):
                if sum(a[0][0])==sum(b[0][0]) or sum(a[-1][0])==sum(b[-1][0]):
                    assert a == b
                    counts['retained'] += 1
                if a != b:
                    counts['distinct_equal'] += 1
            # For a symmetric literal merger, every surviving triple is the
            # source or its reversal with each profile rotated.
            if merger == rotate(merger):
                a = group[0]
                assert all(b in (a,tuple(rotate(q) for q in a[::-1])) for b in group)
    assert counts['distinct_equal'] > 0
    # Extremes alone do not settle the middle component.
    ps = (base,base,fold((base,base)))
    qs = (base,fold((base,base)),base)
    assert fold(ps)==fold(qs)
    assert sorted(poly(p) for p in ps)==sorted(poly(p) for p in qs)
    assert middle(ps)!=middle(qs)
    print('PASS area-word fibers:',dict(counts))
    print('CONTROL: identical block inventory and literal merger do not force the collected middle sum.')


def span_cases():
    # The equal-span case has a row, a two-row strip, and a rectangle.
    cases = [(((2,),()),((3,),()),((4,),())),
             (((3,),()),((2,2),(1,)),((5,),())),
             (((4,),()),((2,3),(1,)),((3,3),(2,)))]
    for ps in cases:
        spans = [lists(p)[0][0] for p in ps]
        U = max(spans[i]+spans[j] for i in range(3) for j in range(i+1,3))
        cyclic = [ps,ps[1:]+ps[:1],ps[2:]+ps[:2]]
        readings = [tuple(sorted(coeff(middle(v),U))) for v in cyclic]
        assert len(set(readings))>1
        if len(set(spans)) == 1:
            assert len({sum(p[0]) for p in ps}) == 3
            assert len(set(readings)) == 3
    # Polynomial arithmetic in the equal-span irreducibility step.
    h,L1,L2,L3,R1,R2,R3 = sp.symbols('h L1 L2 L3 R1 R2 R3')
    f = [L1*h+R1,L2*h+R2,L3*h+R3]
    X = [f[0]*L2*L3,f[1]*L1*L3,f[2]*L1*L2]
    assert sp.expand((X[0]+X[1])-(X[1]+X[2])) == sp.expand(X[0]-X[2])
    assert sp.expand(f[0]*L2-f[1]*L1) == R1*L2-R2*L1
    print('PASS all three largest-pair-span cases, including distinct areas at one common span.')
    print('CONTROL: the three cyclic middle coefficients are not an invariant.')


def root_checks():
    count = 0
    for n in range(1,4):
        for r in product(range(1,5),repeat=n):
            for g in product(*(range(min(a,b)) for a,b in zip(r,r[1:]))):
                p = r,g
                w = word(p)
                root = primitive(w)
                q = decode(root)
                assert q is not None
                assert word(q)*(len(w)//len(root)) == w
                assert fold((q,)*(len(w)//len(root))) == p
                assert all(a is None for a in root) == (len(q[0])==1)
                if free(p):
                    assert free(q)
                if p == rotate(p):
                    assert q == rotate(q)
                count += 1
    # One non-Hessenberg root and a noncommuting control.
    p = ((7,4,6),(3,3))
    q = fold((p,)*2)
    assert free(p) and near(p,q) == near(q,p)
    assert decode(primitive(word(q))) == p
    r = ((7,5,6),(3,3))
    assert near(p,r) != near(r,p)
    m = sp.symbols('m',integer=True)
    assert sp.expand((16*m-1)-16*(m-1)) == 15
    # Multiplicity and total-size identities for abstract composition, not
    # a rerun of any particular power's equality census.
    def compose(a,b):
        ans = ()
        for v in a:
            q = b
            for _ in range(v-1):
                q = q[:-1]+(q[-1]+b[0],)+b[1:]
            ans += q
        return ans
    checked = 0
    for gamma in ((1,2),(2,2),(3,1),(1,1,2)):
        for eta in ((2,6,3),(2,6,6,3),(2,3,5,6,3)):
            composed = compose(gamma,eta)
            assert sum(composed) == sum(gamma)*sum(eta)
            assert composed.count(6) == sum(gamma)*eta.count(6)
            checked += 1
    print('PASS primitive roots of',count,'legal profile words;',checked,'abstract multiplicity identities; Euclidean remainder 15.')
    print('CONTROL: a perturbed noncommuting block fails word commutation.')


def family_and_forcing_controls():
    count = 0
    for m in range(1,7):
        ps = (((9,)+(6,)*m,(2,)*m),((4,5),(2,)),
              ((3,)+(6,)*(m+1),(2,)*(m+1)))
        merged = fold(ps)
        assert all(valid(p) and free(p) for p in ps)
        assert sum(ps[0][0]) == sum(ps[2][0]) == 9+6*m
        assert ps[0][0] != ps[2][0]
        assert merged[0].count(9)==1 and 9>2*max(merged[1])
        assert all(v%2==0 for v in merged[0][1:]+merged[1])
        assert len(join(ps)[0]) == 2*m+5
        assert 6+5-2==9 and join(ps)[0].count(join(ps)[0][-1])>1
        count += 1
    for t in range(2,8):
        ps = (((6,3),(2,)),((3,6,3),(2,2)),((3,)+(6,)*t,(2,)*t))
        merged=fold(ps)
        assert all(valid(p) and free(p) for p in ps)
        assert merged==((6,)*(t+4),(2,)*(t+3))
        assert merged==rotate(merged)
        assert 6+6-2 not in merged[0][1:-1]
        assert sum(ps[0][0]) != sum(ps[2][0])
        count += 1
    for t in range(1,8):
        ps = (((11,4),(2,)),((4,5),(2,)),
              ((9,6)+(10,)*(t-1)+(6,),(4,)*(t+1)))
        merged=fold(ps)
        assert all(valid(p) and free(p) for p in ps)
        assert merged[0].count(11)==1 and 11>2*max(merged[1])
        assert all(v%2==0 for v in merged[0][1:]+merged[1])
        assert 4 not in set(ps[0][1])|set(ps[1][1])
        assert len(join(ps)[0]) == t+6
        x,y=lists(ps[-1])
        assert set(x[i+2]-y[i] for i in range(len(x)-2)) <= {2,-2}
        assert all(x[i]-y[j]<0 for i in range(len(x)) for j in range(i-2))
        count += 1
    # A different commuting source verifies why the top coefficient alone
    # cannot certify the cyclic equality or the required cofactor component.
    root=((3,4),(2,))
    p=[None]+[fold((root,)*i) for i in range(1,6)]
    lhs=middle((p[1],p[2],p[3]))
    rhs=middle((p[2],p[3],p[1]))
    delta=add(lhs,scale(rhs,-1))
    S=lists(root)[0][0]
    assert not coeff(delta,5*S)
    witness=scale(mul(poly(p[2]),coeff(poly(p[4]),4*S)),-1)
    assert tuple(sorted(coeff(delta,4*S)))==tuple(sorted(witness)) and witness
    assert all(S not in mon for mon,c in coeff(poly(p[3]),3*S))
    print('PASS',count,'instances of the three unbounded rigidity suppliers.')
    print('CONTROL: a cyclic candidate passes the top collected coefficient and fails the next one.')


def sympy_calibration():
    for p in (((3,4),(2,)),((4,3,4),(2,2)),((2,3,2),(0,1))):
        x,y = lists(p)
        h = (sp.Integer(1),)+sp.symbols('h1:'+str(x[0]+1))
        matrix = sp.Matrix([[h[a-b] if a>=b else 0 for b in y] for a in x])
        expected = sum(c*sp.prod(h[j] for j in m) for m,c in poly(p))
        assert sp.expand(matrix.det()-expected) == 0
    print('PASS independent SymPy calibration of the full permutation determinant.')


def main():
    sympy_calibration()
    area_fibers()
    span_cases()
    root_checks()
    family_and_forcing_controls()
    print('ALL PASS')


if __name__ == '__main__':
    main()
