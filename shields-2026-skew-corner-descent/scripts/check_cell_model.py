"""Independent cell-set checks of corner transport and legal-mark counts.

Shapes are grown as connected skew lattice animals. Marks are enumerated as
all southwest subsets and tested against the literal I--IV conditions, without
using the local thin-tail lemma to decide legality. Schur polynomials use
Jacobi--Trudi subset expansion; a separate dual determinant is used on witnesses.
No other verification module in this directory is imported.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import argparse
import sympy as sp


def shift(s, v):
    return frozenset((i + v[0], j + v[1]) for i, j in s)


def normal(s):
    if not s:
        return frozenset()
    bottom = max(i for i, j in s)
    left = min(j for i, j in s)
    return shift(s, (-bottom, -left))


def cont(x):
    return x[1] - x[0]


def width(s):
    return len({cont(x) for x in s})


def neighbors(x):
    i, j = x
    return ((i + 1, j), (i - 1, j), (i, j + 1), (i, j - 1))


def skew(s, connected=False):
    if not s:
        return not connected
    rows = sorted({i for i, j in s})
    bounds = []
    for i in rows:
        js = sorted(j for a, j in s if a == i)
        if js != list(range(js[0], js[-1] + 1)):
            return False
        bounds.append((js[0], js[-1]))
    if any(a[0] < b[0] or a[1] < b[1] for a, b in zip(bounds, bounds[1:])):
        return False
    if connected:
        seen, todo = set(), [next(iter(s))]
        while todo:
            x = todo.pop()
            if x in seen:
                continue
            seen.add(x)
            todo.extend(y for y in neighbors(x) if y in s and y not in seen)
        return len(seen) == len(s)
    return True


@lru_cache(None)
def shapes(n):
    if n == 1:
        return (frozenset({(0, 0)}),)
    ans = set()
    for s in shapes(n - 1):
        for x in {y for a in s for y in neighbors(a)} - s:
            t = normal(s | {x})
            if skew(t, True):
                ans.add(t)
    return tuple(sorted(ans, key=lambda s: tuple(sorted(s))))


def compositions(n):
    if n == 0:
        yield ()
    else:
        for a in range(1, n + 1):
            for tail in compositions(n - a):
                yield (a,) + tail


def profile_shape(rows, overlaps):
    left = [0] * len(rows)
    for i in range(len(rows) - 2, -1, -1):
        left[i] = left[i + 1] + rows[i + 1] - overlaps[i]
    return normal(frozenset((i, j) for i, r in enumerate(rows) for j in range(left[i], left[i] + r)))


def profile_shapes(n):
    ans = set()
    for rows in compositions(n):
        for ov in product(*(range(1, min(a, b) + 1) for a, b in zip(rows, rows[1:]))):
            ans.add(profile_shape(rows, ov))
    return ans


def interior(s):
    return frozenset(x for x in s if (x[0] + 1, x[1] + 1) in s)


def components(s):
    remaining, ans = set(s), []
    while remaining:
        todo, block = [next(iter(remaining))], set()
        while todo:
            x = todo.pop()
            if x not in remaining:
                continue
            remaining.remove(x)
            block.add(x)
            todo.extend(neighbors(x))
        ans.append(frozenset(block))
    return ans


def adjacent(a, b):
    return any(y in b for x in a for y in neighbors(x))


def extrema(s):
    return min(s, key=cont), max(s, key=cont)


def candidates(s, w):
    """All end-copy pairs of width w, before maximality or complement tests."""
    low = sorted(x for x in s if cont(x) < w)
    southwest, northeast = extrema(s)
    for k in range(1, len(low) + 1):
        for xs in combinations(low, k):
            lo = frozenset(xs)
            if southwest not in lo or width(lo) != w or not skew(lo, True):
                continue
            _, tip = extrema(lo)
            v = (northeast[0] - tip[0], northeast[1] - tip[1])
            hi = shift(lo, v)
            if hi <= s:
                yield lo, hi, v


def marks(s):
    """Yield (lower mark, displacement, attachment case), plus both empty edges."""
    _, ne = extrema(s)
    vh = (ne[0], ne[1] + 1)
    yield frozenset(), vh, 'a'
    yield frozenset(), (vh[0] - 1, vh[1] - 1), 'b'
    N = width(s)
    for w in range(1, (N - 1) // 2 + 1):
        options = list(candidates(s, w))
        for lo, hi, v in options:
            if any(lo < other for other, _, _ in options):
                continue
            if not skew(s - lo, True) or not skew(s - hi, True):
                continue
            O = s - lo - hi
            # Do not add an unrecorded legality filter: both connected skew
            # one-mark complements must already force a connected skew middle.
            assert skew(O, True), ('complement intersection',s,lo,hi)
            strip = frozenset().union(*(shift(s, (k * v[0], k * v[1])) for k in range(-2, 3)))
            hatW = frozenset(x for x in strip if (x[0] + 1, x[1] + 1) in lo) | frozenset(x for x in lo if (x[0] + 1, x[1] + 1) in strip)
            hatO = interior(O)
            if any(adjacent(hatO, shift(hatW, (k * v[0], k * v[1]))) for k in range(-2, 3)):
                continue
            swO, neO = extrema(O)
            lowers = [('H', (swO[0], swO[1] - 1)), ('V', (swO[0] + 1, swO[1]))]
            uppers = [('H', (neO[0], neO[1] + 1)), ('V', (neO[0] - 1, neO[1]))]
            for a, x in lowers:
                for b, y in uppers:
                    if x in lo and y in hi:
                        case = {('H', 'H'): 'a', ('V', 'V'): 'b', ('H', 'V'): 'c', ('V', 'H'): 'd'}[a, b]
                        yield lo, v, case


def mark_data(s, mark):
    W, v, case = mark
    w, p = width(W), cont(v)
    upper = shift(W, v)
    O = s - W - upper
    strip = frozenset().union(*(shift(s, (k * v[0], k * v[1])) for k in range(-2, 3)))
    hatW = frozenset(x for x in strip if (x[0] + 1, x[1] + 1) in W) | frozenset(x for x in W if (x[0] + 1, x[1] + 1) in strip)
    caps = (frozenset(x for x in interior(s) if cont(x) < w), frozenset(x for x in interior(s) if cont(x) >= p))
    return W, O, hatW, interior(O), caps, p, w


def v_failure(s, mark):
    W, v, case = mark
    if not W or case not in 'ab':
        return False
    O = s - W - shift(W, v)
    return all(sum(any(y in O for y in neighbors(x)) for x in end) > 1 for end in (W, shift(W, v)))


def compose(d, s, mark):
    W, v, case = mark
    intervals = {t: (min(i for i, j in d if cont((i, j)) == t), max(i for i, j in d if cont((i, j)) == t)) for t in {cont(x) for x in d}}
    origins = {}
    for x in d:
        i, j = x
        t = cont(x)
        lo, hi = intervals[t]
        a = {'a': i, 'b': -i, 'c': i - lo, 'd': i - hi}[case]
        origins[x] = (t * v[0] + a, t * v[1] + a)
    parent = set().union(*(shift(s, u) for u in origins.values()))
    # Peel literal northwest/southeast ribbons rather than derive their ranks.
    if case in 'cd':
        remaining = set(d)
        ribbons = []
        while remaining:
            step = (-1, -1) if case == 'c' else (1, 1)
            ribbon = {x for x in remaining if (x[0] + step[0], x[1] + step[1]) not in remaining}
            ribbons.append(ribbon)
            remaining -= ribbon
        for ribbon in ribbons:
            for i, j in ribbon:
                if (i - 1, j) in ribbon:
                    a = 1 if case == 'c' else -1
                    u = origins[i, j]
                    parent.update(shift(W, (u[0] + v[0] + a, u[1] + v[1] + a)))
    parent = frozenset(parent)
    assert skew(parent, True), (d, s, mark, parent)
    return normal(parent)


def h(k):
    return sp.Integer(0) if k < 0 else sp.Integer(1) if k == 0 else sp.Symbol('h' + str(k))


def determinant_entries(lam, mu):
    n = len(lam)
    # Each state enumerates signed partial permutations, not elimination.
    dp = {0: sp.Integer(1)}
    for i in range(n):
        nd = {}
        for mask, P in dp.items():
            for j in range(n):
                if mask >> j & 1:
                    continue
                a = lam[i] - mu[j] - i + j
                if a < 0:
                    continue
                inversions = (mask >> (j + 1)).bit_count()
                m = mask | (1 << j)
                nd[m] = nd.get(m, sp.Integer(0)) + (-1) ** inversions * P * h(a)
        dp = nd
    return sp.expand(dp.get((1 << n) - 1, sp.Integer(0)))


@lru_cache(None)
def schur(s):
    if not s:
        return sp.Integer(1)
    s = normal(s)
    comps = components(s)
    if len(comps) > 1:
        return sp.expand(sp.prod(schur(normal(c)) for c in comps))
    rows = sorted({i for i, j in s})
    lam = [max(j for a, j in s if a == i) + 1 for i in rows]
    mu = [min(j for a, j in s if a == i) for i in rows]
    return determinant_entries(lam, mu)


def polynomial_span(P):
    return max((int(str(v)[1:]) for v in sp.expand(P).free_symbols), default=0)


def kappa(s):
    return sp.expand(schur(s)).coeff(h(width(s))) * (-1) ** (len({i for i, j in s}) - 1)


def census(maxarea):
    totals = Counter()
    failures = []
    for n in range(1, maxarea + 1):
        grown = set(shapes(n))
        direct = profile_shapes(n)
        assert grown == direct, (n, len(grown), len(direct))
        if n == 1:
            continue
        totals['shapes'] += len(grown)
        for s in grown:
            for mark in marks(s):
                W, O, hatW, hatO, caps, p, w = mark_data(s, mark)
                case = mark[-1]
                totals['empty' if not W else 'ordinary' if case in 'ab' else 'mixed'] += 1
                if v_failure(s, mark):
                    totals['fails V'] += 1
                    totals['fails V ' + case] += 1
                    failures.append((s, mark))
                # Independent checks of all local facts used in the row proof.
                if W:
                    v = mark[1]
                    assert W == s & shift(s, (-v[0], -v[1]))
                    assert all(sum(cont(x) == t for x in O) <= 1 for t in list(range(w)) + list(range(p, p + w)))
                    assert all(sum(cont(x) == t for x in s) == 1 for t in (w, p - 1))
                    assert hatW == caps[0] | shift(caps[1], (-v[0], -v[1]))
                assert interior(s) == caps[0] | hatO | caps[1]
                for part, bound in zip((caps[0], caps[1], hatW, hatO), (max(0, w-1), max(0, w-1), w, max(0, p-w-2))):
                    assert skew(part), (s,mark,part)
                    assert all(width(c) <= bound for c in components(part)), (s, mark, part, bound)
                totals['local-geometry checks'] += 1
                # Test the decomposition itself, before any Schur evaluation.
                v = mark[1]
                for m in range(1, 5):
                    row_parent = frozenset().union(*(shift(s, (j*v[0], j*v[1])) for j in range(m)))
                    pieces = [caps[0], shift(caps[1], ((m-1)*v[0], (m-1)*v[1]))]
                    pieces += [shift(hatO, (j*v[0], j*v[1])) for j in range(m)]
                    pieces += [shift(hatW, (j*v[0], j*v[1])) for j in range(1, m)]
                    assert interior(row_parent) == frozenset().union(*pieces)
                    assert all(not (a & b) and not adjacent(a,b) for a,b in combinations(pieces,2))
                    totals['literal row decompositions'] += 1
        print('area', n, 'shapes', len(grown), 'cumulative', dict(totals), flush=True)
    return totals, failures


def witness():
    s = profile_shape((2, 4, 2), (2, 2))
    mark = (frozenset({(-1, 0), (0, 0)}), (-1, 3), 'a')
    assert mark in tuple(marks(s)) and v_failure(s, mark)
    W, O, hatW, hatO, caps, p, w = mark_data(s, mark)
    A, B, C = map(schur, (W, hatW, hatO))
    theta = sp.expand(schur(caps[0]) * schur(caps[1]))
    assert (p, w) == (4, 2)
    assert (A, B, C, theta) == (h(1)**2 - h(2), h(2), 1, h(1)**2)
    # Dual Jacobi--Trudi, using e_k recovered from H(t)E(-t)=1.
    elementary = [sp.Integer(1)]
    for k in range(1, 9):
        elementary.append(sp.expand(sum((-1)**(j-1)*h(j)*elementary[k-j] for j in range(1, k+1))))
    lamt, mut = (3,3,2,2), (1,1,0,0)
    dual = sp.expand(sp.Matrix(4,4,lambda i,j: 0 if lamt[i]-mut[j]-i+j < 0 else elementary[lamt[i]-mut[j]-i+j]).det(method='domain-ge'))
    assert sp.expand(dual - schur(s)) == 0
    assert sp.expand(dual).coeff(h(6)) == theta
    print('witness A,B,C,Theta:', A, B, C, theta, '; spans', tuple(polynomial_span(P) for P in (A,B,C,theta)), flush=True)
    for k in range(3,17):
        E = profile_shape((2,k,2),(2,2))
        lo, v = frozenset({(-1,0),(0,0)}), (-1,k-1)
        options = tuple(candidates(E,2))
        assert (lo,shift(lo,v),v) in options
        assert not any(lo < bigger for bigger,_,_ in options)
        assert skew(E-lo,True) and skew(E-shift(lo,v),True)
        mark_k = (lo,v,'a')
        W,O,Bhat,Chat,K,p,w = mark_data(E,mark_k)
        assert not Chat and v_failure(E,mark_k)
        assert Bhat == frozenset({(-1,-1),(-1,0)})
        expected = h(2)**2*h(k)-2*h(1)*h(2)*h(k+1)+h(1)**2*h(k+2)
        assert sp.expand(schur(E)-expected)==0
    print('non-V family independently checked: k=3..16',flush=True)


@lru_cache(None)
def prime_list(P):
    return tuple(sp.factor_list(P)[1])


@lru_cache(None)
def multiplicity(P, Q):
    variables = sorted(P.free_symbols | Q.free_symbols, key=str)
    p, q = sp.Poly(P, *variables), sp.Poly(Q, *variables)
    exponent = 0
    while True:
        quotient, remainder = p.div(q)
        if not remainder.is_zero:
            return exponent
        exponent += 1
        p = quotient


def empty_boundary(maxarea=9):
    maxima = {}
    by_period = Counter()
    for n in range(2, maxarea+1):
        for E in shapes(n):
            p = width(E)
            C = schur(normal(interior(E)))
            attained = polynomial_span(C)
            assert attained <= max(0,p-2)
            maxima[p] = max(maxima.get(p,0), attained)
            by_period[p] += 2
    print('empty-reading maxima (p, attained, bound, readings):',
          [(p,maxima[p],max(0,p-2),by_period[p]) for p in sorted(maxima)], flush=True)
    # A two-row rectangle attains p-2 for each p>=3, independent of a size box.
    for p in range(2,13):
        E = profile_shape((p-1,p-1),(p-1,))
        assert width(E) == p
        C = schur(normal(interior(E)))
        assert C == h(p-2)
        assert polynomial_span(C)==max(0,p-2)
    print('empty-reading sharp family: two-row rectangles, p=2..12; attained p-2; child margin 2', flush=True)


def transport(maxinner=5, maxouter=7):
    stats = Counter()
    cases = Counter()
    witnesses = {}
    minimum_margin = 10**6
    exponent_minima = [10**6,10**6,10**6]
    empty_minimum_margin = 10**6
    outers = [s for n in range(1, maxouter+1) for s in shapes(n)]
    outers += [profile_shape((3,4,2),(3,2)), profile_shape((3,5,3),(3,3))]
    inners = [s for n in range(2,maxinner+1) for s in shapes(n)]
    inners.append(profile_shape((2,4,2),(2,2)))
    inners.append(profile_shape((2,2,3,2),(2,1,2)))
    for s in inners:
        for mark in marks(s):
            W, O, hatW, hatO, caps, p, w = mark_data(s, mark)
            A,B,C = map(schur,(W,hatW,hatO))
            theta = sp.expand(schur(caps[0])*schur(caps[1]))
            cases[mark[-1]] += 1
            for d in outers:
                # Whole parent determinant only on the smaller side. Larger
                # parents use a literal interior determinant; its attribution
                # is checked separately and is not the transport formula.
                F = compose(d,s,mark)
                parts = components(interior(d))
                r,c = len({i for i,j in d}),len({j for i,j in d})
                M = width(d)
                rho = sum(len({i for i,j in x}) for x in parts)
                chi = sum(len({j for i,j in x}) for x in parts)
                L = sum(width(x) for x in parts)
                children = [compose(normal(x),s,mark) for x in parts]
                assert r-1-rho>=0 and c-1-chi>=0 and M-L>=1
                if len(d)>1:
                    exponent_minima = [min(a,b) for a,b in zip(exponent_minima,(r-1-rho,c-1-chi,M-L))]
                Z = sp.expand(theta * A**(r-1-rho) * B**(c-1-chi) * C**(M-L))
                child_counts = Counter(schur(x) for x in children)
                rhs = sp.expand(Z * sp.prod(schur(x) for x in children))
                lhs = schur(normal(interior(F)))
                assert sp.expand(lhs-rhs) == 0, (s,mark,d)
                assert polynomial_span(Z) < p
                assert all(polynomial_span(schur(x)) >= p for x in children)
                # Direct algebraic collision/multiplicity tests do not read spans.
                for child, exponent in child_counts.items():
                    gap = polynomial_span(child)-polynomial_span(Z)
                    minimum_margin = min(minimum_margin,gap)
                    if w==0:
                        empty_minimum_margin = min(empty_minimum_margin,gap)
                    for prime, power in prime_list(Z):
                        assert sp.expand(child-prime)!=0 and sp.expand(child+prime)!=0
                        stats['direct prime comparisons'] += 1
                    assert multiplicity(lhs,child)==exponent, (s,mark,d,child,exponent)
                    stats['direct multiplicity checks'] += 1
                    if exponent>1:
                        stats['repeated-child checks'] += 1
                        stats['repeated proper-child checks'] += any(len(x)>=2 for x in parts)
                        assert multiplicity(lhs,child)!=exponent-1
                        stats['multiplicity control'] += 1
                    if stats['collision control']==0:
                        assert any(sp.expand(prime-child)==0 or sp.expand(prime+child)==0 for prime,power in prime_list(sp.expand(Z*child)))
                        stats['collision control'] += 1
                if len(d) > 1:
                    assert M-L >= 2
                else:
                    assert M-L == 1
                    stats['singleton outer'] += 1
                stats['transport'] += 1
                stats['empty D interior'] += not parts
                stats['disconnected D interior'] += len(parts)>1
                stats['one-cell children'] += sum(len(x)==1 for x in parts)
                stats['proper children'] += sum(len(x)>=2 for x in parts)
                if len(F) <= 12:
                    assert sp.expand(kappa(F)-lhs)==0
                    stats['full-parent cofactor'] += 1
                if len({i for i,j in d}) == 1:
                    assert sp.expand(lhs-theta*C**len(d)*B**(len(d)-1))==0
                    stats['row amalgamation'] += 1
                bare = A**(r-1-rho)*B**(c-1-chi)*C**(M-L)*sp.prod(schur(x) for x in children)
                if sp.expand(lhs-B**2*bare)!=0:
                    stats['control caps'] += 1
                if sp.expand(lhs-rhs*A)!=0:
                    stats['control A exponent'] += 1
                if sp.expand(lhs-rhs*B)!=0:
                    stats['control B exponent'] += 1
                stats['w=0'] += w==0
                stats['w=p-1'] += w==p-1
            for name, val, bound in [('B',polynomial_span(B),w),('C',polynomial_span(C),max(0,p-w-2)),('Theta',polynomial_span(theta),max(0,w-1))]:
                if val and val==bound:
                    witnesses.setdefault(name,(len(s),p,w,mark[-1]))
        print('transport cumulative', len(s), dict(stats), flush=True)
    assert all(cases[c]>0 for c in 'abcd')
    assert all(stats['control '+name]>0 for name in ('caps','A exponent','B exponent'))
    assert stats['proper children'] and stats['disconnected D interior']
    assert stats['repeated-child checks'] and stats['repeated proper-child checks']
    assert stats['direct prime comparisons']
    print('proper-outer exponent minima (A,B,C):',exponent_minima)
    print('attained child/normalization margin: all=',minimum_margin,'empty=',empty_minimum_margin)
    assert minimum_margin==2 and empty_minimum_margin==2
    assert exponent_minima==[0,0,2]
    print('sharp nonzero bound witnesses', witnesses)
    print('transport cases',dict(cases),';',dict(stats))


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--transport',action='store_true')
    parser.add_argument('--area',type=int,default=9)
    args=parser.parse_args()
    counts,failures=census(args.area)
    if args.area in (8,9):
        expected={8:(294,6,288,856),9:(704,16,690,1970)}[args.area]
        assert tuple(counts[k] for k in ('ordinary','fails V','mixed','empty'))==expected
    witness()
    if args.transport:
        empty_boundary(args.area)
        transport()
    print('check_cell_model: PASS')
