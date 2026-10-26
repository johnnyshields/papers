"""Exact ribbon-fiber check by inverse path charts and Jacobi--Trudi determinants.

No imports from the paper's verification scripts.  All ribbon classes through
weight 10 are computed by a signed subset determinant, not by factor reversals
or coarsening inventories.  All connected skew diagrams through weight 10 are
also enumerated by row lengths and positive adjacent overlaps.

Charts of a ribbon are enumerated inversely from its path.  Empty charts repeat
one internal path in blocks, leaving the joining steps to the outer.  Positive
charts have a row outer: the positive mark and the corner identity exclude
more than one outer row, after excluding a positive outer interior.  Such
charts are precisely overlapping periodic paths.  This geometric reduction,
not a finite search over all arbitrary marked diagrams, bounds the chart set.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product


@lru_cache(None)
def compositions(n):
    if n == 0:
        return ((),)
    return tuple((a,) + b for a in range(1, n + 1) for b in compositions(n-a))


def cells(rows, overlaps):
    """English coordinates, rows explicitly top to bottom."""
    ans = set()
    left = 0
    for i, length in enumerate(rows):
        if i:
            left += overlaps[i-1] - length
        ans.update((i, left+j) for j in range(length))
    return frozenset(ans)


def normalize(S):
    a = min(i for i,j in S)
    b = min(j for i,j in S)
    return frozenset((i-a,j-b) for i,j in S)


def rotate(S):
    return normalize(frozenset((-i,-j) for i,j in S))


def path(S):
    ordered = sorted(S, key=lambda x: x[1]-x[0])
    assert len({j-i for i,j in S}) == len(S)
    out = []
    for (i,j),(k,l) in zip(ordered,ordered[1:]):
        assert (k-i,l-j) in ((0,1),(-1,0))
        out.append(0 if k == i else 1)
    return tuple(out)


def from_path(word):
    i = j = 0
    ans = {(i,j)}
    for north in word:
        if north:
            i -= 1
        else:
            j += 1
        ans.add((i,j))
    return normalize(frozenset(ans))


def rows_of(S):
    return tuple(sum(i == row for i,j in S) for row in sorted({i for i,j in S}))


@lru_cache(None)
def schur(S):
    """Complete-homogeneous polynomial from a signed subset determinant."""
    rr = sorted({i for i,j in S})
    left = [min(j for i,j in S if i == row) for row in rr]
    right = [max(j for i,j in S if i == row) for row in rr]
    r = len(rr)
    dp = {0: {(): 1}}
    for row in range(r):
        nxt = {}
        for mask, poly in dp.items():
            for col in range(r):
                if mask >> col & 1:
                    continue
                h = right[row]-left[col]-row+col+1
                if h < 0:
                    continue
                sign = -1 if (mask >> (col+1)).bit_count() % 2 else 1
                acc = nxt.setdefault(mask | (1 << col), defaultdict(int))
                for mon, coeff in poly.items():
                    newmon = tuple(sorted(mon+(h,))) if h else mon
                    acc[newmon] += sign*coeff
        dp = {mask: {mon:c for mon,c in poly.items() if c}
              for mask,poly in nxt.items()}
    result = tuple(sorted(dp.get((1 << r)-1, {}).items()))
    assert result
    assert all(sum(mon) == len(S) for mon,c in result)
    return result


def empty_word(outer, inner):
    out = list(inner)
    for seam in outer:
        out.append(seam)
        out.extend(inner)
    return tuple(out)


def empty_cells(D, E):
    """Literal empty-horizontal placement j*v+i*(1,1), in southwest frames."""
    def southwest_frame(S):
        sw = min(S, key=lambda x: x[1]-x[0])
        return frozenset((i-sw[0],j-sw[1]) for i,j in S)
    D,E = southwest_frame(D),southwest_frame(E)
    ne = max(E, key=lambda x: x[1]-x[0])
    v = (ne[0], ne[1]+1)
    ans = set()
    for i,j in D:
        k = j-i
        ans.update((a+k*v[0]+i,b+k*v[1]+i) for a,b in E)
    return normalize(frozenset(ans))


def near(a,b):
    return a[:-1]+(a[-1]+b[0],)+b[1:]


def composition_product(a,b):
    result = ()
    for power in a:
        block = b
        for _ in range(power-1):
            block = near(block,b)
        result += block
    return result


def charts(word):
    n = len(word)+1
    out = []
    for p in range(2,n//2+1):
        m,w = divmod(n,p)
        if not w:
            inner = word[:p-1]
            if all(word[k*p:k*p+p-1] == inner for k in range(m)):
                outer = tuple(word[k*p-1] for k in range(1,m))
                assert empty_word(outer,inner) == word
                out.append(((0,p),outer,inner,0))
        else:
            inner = word[:p+w-1]
            if all(word[k] == word[k%p] for k in range(len(word))):
                E = from_path(inner)
                ordered = sorted(E,key=lambda x:x[1]-x[0])
                W = frozenset(ordered[:w])
                v = (ordered[p][0]-ordered[0][0], ordered[p][1]-ordered[0][1])
                assert frozenset((i+v[0],j+v[1]) for i,j in W) == frozenset(ordered[p:])
                repeated = frozenset((i+k*v[0],j+k*v[1]) for k in range(m) for i,j in E)
                assert normalize(repeated) == from_path(word)
                assert len(repeated) == n
                # Legal end copies are consecutive path intervals.  Maximality
                # is automatic because every native diagonal has one cell.
                assert 0 < w < p
                assert normalize(E-W) == from_path(inner[w:])
                assert normalize(frozenset(ordered[:p])) == from_path(inner[:p-1])
                periodic = frozenset((i+k*v[0],j+k*v[1]) for k in range(-2,3) for i,j in E)
                assert len({j-i for i,j in periodic}) == len(periodic)
                assert all((i+1,j+1) not in periodic for i,j in periodic)
                out.append(((w,p+w),(0,)*(m-1),inner,w))
    return out


def positive_fiber(outer,inner,w):
    assert not any(outer)
    E = from_path(inner)
    ordered = sorted(E,key=lambda x:x[1]-x[0])
    p = len(E)-w
    v = (ordered[p][0]-ordered[0][0], ordered[p][1]-ordered[0][1])
    F = normalize(frozenset((i+k*v[0],j+k*v[1]) for k in range(len(outer)+1) for i,j in E))
    # A row has no other connected Schur mates; rotation transports the full mark.
    return {F,rotate(F)}


def main():
    maximum = 10
    ribbon_by_weight = {}
    classes = defaultdict(set)
    for n in range(1,maximum+1):
        ribbon_by_weight[n] = [normalize(cells(a,(1,)*(len(a)-1))) for a in compositions(n)]
        for F in ribbon_by_weight[n]:
            assert len(F) == n
            assert from_path(path(F)) == F
            assert rotate(F) == from_path(path(F)[::-1])
            assert schur(F) == schur(rotate(F))
            classes[schur(F)].add(F)
    print('ribbons through weight 10:',sum(map(len,ribbon_by_weight.values())))

    all_shapes = nonribbons = 0
    for n in range(1,maximum+1):
        seen = set()
        for a in compositions(n):
            for ov in product(*(range(1,min(x,y)+1) for x,y in zip(a,a[1:]))):
                S = normalize(cells(a,ov))
                assert S not in seen
                seen.add(S)
                P = schur(S)
                span = len({j-i for i,j in S})
                assert max(max(mon,default=0) for mon,c in P) == span
                ribbon = span == n
                assert ribbon == all(t == 1 for t in ov)
                assert (P in classes) == ribbon
                nonribbons += not ribbon
        all_shapes += len(seen)
    print('connected skew diagrams through weight 10:',all_shapes,
          '; nonribbons excluded from ribbon classes:',nonribbons)

    bridges = 0
    for m in range(1,maximum+1):
        for k in range(1,maximum//m+1):
            for a in compositions(m):
                for b in compositions(k):
                    D = normalize(cells(a,(1,)*(len(a)-1)))
                    E = normalize(cells(b,(1,)*(len(b)-1)))
                    F = empty_cells(D,E)
                    assert F == from_path(empty_word(path(D),path(E)))
                    assert rows_of(F) == composition_product(a,b)
                    bridges += 1
    print('top-to-bottom product/cell bridges through weight 10:',bridges)

    rooted = tested = empty = positive = 0
    histogram = defaultdict(int)
    for n in range(1,maximum+1):
        for F in ribbon_by_weight[n]:
            available = charts(path(F))
            if not available:
                assert classes[schur(F)] == {F,rotate(F)}
                continue
            rooted += 1
            best = min(c[0] for c in available)
            for score,outer,inner,w in available:
                if score != best:
                    continue
                D = from_path(outer)
                outer_class = classes[schur(D)]
                if w:
                    assert outer_class == {D}
                    fiber = positive_fiber(outer,inner,w)
                    positive += 1
                else:
                    fiber = {from_path(empty_word(path(A),e))
                             for A in outer_class for e in (inner,inner[::-1])}
                    empty += 1
                assert classes[schur(F)] == fiber, (rows_of(F),score)
                for H in classes[schur(F)]:
                    hc = charts(path(H))
                    assert hc and min(c[0] for c in hc) == best
                tested += 1
                histogram[n] += 1
    print('rooted ribbons:',rooted)
    print('source-minimal charts:',tested,'; empty:',empty,'; positive:',positive)
    print('source-minimal charts by weight:',dict(sorted(histogram.items())))

    a = b = (1,2)
    original = composition_product(a,b)
    flipped = composition_product(a,b[::-1])
    assert flipped != original and flipped != original[::-1]
    assert schur(normalize(cells(original,(1,)*(len(original)-1)))) == schur(normalize(cells(flipped,(1,)*(len(flipped)-1))))
    print('last-factor reversal counterexample:',original,'->',flipped,
          '; whole reversal:',original[::-1])
    print('ALL PASS')


if __name__ == '__main__':
    main()
