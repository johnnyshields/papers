"""Complete small-parent roots and source-minimality under changed outers.

Uses only the cell model in check_cell_model, which shares no code with
diagram_tools.py. Every nonempty proper composition contains its inner
and cells outside it. Private-singleton sampling injects the outer cells into
the parent and misses another residue. Thus both factor areas are strictly less
than parent area; enumerating all such factors gives complete root lists here.
The span bound is used only to discard candidates incapable of landing in range.
"""
from collections import Counter, defaultdict
from math import gcd
from check_cell_model import shapes, marks, compose, width, cont, normal, h, schur, interior, components


def is_line(s):
    return len({i for i,j in s}) == 1 or len({j for i,j in s}) == 1


def main(limit=10):
    stats=Counter()
    charts=defaultdict(list)
    outers=[(d,width(d)) for n in range(2,limit) for d in shapes(n)]
    for n in range(2,limit):
        for E in shapes(n):
            for mark in marks(E):
                W,v,case=mark
                p,w=cont(v),width(W)
                if 2*p+w > limit:
                    continue
                for D,M in outers:
                    if p*M+w > limit:
                        continue
                    F=compose(D,E,mark)
                    assert len(D)<len(F) and len(E)<len(F)
                    if len(F)<=limit:
                        charts[F].append((E,mark,D))
                        stats['charts']+=1
        print('inner area',n,'charts',stats['charts'],flush=True)
    minima={F:min((width(mark[0]),width(E)) for E,mark,D in ch) for F,ch in charts.items()}
    grouped=defaultdict(list)
    for F,ch in charts.items():
        root_periods={cont(mark[1]) for E,mark,D in ch}
        for E,mark,D in ch:
            score=(width(mark[0]),width(E))
            p=cont(mark[1])
            grouped[E,mark].append((F,D,score==minima[F]))
            if not is_line(E) and score==minima[F]:
                assert all(q%p==0 for q in root_periods)
                stats['nonline minimal charts']+=1
            for E2,mark2,D2 in ch:
                q=cont(mark2[1])
                if gcd(p,q)==1:
                    assert is_line(E) and is_line(E2)
                    stats['coprime comparisons']+=1
        stats['rooted parents']+=1
    for (E,mark),items in grouped.items():
        if is_line(E):
            continue
        verdicts={is_min for F,D,is_min in items}
        assert len(verdicts)==1, (E,mark,items)
        if any(is_min for F,D,is_min in items) and len({D for F,D,is_min in items})>1:
            stats['outer-independent mark groups']+=1
            stats['outer-independent charts']+=len(items)
    # Re-derive the line control from every row factor/overlap, not a fixed list.
    row_min={}
    for N in (9,12):
        scores=[]
        for outer in range(2,N):
            for inner in range(2,N):
                for w in range(inner):
                    p=inner-w
                    if w<p and outer*p+w==N:
                        scores.append((w,inner))
        row_min[N]=min(scores)
    assert row_min=={9:(0,3),12:(0,2)}
    print('line-inner control:',row_min)
    # Compare Schur-equal rooted parents through the whole computed range.
    fibers=defaultdict(list)
    for F in charts:
        fibers[schur(F)].append(F)
    for fiber in fibers.values():
        ps={minima[F][1]-minima[F][0] for F in fiber}
        assert len(ps)==1
        if len(fiber)>1:
            stats['equal-parent comparisons']+=len(fiber)*(len(fiber)-1)//2
    assert stats['nonline minimal charts']>0 and stats['outer-independent mark groups']>0
    print('complete parent-area bound:',limit)
    print(dict(stats))
    print('check_root_periods: PASS')


if __name__=='__main__':
    main()
