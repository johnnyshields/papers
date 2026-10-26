"""All-root finite checks of source minima, gauges, and graph components.

Uses only the cell implementation in check_gcd_fold_sweep.py.  Schur equality is
computed in elementary generators; charts are exhaustively recovered from
parent extreme windows at every proper period, then recomposed literally.
"""
from collections import defaultdict,Counter
from check_gcd_fold_sweep import (shapes,span,roots_at,marks_at,rotate_mark,
                                 rotate,at,dual_jt,profile,compose)


def polykey(D):return tuple(sorted(dual_jt(D).items()))


def markedkey(m):return (tuple(sorted(m.E)),tuple(sorted(m.W)),m.v,m.case)


def key(D,m):
    variants=[]
    for mm in (m,rotate_mark(m)):
        variants.append((markedkey(mm),polykey(D)))
        if mm.case in 'ab':
            for nn in marks_at(mm.E,mm.p):
                if nn.case in 'ab' and nn.case!=mm.case:
                    assert compose(D,mm)==compose(at(D),nn)
                    variants.append((markedkey(nn),polykey(at(D))))
    return min(variants)


def is_line(S):return len({i for i,j in S})==1 or len({j for i,j in S})==1


def main(max_area=9):
    counts=Counter()
    for n in range(1,max_area+1):
        by_poly=defaultdict(list);info={}
        for F in shapes(n):
            rr=[(D,m) for p in range(2,span(F)//2+1) for D,m in roots_at(F,p)]
            counts['connected diagrams']+=1;counts['charts']+=len(rr)
            if rr:
                counts['rooted diagrams']+=1
                score=min((m.w,span(m.E)) for D,m in rr)
                source=[(D,m) for D,m in rr if (m.w,span(m.E))==score]
                kk={key(D,m) for D,m in source}
                assert len(kk)==1,('key ambiguity',profile(F),source)
                pp={m.p for D,m in rr};p0=min(pp)
                if not any(is_line(m.E) for D,m in rr):
                    counts['line-inner-free diagrams']+=1
                    assert all(p%p0==0 for p in pp)
                    assert {m.p for D,m in source}=={p0}
                for D,m in source:
                    if not is_line(m.E):assert all(p%m.p==0 for p in pp)
                info[F]=(rr,next(iter(kk)),{key(D,m) for D,m in rr})
            else:info[F]=([],None,set())
            by_poly[polykey(F)].append(F)
        for cls in by_poly.values():
            # Explicit common-factor adjacency; no use of the minimum key here.
            adj={F:{G for G in cls if info[F][2]&info[G][2]} for F in cls}
            unseen=set(cls)
            while unseen:
                F=next(iter(unseen));comp={F};queue=[F]
                for H in queue:
                    for G in adj[H]:
                        if G not in comp:comp.add(G);queue.append(G)
                unseen-=comp;counts['components']+=1
                assert all(G==H or G in adj[H] for G in comp for H in comp)
                if info[F][0]:
                    assert rotate(F) in comp
                    assert len({info[H][1] for H in comp})==1
                    for H in comp:
                        rr,k,_=info[H]
                        assert comp=={G for G in cls if k in info[G][2]}
                else:assert comp=={F}
            # A and R have no hidden graph convention in these finite classes.
            keys={info[F][1] for F in cls if info[F][0]}
            A=all(set(cls)=={F,rotate(F)} for F in cls if not info[F][0])
            R=len(keys)<=1
            augmented={F:adj[F]|{rotate(F)} for F in cls}
            comp={cls[0]};queue=[cls[0]]
            for F in queue:
                for G in augmented[F]:
                    if G not in comp:comp.add(G);queue.append(G)
            assert (len(comp)==len(cls))==(A and R)
        print('through area',n,dict(counts),flush=True)
    print('ALL PASS',dict(counts))


if __name__=='__main__':main()
