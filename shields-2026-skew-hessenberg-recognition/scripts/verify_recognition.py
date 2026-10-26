"""Exact tests of stronger recognition and compositional positive-gap relaxation."""
from collections import defaultdict
from itertools import permutations
from verify_hessenberg import compositions, interval, determinant, betas, composite


def circ(alpha,beta):
    ans=[]
    for a in alpha:
        block=list(beta)
        for _ in range(a-1):
            block[-1]+=beta[0]
            block+=list(beta[1:])
        ans+=block
    return tuple(ans)


def signature(f):
    return tuple(sorted(f.items()))


def tests():
    tested=0
    for size in range(1,13):
        groups=defaultdict(list)
        for delta in compositions(size):
            groups[signature(interval(delta,(0,)*(len(delta)-1)))].append(delta)
        for group in groups.values():
            for delta in group:
                interior=delta[1:-1]
                if (delta[0]+delta[-1] not in interior or
                    (delta[-1],delta[0]) not in tuple(zip(interior,interior[1:]))):
                    assert set(group)<={delta,delta[::-1]},(delta,group)
                    tested+=1
    print('PASS: missing-sum-or-adjacent-endpoint-pair criterion:',tested,'compositions, sizes 1 through 12.')
    # Successive examples need genuinely weaker recognition hypotheses.
    profiles=[((3,3,3),(1,1)),((3,3,4,4),(1,1,1)),
              ((5,3,7,3),(1,1,1)),((3,3,4,6,4),(1,1,1,1))]
    counts=0
    for index,(rows,gaps) in enumerate(profiles):
        a,b,c=rows[0],rows[-1],gaps[0]
        if index<2:
            assert a in rows[1:-1] and b in rows[1:-1]
            assert a+b-c not in rows[1:-1]
        elif index==2:
            assert a not in rows[1:-1] and a+b-c in rows[1:-1]
            assert 3+3-c==a
        else:
            assert all(x in rows[1:-1] for x in (a,b,a+b-c))
            assert (b,a) not in tuple(zip(rows[1:-1],rows[2:-1]))
        for m in ((1,2,3) if index<3 else (1,2)):
            r,g=composite(rows,gaps,(m,))
            ref=interval(r,g)
            mates=[]
            for order in set(permutations(r)):
                if any(order[i]<=g[i-1]+g[i] for i in range(1,len(r)-1)):
                    continue
                f=interval(order,g)
                if f==ref:
                    mates.append(order)
                    assert determinant(*betas(order,g))==ref
                counts+=1
            assert set(mates)=={r,r[::-1]}
    print('PASS: strengthened constant-gap examples (first three: powers 1..3; '
          'last: powers 1..2);',counts,'legal row orders.')
    # No Hessenberg assumption is made in this dense recognition test.
    rows,gaps=(11,6,8),(4,4)
    assert rows[0]>2*max(gaps) and rows[1]<=sum(gaps)
    dense=0
    for m in (1,2,3):
        r,g=composite(rows,gaps,(m,))
        ref=determinant(*betas(r,g))
        mates=[]
        for order in set(permutations(r)):
            if any(c>=min(a,b) for a,b,c in zip(order,order[1:],g)):
                continue
            f=determinant(*betas(order,g))
            if f==ref:
                mates.append(order)
            dense+=1
        assert set(mates)=={r,r[::-1]}
    print('PASS: dense private-endpoint example, powers 1 through 3;',dense,'connected row orders.')
    # F_alpha(F_gamma(D)) = F_(alpha circ gamma)(D), including zero gaps.
    checks=0
    for rows,gaps in [((3,3),(1,)),((3,4),(1,)),((2,4,2),(1,1))]:
        for size in range(1,5):
            for gamma in compositions(size):
                E=composite(rows,gaps,gamma)
                for M in range(1,5):
                    for alpha in compositions(M):
                        left=composite(*E,alpha)
                        right=composite(rows,gaps,circ(alpha,gamma))
                        assert left==right
                        checks+=1
    print('PASS: exact profile associativity:',checks,'mixed-zero recodings.')
    print('ALL PASS')

if __name__=='__main__':
    tests()
