"""Exact controls for the complete five-row constant-gap power-recognition split."""
from itertools import product
from verify_hessenberg import betas, data, composite, interval, determinant, core, coefficient
from verify_wall_criteria import sites
from check_multiplicity_recognition import unique_orders


def tests():
    balanced=nonrigid=orders=deletions=0
    for c in (1,2,3):
        for a,b in product(range(2*c+1,15),repeat=2):
            L=a+b-c
            if L>14:
                continue
            E=(a,b,a,L,b);H=(a,L,b,a,b);g=(c,)*4
            assert L in E[1:-1] and (b,a) in tuple(zip(E[1:-1],E[2:-1]))
            assert L in H[1:-1] and (b,a) in tuple(zip(H[1:-1],H[2:-1]))
            assert interval(E,g)==interval(H,g)
            assert determinant(*betas(E,g))==interval(E,g)
            if a!=b:
                assert E!=H and E[::-1]!=H
                nonrigid+=2
                continue
            balanced+=2
            reduced=((3*a-2*c,4*a-3*c,a),(2*a-c,c))
            S,p,P,Q,J=data(E,g);SS,pp,PP,QQ,JJ=data(*reduced)
            assert (S,p)==(6*a-5*c,a-c)==(SS,pp)
            R=sites(S,p,P,Q,c)
            assert R=={(4*a-3*c,4*a-4*c),(5*a-4*c,5*a-5*c)}
            assert P-{x for x,y in R}==PP and Q-{y for x,y in R}==QQ
            assert sites(S,p,PP,QQ,2*a-c)=={(2*a-c,0)}
            for m in (1,2):
                rows,gaps=composite(E,g,(m,))
                f=interval(rows,gaps);matches=[]
                for order in unique_orders(rows):
                    assert all(order[i]>2*c for i in range(1,len(order)-1))
                    orders+=1
                    if interval(order,gaps)==f:
                        matches.append(order)
                assert set(matches)=={rows,rows[::-1]}
            for M,K in ((1,set()),(2,{1})):
                f=determinant(*core(S,p,P,Q,M,K))
                selected=coefficient(f,c,2*M)
                g0=determinant(*core(S,p,PP,QQ,M,K))
                assert selected==g0 or selected=={mon:-v for mon,v in g0.items()}
                deletions+=1
    assert (balanced,nonrigid)==(22,164)
    print('PASS: the 186 five-row pattern escapes in c=1..3, rows<=14 split into '
          '22 balanced power-rigid profiles and 164 profiles with an exact extra mate.')
    print('PASS:',orders,'legal power orders of balanced rotation representatives, '
          'powers 1 and 2; only rotations.')
    print('PASS:',deletions,'full core-deletion polynomials; actual site and private '
          'terminal checks for every balanced parameter pair.')
    print('ALL PASS')

if __name__=='__main__':
    tests()
