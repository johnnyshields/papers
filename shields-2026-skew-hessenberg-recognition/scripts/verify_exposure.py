"""Positional exposure checks including equal endpoints and palindromic gaps."""
from itertools import product
from verify_hessenberg import composite, compositions


def join(pieces, contract=False):
    rows,gaps=map(list,pieces[0])
    for r,g in pieces[1:]:
        if contract:
            rows[-1]+=r[0]
            rows.extend(r[1:])
            gaps.extend(g)
        else:
            rows.extend(r)
            gaps.extend((0,)+g)
    return tuple(rows),tuple(gaps)


def tests():
    inners=[((3,4,5,3),(1,1,1)),((3,6,3),(1,1)),
            ((2,4,3),(1,1)),((2,3),(1,)),((3,4,7,3),(1,2,1)),
            ((9,6,6),(4,4)),((11,6,8),(4,4))]
    count=accepted=0
    for E in inners:
        for M in range(1,7):
            C=composite(*E,(M,))
            for beta in compositions(M):
                normal=composite(*E,beta)
                for flips in product((False,True),repeat=len(beta)):
                    pieces=[]
                    for b,flip in zip(beta,flips):
                        r,g=composite(*E,(b,))
                        pieces.append((r[::-1],g[::-1]) if flip else (r,g))
                    contraction=join(pieces,True)
                    H=join(pieces)
                    if contraction==C:
                        assert H==normal,(E,beta,flips)
                        accepted+=1
                    count+=1
    # Gaps alone do not orient this inner.
    E=inners[0]
    assert E[1]==E[1][::-1] and E[0]!=E[0][::-1]
    reversed_E=(E[0][::-1],E[1][::-1])
    assert join([E,reversed_E],True)!=composite(*E,(2,))
    print(f'PASS: {count} positional orientation choices; {accepted} compatible '
          'contractions give exactly the prescribed literal composite.')
    print('PASS: equal-endpoint palindromic-gap row-orientation negative control fires.')
    print('ALL PASS')

if __name__=='__main__':
    tests()
