"""Firing controls for dense private-row recognition and mixed-zero recoding."""
from verify_hessenberg import betas, determinant, interval, coefficient, composite, compositions


def rotate(E):
    return E[0][::-1],E[1][::-1]


def tests():
    delta=(1,2,1,3,2)
    reference=interval(delta,(0,)*4)
    ribbon_class={a for a in compositions(9) if interval(a,(0,)*(len(a)-1))==reference}
    assert ribbon_class=={(1,2,1,3,2),(1,3,2,1,2),(2,1,2,3,1),(2,3,1,2,1)}
    assert len(ribbon_class)>2 and delta[0]+delta[-1] in delta[1:-1]
    assert (delta[-1],delta[0]) in tuple(zip(delta[1:-1],delta[2:-1]))
    print('PASS: classical four-member ribbon class detected; endpoint sum and '
          'reversed adjacent endpoint pair occur internally, so recognition rejects it.')
    # The full determinant engine must detect a genuine nonrotation mate.
    A=((2,4,4,5),(1,1,2));B=((2,4,5,4),(1,2,1))
    f=determinant(*betas(*A));g=determinant(*betas(*B))
    assert f==g==interval(*A) and f and B not in (A,rotate(A))
    XA,YA=betas(*A);XB,YB=betas(*B)
    fa=determinant(tuple(x+1 for x in XA),YA)
    fb=determinant(tuple(x+1 for x in XB),YB)
    assert fa!=fb and (fa.get((2,6,11),0),fb.get((2,6,11),0))==(0,-1)
    print('PASS: determinant engine sees a nonrotation equality and its later separation.')
    # Below a>2G an internal private row can have an irreducible cofactor.
    H=((5,3,5),(2,2));X,Y=betas(*H)
    assert sum(x-y==3 for x in X for y in Y)==1
    got=coefficient(determinant(X,Y),3)
    assert got=={(5,5):1,(1,9):-1}
    assert X[2]-Y[0]==1>0
    assert H[0][1]<=2*max(H[1])
    J=((5,6,5),(2,2));X,Y=betas(*J)
    assert J[0][1]>2*max(J[1]) and X[2]-Y[0]<0
    assert coefficient(determinant(X,Y),6)=={(5,5):1}
    print('PASS: the 2G guard separates the split cofactor from the connected '
          'h5^2-h1*h9 cofactor.  This is a control of the proof step, not a '
          'counterexample to every possible weakened theorem.')
    # Dropping the ribbon/base-symmetry alternatives makes MTZ false at m=1.
    D=((3,4),(1,));gamma=(1,2)
    E=composite(*D,gamma);F=composite(*D,gamma[::-1])
    assert D!=rotate(D) and E!=F and F!=rotate(E)
    e=determinant(*betas(*E));f=determinant(*betas(*F))
    assert e==f==interval(*E) and e
    print('PASS: recoding guard fires; nonsymmetric D=(3,4;1), gamma=(1,2) '
          'has extra one-copy mate',F,'for',E)
    print('ALL PASS')

if __name__=='__main__':
    tests()
