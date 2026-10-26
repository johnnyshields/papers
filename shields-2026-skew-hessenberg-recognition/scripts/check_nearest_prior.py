"""Check the exact relation to decomposition-independent content sets.

For the row outside decomposition, initial contents are Y+1-N and
terminal contents plus one are X+1-N, for beta lists of length N.
"""
from verify_hessenberg import betas, determinant, composite, data, core


def tests():
    E=((3,9,4),(1,2)); alpha=(2,1,2)
    r,g=composite(*E,alpha); X,Y=betas(r,g);N=len(X)
    S,p,P,Q,J=data(*E); M=sum(alpha)
    T={sum(alpha[i:]) for i in range(1,len(alpha))};K=set(range(1,M))-T
    starts={y+1-N for y in Y};ends={x+p+1-N for x in X}
    U,V=core(S,p,P,Q,M,K)
    assert starts-ends=={v+1-N for v in V}
    assert ends-starts=={u+1-N for u in U}
    assert {u//S for u in U if u%S==0 and 0<u<M*S}==K
    # General content-set recovery from a scalar polynomial is false.
    A=((2,4,4,5),(1,1,2)); B=((2,4,5,4),(1,2,1))
    XA,YA=betas(*A);XB,YB=betas(*B)
    assert not set(XA)&set(YA) and not set(XB)&set(YB)
    assert determinant(XA,YA)==determinant(XB,YB)
    assert (XA,YA)!=(XB,YB)
    S=XA[0]
    assert (tuple(sorted(S-y for y in YA)),tuple(sorted(S-x for x in XA))) != (tuple(sorted(XB)),tuple(sorted(YB)))
    print('PASS: Chen–Yang unmatched content sets are translated residual V and U; '
          'K is their variable residue-zero portion with E,M fixed.')
    print('PASS: equal positive-gap Hessenberg polynomials need not have the same '
          'unmatched content sets, even up to rotation:',(XA,YA),(XB,YB))
    print('ALL PASS')

if __name__=='__main__':
    tests()
