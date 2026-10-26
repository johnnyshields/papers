"""Test a proposed completeness step: use a core decoder, else an unused contact pair.

The purpose is to find a geometric obstruction to that step, not to estimate
unrestricted orientation coverage or certify equality from evaluations.
"""
from verify_hessenberg import betas, data, core, determinant
from verify_wall_criteria import sites


def profile(X,Y):
    X,Y=sorted(X,reverse=True),sorted(Y,reverse=True)
    if len(X)!=len(Y) or len(set(X))!=len(X) or len(set(Y))!=len(Y):
        return None
    r=tuple(a-b for a,b in zip(X,Y));g=tuple(X[i+1]-Y[i] for i in range(len(X)-1))
    if not all(0<c<min(a,b) for a,b,c in zip(r,r[1:],g)):
        return None
    if not all(r[i]>g[i-1]+g[i] for i in range(1,len(r)-1)):
        return None
    return r,g


def tests():
    # Fixed reflection-symmetric cores, not a census of all inner profiles.
    seeds=[((4,8,9,8,4),(3,3,3,3)),
           ((4,8,9,10,9,8,4),(3,3,3,3,3,3)),
           ((5,10,11,10,5),(4,4,4,4)),
           ((3,6,7,6,3),(2,2,2,2))]
    witnesses=[]
    for seed in seeds:
        S,p,P,Q,J=data(*seed)
        assert P=={S+p-b for b in Q}
        X,Y=betas(*seed)
        for t in range(2*p+1,S-p):
            if t in P|Q|J or t-p in X or t in Y:
                continue
            E=profile((*X,t-p),(*Y,t))
            if E is None or E==(E[0][::-1],E[1][::-1]):
                continue
            SS,pp,PP,QQ,JJ=data(*E)
            assert (SS,pp,PP,QQ)==(S,p,P,Q)
            W={(a-b)%S for a in {0,p}|P for b in {0,p}|Q}
            Js={S+p-a for a in JJ}
            def counts(Z):
                out={}
                for a in Z:
                    pair=tuple(sorted((a,S-a)))
                    out[pair]=out.get(pair,0)+1
                return out
            lhs,rhs=counts(JJ),counts(Js)
            uncovered=[pair for pair in lhs.keys()|rhs.keys()
                       if lhs.get(pair,0)!=rhs.get(pair,0) and all(a not in W for a in pair)]
            if not uncovered:
                witnesses.append((E,S,p,P,Q,JJ,W))
    assert witnesses,'This proposed obstruction was not found in the specified tests.'
    E,S,p,P,Q,J,W=witnesses[0]
    assert E == ((4,8,9,10,9,6,3,2),(3,3,3,3,3,1,1))
    assert (S,p,P,Q,J) == (34,1,{5,10,16,23,29},{6,12,19,25,30},{3})
    assert W == {0,1,4,5,9,10,11,14,15,16,17,19,20,22,23,25,27,28,29,31,32,33}
    print('OBSTRUCTION',E,'S,p=',S,p,'P,Q,J=',sorted(P),sorted(Q),sorted(J),'W=',sorted(W))
    U,V=core(S,p,P,Q,3,{1})
    Us,Vs=core(S,p,P,Q,3,{2})
    assert determinant(U,V)==determinant(Us,Vs)
    print('PASS: exact symmetric-core equality; every asymmetric contact pair is contaminated.')
    print('This refutes completeness of core-only decoding plus the unused-pair contact rule, '
          'not the full-parent orientation conjecture.')
    print('ALL PASS')

if __name__=='__main__':
    tests()
