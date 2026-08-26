#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `lem:amplitude-divisor`.

`hamp_1`'s exponent at the `r = 1` upper endpoint when the WEIGHT vanishes there.

`check_upper_amplitude_r_one.py` measures the exponent at `B = 1` and finds `-1`:
`ftAmp = -B(tau)/D'(tau)` is a residue, `D'(-L) = 0` because the principal pair
collides at `-L`, so the amplitude blows up.  That is the `B(-L) != 0` case.  The
vanishing case was uncovered, and it is the real cost of the binder -- the
analogue of `B(0) != 0` at the other end.

Measured here with `B(t) = (t + L)^m`, which vanishes at `-L` to order exactly
`m` and keeps `B(0) = L^m != 0`:

    exponent  =  m - 1        (numerator order m, denominator order 1)

  (V1) `m = 0` gives `-1`: the amplitude BLOWS UP, and a constant floor serves.
  (V2) `m = 1` gives `0`: the amplitude tends to a finite NONZERO limit.  A
       constant floor still serves, but nothing smaller is available.
  (V3) `m >= 2` gives `m - 1 > 0`: the amplitude VANISHES.  A constant floor is
       then FALSE, and `hamp_1` needs `A_1 * eta^(m-1)` -- the same shape the
       `r >= 2` endpoint carries at `p_1 = 1`, arriving here for a different
       reason.

So `hamp_1` at `r = 1` is not uniformly "a constant floor serves": that holds
exactly while `B` does not vanish at the collision point, and the general
exponent is `ord_{-L}(B) - 1`.

mpmath only, 45 digits.  The branch comes from the monotone angle-sum and is
validated as the minimum modulus; `L` is found from `E(-L) = 0`.
"""
from mpmath import mp, mpf, mpc, exp, pi, arg, findroot, polyroots, im, re, fabs, log
mp.dps=45
def qc(c,a):
    p=[mpf(c)]
    for ak in a:
        n=[mpf(0)]*(len(p)+1)
        for i,co in enumerate(p): n[i]+=co*mpf(ak); n[i+1]-=co
        p=n
    return p[::-1]
def pe(C,t):
    v=mpc(0)
    for co in C: v=v*t+co
    return v
def dv(C):
    d=len(C)-1
    return [C[i]*(d-i) for i in range(d)] if d>0 else [mpf(0)]
def dco(Q,z,r):
    D=[mpf(0)]*max(0,r+1-len(Q))+list(Q); D[len(D)-1-r]+=z
    while len(D)>1 and D[0]==0: D=D[1:]
    return D
def angsum(a,r,th,tau):
    w=mpc(tau)*exp(mpc(0,1)*th)
    return sum(arg(mpc(ak)-w) for ak in a)-r*th
def branch(c,a,r,th):
    Q=qc(c,a); lo,hi=mpf(10)**-14, mpf(max(a))*4
    Slo,Shi=angsum(a,r,th,lo),angsum(a,r,th,hi); cand=[]
    for l in range(int(mp.floor(-Slo/pi))-1,int(mp.ceil(-Shi/pi))+2):
        t=-mpf(l)*pi
        if not (Shi<t<Slo): continue
        cand.append(mpf(re(findroot(lambda u: angsum(a,r,th,u)-t,(lo,hi),solver='bisect',tol=mpf(10)**-38))))
    for tau in sorted(cand):
        w=mpc(tau)*exp(mpc(0,1)*th); zc=-pe(Q,w)/w**r
        if fabs(im(zc))>mpf(10)**-22: continue
        z=mpf(re(zc)); rts=polyroots(dco(Q,z,r),maxsteps=400,extraprec=600)
        if min(fabs(t-w) for t in rts)>mpf(10)**-20: continue
        if fabs(fabs(w)-min(fabs(t) for t in rts))<mpf(10)**-20: return tau,z,Q
    return None
def Lof(a,r):
    Q=qc(1.0,a); Qp=dv(Q)
    E=lambda t:(mpc(t)*pe(Qp,mpc(t))-r*pe(Q,mpc(t))).real
    step=mpf(1)/2000; x=step; prev=E(-x)
    while x<50:
        cur=E(-(x+step))
        if prev*cur<0: return mpf(findroot(lambda u:E(-u),(x,x+step),solver='bisect',tol=mpf(10)**-30))
        prev,x=cur,x+step
    return None
print("hamp_1's exponent at r = 1 when B VANISHES at -L to order m")
print("  predicted: exponent = m - 1  (numerator order m, denominator order 1)")
print("   a              m   B(t)          exponent    |W| at eta=1e-3,1e-4,1e-5")
ETAS=[mpf(10)**-3,mpf(10)**-4,mpf(10)**-5]
ROWS=[]
for a in ([1.0,1.0,2.0],[1.0,1.0,1.0,2.0]):
    L=Lof(a,1)
    for m in (0,1,2):
        # B(t) = (t + L)^m  vanishes at -L to order m; B(0) = L^m != 0
        Bc=[mpf(1)]
        for _ in range(m):
            nb=[mpf(0)]*(len(Bc)+1)
            for i,co in enumerate(Bc): nb[i]+=co; nb[i+1]+=co*L
            Bc=nb
        vals=[]
        for th in [pi-e for e in ETAS]:
            b=branch(1.0,a,1,th)
            tau,z,Q=b; w=mpc(tau)*exp(mpc(0,1)*th)
            D=dco(Q,z,1); dp=pe(dv(D),w)
            vals.append(fabs(pe(Bc,w)/dp))
        sl=(log(vals[0])-log(vals[-1]))/(log(ETAS[0])-log(ETAS[-1]))
        print(f"   {str(tuple(a)):15s}{m}  (t+L)^{m}      {mp.nstr(sl,8):11s} "
              +"  ".join(mp.nstr(v,6) for v in vals))
        ROWS.append((tuple(a), m, sl, vals))

print()
for a, m, sl, vals in ROWS:
    assert fabs(sl - (m - 1)) < mpf(1) / 50, (
        f"a={a}, m={m}: exponent {mp.nstr(sl,8)}, expected {m-1}")
print(f"PASS  the exponent is ord_(-L)(B) - 1 at all {len(ROWS)} cases: -1 when B "
      f"does not vanish, 0 at a simple zero, +1 at a double one")

for a, m, sl, vals in ROWS:
    if m == 0:
        assert vals[-1] > vals[0] > 1, f"a={a}: |W| should blow up at m=0"
    elif m == 1:
        assert fabs(vals[-1] / vals[0] - 1) < mpf(1) / 1000, (
            f"a={a}: |W| should tend to a finite nonzero limit at m=1")
        assert vals[-1] > 0
    else:
        assert vals[-1] < vals[0], f"a={a}: |W| should vanish at m>=2"
print("PASS  and the three regimes are qualitatively distinct -- blow-up, finite "
      "nonzero limit, and decay -- so a constant floor serves at m <= 1 and is "
      "FALSE at m >= 2, where hamp_1 needs A_1 * eta^(m-1)")

print()
print("ALL PASS  check_upper_amplitude_b_vanishing")
