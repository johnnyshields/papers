"""The elbow cone satisfies the paper's own square-gap formula `eq:square-gap`.

The cone of Proposition prop:elbow satisfies both the row-zero relation and the
ratio identity by construction, and fails the Floor conclusion.  This file checks
the sharper fact: its square-weight gap is exactly the one the paper's own
Theorem thm:ratio-rigidity predicts, alpha_x - alpha_y = 2 gamma (y - x) with
gamma = a when r = 0 and gamma = r otherwise (`eq:square-gap`).  So the formula follows
from the tie structure alone, carries no realizability, and cannot separate a
genuine defect from a formal one.
"""
import sys, itertools
from collections import defaultdict

def padd(p, q, s=1):
    o = defaultdict(int)
    for m, c in p.items(): o[m] += c
    for m, c in q.items(): o[m] += s * c
    return {m: c for m, c in o.items() if c}

def pmul(p, q):
    o = defaultdict(int)
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            o[tuple(sorted(m1 + m2, reverse=True))] += c1 * c2
    return {m: c for m, c in o.items() if c}

def h(k):
    return {} if k < 0 else ({(): 1} if k == 0 else {(k,): 1})

def sqwt(m):
    return sum(e * e for e in m)

def minwt(p):
    return min(sqwt(m) for m in p)

fails = []
tot = ties = 0
for x, y, z in itertools.combinations(range(1, 6), 3):
    for r in range(0, 4):
        for a in range(1, 4):
            Y = {d: padd(h(r + a + d), pmul(h(a), h(r + d)), -1) for d in (x, y, z)}
            hv = {d: h(d) for d in (x, y, z)}
            G = {x: padd(pmul(hv[y], Y[z]), pmul(hv[z], Y[y]), -1),
                 y: padd(pmul(hv[z], Y[x]), pmul(hv[x], Y[z]), -1),
                 z: padd(pmul(hv[x], Y[y]), pmul(hv[y], Y[x]), -1)}
            if not all(G.values()):
                continue
            # both relations, exactly
            P0 = {}
            ratio = {}
            for d in (x, y, z):
                P0 = padd(P0, pmul(h(d), G[d]))
                ratio = padd(ratio, pmul(h(r + a + d), G[d]))
                ratio = padd(ratio, pmul(pmul(h(a), h(r + d)), G[d]), -1)
            alpha = {d: minwt(G[d]) + d * d for d in (x, y, z)}
            gamma = a if r == 0 else r
            tot += 1
            ok = (P0 == {} and ratio == {}
                  and alpha[y] == alpha[z]
                  and alpha[x] - alpha[y] == 2 * gamma * (y - x))
            if alpha[y] == alpha[z]:
                ties += 1
            if not ok:
                fails.append((x, y, z, r, a, alpha, 2 * gamma * (y - x)))

print(f"cone points tested                     : {tot}")
print(f"with alpha_y = alpha_z (so T_0^+ = two): {ties}")
print(f"failures of relations or of the gap    : {len(fails)}")
for f in fails[:3]:
    print("   ", f)
print()
print("ALL PASS" if tot and not fails else "FAILURES")
sys.exit(1 if fails else 0)
