"""Four claims about cofactor data, each rederived from the paper's own definitions.

Four claims, verified independently from the definitions.  Every object is built from
eq:Adef, eq:dexplicit, eq:capmatrix
and eq:cofactor by full permutation expansion over integer coefficients.

  A  SCALAR RECONSTRUCTION.  With deg h_k = k, put delta_j = deg C_j(X) and
     tau_j = wt_{k^2}(C_j(X)).  Then the ordered pairs (delta_j, tau_j) for
     j = 0..n determine X up to translation, via
         rho_j     = (Delta_j + S_j/Delta_j) / 2
         o_{j-1}   = 1 + (S_j/Delta_j - Delta_j) / 2
     where Delta_j = delta_j - delta_{j+1} and S_j = tau_j - tau_{j+1}.
     prop:stable-cofactor states it from the whole cofactor vector; this is the
     statement from the scalar pairs alone.

  B  EXACT SUPPORT CRITERION.  C_j(X) != 0 iff lambda_i > mu_{i-1} for every
     1 <= i < j -- no connectedness.  Hence C_n(X) != 0 iff X is connected, and
     C_1(X) = -s_Xbar needs no connectedness at all.  lem:cofactor-factorization
     states the criterion for connected and disconnected X alike.

  C  ONE EXTENSION IS INSUFFICIENT AT EVERY FIXED LENGTH.  For mu = (4a-2,2a-1,0),
     U_a = (6a-2,5a-1,2a)/mu and V_a = (6a-2,4a-1,3a)/mu are connected with
     s_{U_a.(a)} = s_{V_a.(a)} and s_{U_a} - s_{V_a} = h_{3a}h_{4a} - h_{2a}h_{5a}.

  D  QUANTITATIVE NO-BACKFLOW.  At square weight,
     F_i(l) - F_i(q) >= (l-q)(l+q-2i-1) for q < l <= n and i < v.
"""
from itertools import permutations, combinations
import functools, sys
print = functools.partial(print, flush=True)

def hm(k):
    if k < 0:  return {}
    if k == 0: return {(): 1}
    return {(k,): 1}
def mul(p, q):
    o = {}
    for a, ca in p.items():
        for b, cb in q.items():
            k = tuple(sorted(a + b)); o[k] = o.get(k, 0) + ca * cb
    return {k: v for k, v in o.items() if v}
def add(p, q):
    o = dict(p)
    for k, v in q.items(): o[k] = o.get(k, 0) + v
    return {k: v for k, v in o.items() if v}
def scale(p, c): return {k: v * c for k, v in p.items()} if c else {}
def det(rows):
    n = len(rows); acc = {}
    for perm in permutations(range(n)):
        sgn, pr = 1, list(perm)
        for i in range(n):
            for j in range(i + 1, n):
                if pr[i] > pr[j]: sgn = -sgn
        t = {(): 1}
        for i, j in enumerate(perm):
            t = mul(t, rows[i][j])
            if not t: break
        if t: acc = add(acc, scale(t, sgn))
    return acc
sq = lambda k: k * k
def wto(p): return None if not p else min(sum(sq(e) for e in m) for m in p)
def degree(p):
    if not p: return None
    ds = {sum(m) for m in p}
    assert len(ds) == 1, f"cofactor not homogeneous: {ds}"
    return ds.pop()

def coords(lam, mu):
    n = len(lam); L = lam[0]
    return ([L - lam[i] + i for i in range(n)],
            [0] + [L - mu[j - 1] + j - 1 for j in range(1, n + 1)])
def cofactors(lam, mu):
    A, d = coords(lam, mu); n = len(lam)
    M = [[hm(d[j] - A[i]) for j in range(n + 1)] for i in range(n)]
    return [scale(det([[M[i][t] for t in range(n + 1) if t != j] for i in range(n)]),
                  (-1) ** j) for j in range(n + 1)]
def schur(lam, mu):
    rows = [(lam[i], (list(mu) + [0] * len(lam))[i]) for i in range(len(lam))]
    rows = [(a, b) for a, b in rows if a - b > 0]
    if not rows: return {(): 1}
    n = len(rows)
    return det([[hm(rows[i][0] - rows[j][1] - i + j) for j in range(n)] for i in range(n)])
def extend_ne(lam, mu, a):
    return [lam[0] + a - 1] + list(lam), [lam[0] - 1] + list(mu)

def skews(maxcells, maxrows):
    """every skew diagram lam/mu, up to translation (mu_last = 0), with all rows
    nonempty; connected and disconnected alike"""
    out = []
    for n in range(1, maxrows + 1):
        def rec(lam, mu):
            if len(lam) == n:
                if mu[-1] != 0: return
                if sum(lam[i] - mu[i] for i in range(n)) <= maxcells:
                    out.append((list(lam), list(mu)))
                return
            hi = lam[-1] if lam else maxcells
            for L in range(1, hi + 1):
                lo = mu[-1] if mu else 0
                for Mv in range(0, min(L, (mu[-1] if mu else maxcells)) + 1):
                    if mu and Mv > mu[-1]: continue
                    if L - Mv < 1: continue
                    rec(lam + [L], mu + [Mv])
        rec([], [])
    return out

def connected(lam, mu):
    mu = list(mu) + [0] * (len(lam) - len(mu))
    return all(lam[i] > mu[i - 1] for i in range(1, len(lam)))

# ------------------------------------------------------------------ CLAIM B
print("=== B  exact cofactor-support criterion, connected AND disconnected ===")
# skews(13,5) enumerates 651,837 presentations -- three orders of magnitude more
# than a first estimate of it, and far past what permutation-expansion
# determinants can absorb.  These are bounded REGRESSION populations, chosen so
# each claim runs in seconds; the universal statements rest on the written
# proofs, not on these counts.  A stride keeps the sample spread over the
# enumeration order rather than clustered at its start.
ALL = skews(10, 4)
pop = ALL[::max(1, len(ALL) // 4000)]
nB = ncrit = nconn = 0
for lam, mu in pop:
    n = len(lam); mud = list(mu) + [0] * n
    C = cofactors(lam, mu)
    for j in range(n + 1):
        crit = all(lam[i] > mud[i - 1] for i in range(1, j))
        assert (C[j] != {}) == crit, ("B fails", lam, mu, j, crit, C[j] != {})
        nB += 1
        ncrit += crit
    # C_n != 0 iff connected
    assert (C[n] != {}) == connected(lam, mu), ("B/connected fails", lam, mu)
    nconn += connected(lam, mu)
    # C_1 = -s_Xbar with NO connectedness hypothesis
    bar = schur(lam[1:], mu[1:]) if n > 1 else {(): 1}
    assert C[1] == scale(bar, -1), ("C_1 = -s_Xbar fails", lam, mu)
print(f"  {len(pop)} presentations sampled from {len(ALL)} of size<=10, rows<=4; {nconn} connected, {len(pop)-nconn} NOT")
print(f"  {nB} cofactor tests: nonvanishing matches the prefix criterion exactly ({ncrit} nonzero)")
print(f"  C_n != 0 iff connected: holds on all {len(pop)}")
print(f"  C_1 = -s_Xbar: holds on all {len(pop)}, connectedness never used")

# ------------------------------------------------------------------ CLAIM A
print()
print("=== A  scalar reconstruction from (deg C_j, wt_{k^2} C_j) ===")
conn = [(l, m) for l, m in ALL if connected(l, m)]
seen = {}
nA = 0
for lam, mu in conn:
    n = len(lam); mud = list(mu) + [0] * n
    C = cofactors(lam, mu)
    delta = [degree(C[j]) for j in range(n + 1)]
    tau   = [wto(C[j])    for j in range(n + 1)]
    rho = [lam[i] - mud[i] for i in range(n)]
    ov  = [lam[i + 1] - mud[i] for i in range(n - 1)]     # o_i, i = 0..n-2
    # reconstruct
    rrho, rov = [], []
    for j in range(n):
        D = delta[j] - delta[j + 1]; S = tau[j] - tau[j + 1]
        assert D > 0, ("Delta must be positive", lam, mu, j, D)
        assert S % D == 0, ("S/Delta must be an integer", lam, mu, j, S, D)
        rrho.append((D + S // D) // 2)
        if j >= 1: rov.append(1 + (S // D - D) // 2)
    assert rrho == rho, ("rho mismatch", lam, mu, rrho, rho)
    assert rov == ov,   ("overlap mismatch", lam, mu, rov, ov)
    # the scalar data must SEPARATE distinct diagrams up to translation
    key = tuple(zip(delta, tau))
    if key in seen:
        assert seen[key] == (tuple(rho), tuple(ov)), ("collision", lam, mu, seen[key])
    seen[key] = (tuple(rho), tuple(ov))
    nA += 1
print(f"  {nA} connected presentations: (rho, o) recovered exactly from 2(n+1) integers")
print(f"  {len(seen)} distinct scalar signatures, zero collisions across distinct profiles")

# ------------------------------------------------------------------ CLAIM C
print()
print("=== C  one positive extension is insufficient at EVERY fixed length a ===")
for a in range(1, 8):
    mu = [4 * a - 2, 2 * a - 1, 0]
    U  = [6 * a - 2, 5 * a - 1, 2 * a]
    V  = [6 * a - 2, 4 * a - 1, 3 * a]
    assert connected(U, mu) and connected(V, mu), ("not connected", a)
    eU = schur(*extend_ne(U, mu, a)); eV = schur(*extend_ne(V, mu, a))
    assert eU == eV, ("extensions must agree", a)
    dif = add(schur(U, mu), scale(schur(V, mu), -1))
    want = {(3 * a, 4 * a): 1, (2 * a, 5 * a): -1}
    assert dif == want, ("parent difference wrong", a, dif, want)
    print(f"  a={a}: U={tuple(U)}/{tuple(mu)}  V={tuple(V)}/{tuple(mu)}  "
          f"s_(U.({a}))=s_(V.({a})) yet s_U-s_V = h_{3*a}h_{4*a}-h_{2*a}h_{5*a}")

# ------------------------------------------------------------------ CLAIM D
print()
print("=== D  quantitative no-backflow margin  F_i(l)-F_i(q) >= (l-q)(l+q-2i-1) ===")
# Claim D pairs boards, so it is QUADRATIC in the population where the others
# are linear.  It gets its own smaller population: the margin is an inequality
# between two grids, so what it needs is many DISTINCT (v, n, grid) shapes, not
# many diagrams.
import collections
groups = collections.defaultdict(list)
for lam, mu in conn:
    mud = list(mu) + [0] * len(lam)
    key = (tuple(mu), tuple(sorted(lam[i] - mud[i] for i in range(len(lam)))))
    groups[key].append((lam, mu))
cand = [(x, y) for g in groups.values() if len(g) > 1
                for x, y in combinations(g, 2)]
print(f"  (claim D: {len(conn)} connected diagrams give {len(cand)} same-mu, "
      f"same-row-length pairs in {sum(1 for g in groups.values() if len(g)>1)} groups)")
pairs = tested = 0
for (lam, mu), (lam2, mu2) in cand:
        A1, d1 = coords(lam, mu); A2, d2 = coords(lam2, mu2)
        if d1 != d2: continue
        n = len(lam)
        v = next((i for i in range(n) if A1[i] != A2[i]), None)
        if v is None or v < 1: continue
        C1, C2 = cofactors(lam, mu), cofactors(lam2, mu2)
        G = [add(C1[j], scale(C2[j], -1)) for j in range(n + 1)]
        al = [None if not G[j] else wto(G[j]) + sq(d1[j]) for j in range(n + 1)]
        q = v + 1
        if al[q] is None: continue
        pairs += 1
        F = lambda i, j: al[j] + sq(d1[j] - A1[i]) - sq(d1[j])
        for i in range(v):
            for l in range(q + 1, n + 1):
                if al[l] is None: continue
                lhs = F(i, l) - F(i, q); rhs = (l - q) * (l + q - 2 * i - 1)
                assert lhs >= rhs, ("D fails", lam, lam2, i, l, lhs, rhs)
                tested += 1
print(f"  {pairs} defect pairs on a common grid with equal row lengths, {tested} (i,l) comparisons")
assert tested > 0, "the margin check must not be vacuous"
print(f"  the bound holds at every one; qualitative no-backflow F_i(l) > F_i(q) follows")
print()
print("ALL PASS")
