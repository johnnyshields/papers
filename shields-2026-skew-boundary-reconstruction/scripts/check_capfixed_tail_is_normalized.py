"""thm:cap-fixed-rigidity's tail sentence compares normalized actions, not valuations.

The theorem closes: "Every later positive coordinate has normalized action strictly
larger than alpha_{v+1}^omega."  Its proof delivers

    alpha_ell^omega > alpha_{v+1}^omega ,          alpha_j^omega = wto(G_j) + omega(d_j),

a statement about the NORMALIZED ACTION.  Comparing the raw valuation wto(G_ell) against
alpha_{v+1}^omega would be a different statement: alpha carries the +omega(d_j) shift.

This check builds the k = 2 member of the ratio family of subsec:locus-family
from the paper's own definitions -- eq:Adef, eq:dexplicit, eq:capmatrix,
eq:cofactor, eq:alpha-general, square weight -- and evaluates both readings.
The normalized reading holds; the raw-valuation reading FAILS, so the two are not
synonyms.
"""
from itertools import permutations
from fractions import Fraction

# ---- polynomials in h_1, h_2, ... : dict {sorted tuple of subscripts: coeff}
def hmono(k):
    if k < 0:  return {}                      # h_k = 0 for k < 0
    if k == 0: return {(): 1}                 # h_0 = 1
    return {(k,): 1}

def pmul(p, q):
    out = {}
    for a, ca in p.items():
        for b, cb in q.items():
            key = tuple(sorted(a + b))
            out[key] = out.get(key, 0) + ca * cb
    return {k: v for k, v in out.items() if v != 0}

def padd(p, q):
    out = dict(p)
    for k, v in q.items():
        out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}

def pscale(p, c):
    return {k: v * c for k, v in p.items()} if c else {}

def det(rows):
    """permutation expansion; rows is a list of lists of polynomials"""
    n = len(rows)
    acc = {}
    for perm in permutations(range(n)):
        sgn = 1
        pr = list(perm)
        for i in range(n):
            for j in range(i + 1, n):
                if pr[i] > pr[j]: sgn = -sgn
        term = {(): 1}
        for i, j in enumerate(perm):
            term = pmul(term, rows[i][j])
            if not term: break
        if term: acc = padd(acc, pscale(term, sgn))
    return acc

def wto(p, omega):
    """eq:alpha-general: wto(monomial) = sum omega(eta_r); wto(f) = min over terms"""
    if not p: return None                     # wto(0) = +infinity
    return min(sum(omega(e) for e in mono) for mono in p)

def coords(lam, mu):
    n = len(lam); L = lam[0]
    A = [L - lam[i] + i for i in range(n)]
    d = [0] + [L - mu[j - 1] + j - 1 for j in range(1, n + 1)]
    return A, d

def cofactors(lam, mu):
    A, d = coords(lam, mu)
    n = len(lam)
    M = [[hmono(d[j] - A[i]) for j in range(n + 1)] for i in range(n)]
    C = []
    for j in range(n + 1):
        sub = [[M[i][t] for t in range(n + 1) if t != j] for i in range(n)]
        C.append(pscale(det(sub), (-1) ** j))
    return C, A, d

sq = lambda k: k * k

# ---- the k = 2 member of subsec:locus-family, built from the printed recipe
k = 2
N = 2 * k + 2
mu = list(range(N - 1, -1, -1))
rhoA = [2] + [2] * k + [3] * k + [2]
rhoB = [2] + [3] * k + [2] * k + [2]
lamA = [mu[i] + rhoA[i] for i in range(N)]
lamB = [mu[i] + rhoB[i] for i in range(N)]
assert all(lamA[i] >= lamA[i + 1] for i in range(N - 1)), lamA
assert all(lamB[i] >= lamB[i + 1] for i in range(N - 1)), lamB
print(f"k = {k}:  mu = {tuple(mu)}")
print(f"          lambda(A) = {tuple(lamA)}   rho(A) = {tuple(rhoA)}")
print(f"          lambda(B) = {tuple(lamB)}   rho(B) = {tuple(rhoB)}")

CA, AA, d = cofactors(lamA, mu)
CB, AB, dB = cofactors(lamB, mu)
assert d == dB, "the two parents must share the cap grid"
G = [padd(CA[j], pscale(CB[j], -1)) for j in range(N + 1)]

v = next(i for i in range(N) if AA[i] != AB[i])
q = v + 1
print(f"          A^A = {tuple(AA)}")
print(f"          A^B = {tuple(AB)}")
print(f"          d   = {tuple(d)}      first changed row v = {v}, q = {q}")
print()

nu    = [wto(G[j], sq) for j in range(N + 1)]
alpha = [None if nu[j] is None else nu[j] + sq(d[j]) for j in range(N + 1)]
print(f"{'j':>3} {'d_j':>4} {'G_j':>6} {'wto(G_j)':>9} {'alpha_j':>8}")
for j in range(N + 1):
    print(f"{j:3} {d[j]:4} {'0' if not G[j] else 'nonzero':>6} "
          f"{'inf' if nu[j] is None else nu[j]:>9} {'inf' if alpha[j] is None else alpha[j]:>8}")
print()

aq = alpha[q]
later = [j for j in range(q + 1, N + 1) if G[j]]
print(f"alpha_q = alpha_{q} = {aq};  later positive supported coordinates: {later}")
print()
print("=== the two readings of the closing sentence ===")
norm_ok, raw_ok = True, True
for j in later:
    n_ok = alpha[j] > aq
    r_ok = nu[j] > aq
    norm_ok &= n_ok; raw_ok &= r_ok
    print(f"  j={j}: normalized  alpha_{j} = {alpha[j]:3} > {aq}  -> {n_ok}"
          f"      raw  wto(G_{j}) = {nu[j]:3} > {aq}  -> {r_ok}")
print()
assert later, "the family must have a later positive coordinate, or the check is vacuous"
assert norm_ok, "the NORMALIZED reading must hold -- it is what the proof delivers"
assert not raw_ok, ("the RAW-VALUATION reading must FAIL somewhere, or the wording "
                    "is a harmless synonym and there is nothing to fix")
bad = [j for j in later if not nu[j] > aq]
print(f"VERDICT: the normalized reading holds at every later coordinate.")
print(f"         the raw-valuation reading FAILS at j = {bad} "
      f"(wto(G_{bad[0]}) = {nu[bad[0]]} is not > alpha_{q} = {aq}).")
print(f"         So 'valuation' in the closing sentence must read 'normalized action'.")
print()
print("ALL PASS")
