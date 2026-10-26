"""Exact h-polynomial algebra and the cap-cofactor vector.

Every claim in this problem is an identity in Z[h_1, h_2, ...], so an
h-polynomial is a dict {sorted exponent tuple: integer coefficient} throughout
and no floating point appears anywhere.  h_0 = 1 contributes the empty tuple;
h_{<0} = 0 is the empty dict, which is what makes a Jacobi-Trudi term drop out
rather than merely vanish numerically.

The cap-cofactor vector C(A) is the Laplace expansion of the JT determinant of
A.(k) along its cap row.  It does not depend on k -- that independence is the
whole reason the vector exists -- so it is computed once from the symbolic cap
and reused for every r and a.
"""
from collections import defaultdict
from itertools import permutations


def pmul(p, q):
    out = defaultdict(int)
    for a, ca in p.items():
        for b, cb in q.items():
            out[tuple(sorted(a + b, reverse=True))] += ca * cb
    return {k: v for k, v in out.items() if v}


def padd(p, q, sign=1):
    out = defaultdict(int, p)
    for k, v in q.items():
        out[k] += sign * v
    return {k: v for k, v in out.items() if v}


def h(j):
    """h_j as a polynomial; h_0 = 1, h_{<0} = 0."""
    if j < 0:
        return {}
    if j == 0:
        return {(): 1}
    return {(j,): 1}


def det_h(entries):
    """Determinant of a matrix of h-INDICES, as an exact h-polynomial."""
    n = len(entries)
    if n == 0:
        return {(): 1}
    out = {}
    for pi in permutations(range(n)):
        term = {(): 1}
        ok = True
        for i, j in enumerate(pi):
            f = h(entries[i][j])
            if not f:
                ok = False
                break
            term = pmul(term, f)
        if not ok:
            continue
        inv = sum(pi[i] > pi[j] for i in range(n) for j in range(i + 1, n))
        out = padd(out, term, -1 if inv % 2 else 1)
    return out


def jt_entries(sh):
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    n = len(lam)
    return [[lam[i] - mu[j] - i + j for j in range(n)] for i in range(n)]


def s_poly(sh):
    if not sh[0]:
        return {(): 1}
    return det_h(jt_entries(sh))


def cofactors(sh):
    """{d: C_d(A)} from Laplace expansion of A.(k) along its cap row.

    Independent of k, so computed from the (n+1)x(n+1) JT matrix of A.(k) with
    a symbolic cap: the first row's entry in column j is h_{k+d} with d the
    shift below.
    """
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    n = len(lam)
    L = lam[0]
    lamp = [None] + list(lam)             # row 0's outer part carries the symbol k
    mup = [L - 1] + list(mu)
    shifts = [(L - 1) - mup[j] + j for j in range(n + 1)]
    assert shifts[0] == 0
    out = {}
    for j in range(n + 1):
        cols = [c for c in range(n + 1) if c != j]
        ent = [[lamp[i] - mup[c] - i + c for c in cols] for i in range(1, n + 1)]
        cof = det_h(ent)
        if not cof:
            continue
        sgn = -1 if j % 2 else 1
        out[shifts[j]] = {k_: sgn * v for k_, v in cof.items()}
    return out


def Pk(G, k):
    """P_k(F) = sum_d F_d h_{k+d}, the shifted cofactor combination."""
    out = {}
    for d, p in G.items():
        out = padd(out, pmul(p, h(k + d)))
    return {m: c for m, c in out.items() if c}
