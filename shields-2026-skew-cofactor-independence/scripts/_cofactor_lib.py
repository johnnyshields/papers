"""Exact polynomial Jacobi-Trudi cofactors and units over Z[h_1,h_2,...].

Import-only module.  Polynomials are dicts  monomial -> int,  a monomial being a sorted tuple of
POSITIVE generator indices (h_0 = 1 is dropped, h_j = 0 for j < 0 kills the term).  Every determinant is
expanded over all permutations, so every polynomial here is exact; ranks are exact flint fmpz_mat ranks.
"""
import itertools
from collections import defaultdict
import flint


def perm_sign(p):
    s = 1
    p = list(p)
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]
            p[i], p[j] = p[j], p[i]
            s = -s
    return s


_PERMS = {}


def perms(m):
    if m not in _PERMS:
        _PERMS[m] = [(p, perm_sign(p)) for p in itertools.permutations(range(m))]
    return _PERMS[m]


def det_poly(rows, cols):
    """det (h_{r-c})_{r in rows, c in cols} as a dict (rows, cols are sequences of ints, same length)."""
    m = len(rows)
    out = defaultdict(int)
    if m == 0:
        out[()] = 1
        return dict(out)
    for p, s in perms(m):
        mon = []
        ok = True
        for i in range(m):
            d = rows[i] - cols[p[i]]
            if d < 0:
                ok = False
                break
            if d > 0:
                mon.append(d)
        if ok:
            out[tuple(sorted(mon))] += s
    return {k: v for k, v in out.items() if v}


def cofactors(A, B):
    """signed cofactors D[i][j] (0-based) of M=(h_{a_i-b_j})."""
    n = len(A)
    D = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            P = det_poly([A[r] for r in range(n) if r != i], [B[c] for c in range(n) if c != j])
            s = -1 if (i + j) % 2 else 1
            D[i][j] = {k: s * v for k, v in P.items()}
    return D


def pmul_mon(P, extra):
    """P * prod h_e (e in extra, positive only; any negative kills)."""
    ex = []
    for e in extra:
        if e < 0:
            return {}
        if e > 0:
            ex.append(e)
    return {tuple(sorted(k + tuple(ex))): v for k, v in P.items()}


def padd(P, Q, c=1):
    out = dict(P)
    for k, v in Q.items():
        out[k] = out.get(k, 0) + c * v
        if out[k] == 0:
            del out[k]
    return out


def rank_of(polys):
    """exact rank over Q of a list of polynomial dicts."""
    idx = {}
    for P in polys:
        for k in P:
            if k not in idx:
                idx[k] = len(idx)
    if not idx:
        return 0
    M = flint.fmpz_mat(len(polys), len(idx))
    for r, P in enumerate(polys):
        for k, v in P.items():
            M[r, idx[k]] = v
    return M.rank()


def relation_space(polys):
    """basis (list of fmpq lists) of {c : sum c_r P_r = 0}."""
    idx = {}
    for P in polys:
        for k in P:
            idx.setdefault(k, len(idx))
    m = len(polys)
    if not idx:
        return [[1 if r == s else 0 for r in range(m)] for s in range(m)]
    MT = flint.fmpz_mat(len(idx), m)
    for r, P in enumerate(polys):
        for k, v in P.items():
            MT[idx[k], r] = v
    X, nullity = MT.nullspace()
    basis = [[X[r, c] for r in range(m)] for c in range(nullity)]
    for v in basis:  # exact check
        tot = {}
        for r, P in enumerate(polys):
            if v[r]:
                for k, c in P.items():
                    tot[k] = tot.get(k, 0) + int(v[r]) * c
        assert not any(tot.values())
    return basis


def is_symmetric(A, B):
    N = A[0]
    n = len(A)
    return all(A[i] + B[n - 1 - i] == N for i in range(n))


def dense_cores(n, Nmax, Nmin=None):
    """every normalized dense core of order n: a1=N, b_n=0, strict decreasing, a_n > b_1, N <= Nmax."""
    if Nmin is None:
        Nmin = 2 * n - 1
    for N in range(Nmin, Nmax + 1):
        # choose b_1 > ... > b_{n-1} > 0 and a_2 > ... > a_n > b_1, a_2 < N
        for Bs in itertools.combinations(range(1, N), n - 1):
            B = tuple(sorted(Bs, reverse=True)) + (0,)
            b1 = B[0]
            for As in itertools.combinations(range(b1 + 1, N), n - 1):
                A = (N,) + tuple(sorted(As, reverse=True))
                yield A, B


def connected_cores(n, Nmax):
    """normalized strict lists, connected (profile condition) but NOT dense (a_n <= b_1); for controls."""
    for N in range(n, Nmax + 1):
        for Bs in itertools.combinations(range(1, N), n - 1):
            B = tuple(sorted(Bs, reverse=True)) + (0,)
            for As in itertools.combinations(range(1, N), n - 1):
                A = (N,) + tuple(sorted(As, reverse=True))
                if A[-1] > B[0]:
                    continue
                # connected: r_i = a_i - b_i > 0, s_i = a_{i+1}-b_i >= 0 (and < min(r_i,r_{i+1}) automatic by strictness)
                if all(A[i] > B[i] for i in range(n)) and all(A[i + 1] >= B[i] for i in range(n - 1)):
                    yield A, B


def units(A, B, D=None):
    """U_z for z in Omega_C = {1..N-1} minus (A u B); returns (Omega list, list of dicts)."""
    n = len(A)
    N = A[0]
    if D is None:
        D = cofactors(A, B)
    S = set(A) | set(B)
    Om = [z for z in range(1, N) if z not in S]
    Us = []
    for z in Om:
        U = {}
        for i in range(n):
            if A[i] <= z:
                continue
            for j in range(n):
                if B[j] >= z:
                    continue
                U = padd(U, pmul_mon(D[i][j], (A[i] - z, z - B[j])))
        Us.append(U)
    return Om, Us
