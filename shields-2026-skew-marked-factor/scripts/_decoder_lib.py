"""Shared primitives for `check_decoder_modes.py`, written from the definitions.

Conventions: a cell is (i, j), i increasing south, j east, content j - i, e = (1, 1).
Profile (r_1..r_n; g_1..g_{n-1}): rows top to bottom, g_i = overlap(row i, row i+1) - 1.
Interior D^- = {x in D : x + e in D}.  JT: s_{lam/mu} = det(h_{lam_i - mu_j - i + j}), h_0 = 1, h_<0 = 0.
delta_k = p_k^perp = sum_{j >= k} h_{j-k} d/dh_j ;  delta_k^0 = the same sum over j > k only.

Exact polynomials: python-flint fmpz_mpoly in h_1..h_N
(variable index t <-> h_{t+1}).  Modular evaluation is used ONLY to certify NONvanishing (a nonzero value of a
polynomial at a point proves the polynomial nonzero); zero claims are always decided exactly.
"""
import random
from functools import lru_cache

import flint

PR = (1 << 61) - 1


# ----------------------------------------------------------------------------- shapes
def cells_from_profile(rows, gaps):
    r = len(rows)
    start = [0] * r
    for i in range(r - 2, -1, -1):
        end_below = start[i + 1] + rows[i + 1] - 1
        start[i] = end_below - gaps[i]
    c0 = min(start)
    return frozenset((i, start[i] - c0 + t) for i in range(r) for t in range(rows[i]))


def normalize(cells):
    i0 = min(i for i, _ in cells)
    j0 = min(j for _, j in cells)
    return frozenset((i - i0, j - j0) for i, j in cells)


def profile_of(cells):
    rows = {}
    for i, j in cells:
        rows.setdefault(i, []).append(j)
    ks = sorted(rows)
    lens, gaps = [], []
    iv = []
    for k in ks:
        js = sorted(rows[k])
        assert js == list(range(js[0], js[-1] + 1))
        iv.append((js[0], js[-1]))
        lens.append(len(js))
    for a, b in zip(iv, iv[1:]):
        gaps.append(b[1] - a[0])          # overlap - 1
    return tuple(lens), tuple(gaps)


def lam_mu(cells):
    rows = {}
    for i, j in cells:
        rows.setdefault(i, []).append(j)
    ks = sorted(rows)
    c0 = min(j for _, j in cells)
    lam = [max(rows[k]) - c0 + 1 for k in ks]
    mu = [min(rows[k]) - c0 for k in ks]
    return lam, mu


def jt_index_matrix(cells):
    lam, mu = lam_mu(cells)
    r = len(lam)
    return [[lam[i] - mu[j] - i + j for j in range(r)] for i in range(r)]


def interior(cells):
    return frozenset((i, j) for (i, j) in cells if (i + 1, j + 1) in cells)


def is_discrete(S):
    for (i, j) in S:
        if (i + 1, j) in S or (i, j + 1) in S:
            return False
    return True


def span(cells):
    cs = [j - i for i, j in cells]
    return max(cs) - min(cs) + 1


def rotate(cells):
    return normalize(frozenset((-i, -j) for i, j in cells))


# ----------------------------------------------------------------------------- enumeration
def profiles_gap01(area):
    """All connected profiles of the given area with every gap in {0, 1}."""
    out = []

    def rec(rows, gaps, rem):
        if rem == 0:
            out.append((tuple(rows), tuple(gaps)))
            return
        for L in range(1, rem + 1):
            if not rows:
                rec([L], [], rem - L)
                continue
            for g in (0, 1):
                if g <= min(rows[-1], L) - 1:
                    rows.append(L)
                    gaps.append(g)
                    rec(rows, gaps, rem - L)
                    rows.pop()
                    gaps.pop()

    rec([], [], area)
    return out


def all_connected_profiles(area):
    out = []

    def rec(rows, gaps, rem):
        if rem == 0:
            out.append((tuple(rows), tuple(gaps)))
            return
        for L in range(1, rem + 1):
            if not rows:
                rec([L], [], rem - L)
                continue
            for g in range(0, min(rows[-1], L)):
                rows.append(L)
                gaps.append(g)
                rec(rows, gaps, rem - L)
                rows.pop()
                gaps.pop()

    rec([], [], area)
    return out


def positive_discrete_profiles(area):
    res = []
    for rows, gaps in profiles_gap01(area):
        D = cells_from_profile(rows, gaps)
        I = interior(D)
        if I and is_discrete(I):
            res.append((rows, gaps))
    return res


# ----------------------------------------------------------------------------- exact polynomials
class Ring:
    def __init__(self, N):
        self.N = N
        self.ctx = flint.fmpz_mpoly_ctx.get(('h', N), 'deglex')
        self.g = self.ctx.gens()
        self.one = self.ctx.from_dict({(0,) * N: 1})
        self.zero = self.ctx.from_dict({})

    def h(self, k):
        if k == 0:
            return self.one
        if k < 0:
            return self.zero
        if k > self.N:
            raise ValueError("h index beyond ring")
        return self.g[k - 1]


def det_poly(M, R):
    """Determinant of a matrix of h-indices, by memoized Laplace expansion on the first row."""
    r = len(M)
    memo = {}

    def rec(i, cols):
        if i == r:
            return R.one
        key = (i, cols)
        if key in memo:
            return memo[key]
        acc = R.zero
        for pos, j in enumerate(cols):
            e = M[i][j]
            if e < 0:
                continue
            sub = rec(i + 1, cols[:pos] + cols[pos + 1:])
            term = R.h(e) * sub
            acc = acc - term if (pos & 1) else acc + term
        memo[key] = acc
        return acc

    return rec(0, tuple(range(r)))


def schur_poly(cells, R):
    return det_poly(jt_index_matrix(cells), R)


def delta(f, k, R, strict=False):
    """delta_k f = sum_{j >= k} h_{j-k} df/dh_j ; strict=True drops j = k (delta_k^0)."""
    acc = R.zero
    for j in range(k + (1 if strict else 0), R.N + 1):
        d = f.derivative(j - 1)
        if not d.is_zero():
            acc = acc + R.h(j - k) * d
    return acc


def top_degree_part(f, d, R):
    dd = {m: c for m, c in f.to_dict().items() if sum(m) == d}
    return R.ctx.from_dict(dd)


def h1_coefficients(f, R):
    """Dict v -> coefficient polynomial of h_1^v (as a polynomial without h_1)."""
    out = {}
    for m, c in f.to_dict().items():
        v = m[0]
        mm = (0,) + tuple(m[1:])
        out.setdefault(v, {})
        out[v][mm] = out[v].get(mm, 0) + c
    return {v: R.ctx.from_dict(dd) for v, dd in out.items()}


# ----------------------------------------------------------------------------- modular evaluation
def det_mod(A, P=PR):
    A = [row[:] for row in A]
    n = len(A)
    det = 1
    for c in range(n):
        piv = None
        for r_ in range(c, n):
            if A[r_][c] % P:
                piv = r_
                break
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det = det * A[c][c] % P
        inv = pow(A[c][c], P - 2, P)
        for r_ in range(c + 1, n):
            if A[r_][c] % P:
                f = A[r_][c] * inv % P
                for k in range(c, n):
                    A[r_][k] = (A[r_][k] - f * A[c][k]) % P
    return det % P


def eval_delta_mod(M, k, hv, strict=False, P=PR):
    """(s(h), delta_k s(h)) mod P for the JT index matrix M at the point hv (hv[0] = 1).
    delta_k s = sum_i det(M with row i replaced by the row of d h_{e} = h_{e-k} [e >= k (or > k)])."""
    r = len(M)

    def hval(e):
        return hv[e] if e >= 0 else 0

    def dval(e):
        if e < k or (strict and e == k):
            return 0
        return hv[e - k]

    A = [[hval(M[i][j]) for j in range(r)] for i in range(r)]
    s = det_mod(A, P)
    tot = 0
    for i in range(r):
        B = [row[:] for row in A]
        B[i] = [dval(M[i][j]) for j in range(r)]
        if any(B[i]):
            tot = (tot + det_mod(B, P)) % P
    return s, tot


def random_point(N, rng, P=PR):
    return [1] + [rng.randrange(1, P) for _ in range(N + 2)]


# ----------------------------------------------------------------------------- blocks
def gap_one_blocks(rows, gaps):
    """Maximal runs of rows joined by gap-one adjacencies (split at zero gaps)."""
    blocks = [[0]]
    for i, g in enumerate(gaps):
        if g == 1:
            blocks[-1].append(i + 1)
        else:
            blocks.append([i + 1])
    out = []
    for b in blocks:
        out.append((tuple(rows[i] for i in b), tuple(gaps[i] for i in b[:-1])))
    return out
