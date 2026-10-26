"""Profiles, enumeration, Jacobi-Trudi evaluation and exact Jacobi-Trudi polynomials.

Conventions.  A connected skew diagram is identified up to translation with its profile
(r_1, ..., r_n; g_1, ..., g_{n-1}): row lengths from top to bottom, and g_i equal to the number of
columns shared by rows i and i+1, minus one.  The profile is legal exactly when every r_i >= 1 and
0 <= g_i < min(r_i, r_{i+1}).  The beta lists, normalized by y_n = 0, are

    x_n = r_n,   y_i = x_{i+1} - g_i,   x_i = y_i + r_i,

so that x_i = lambda_i - i and y_i = mu_i - i up to a common shift, and the Jacobi-Trudi formula reads
s_F = det(h_{x_i - y_j}) with h_0 = 1 and h_k = 0 for k < 0.  Row i occupies the contents
y_i, ..., x_i - 1, so the diagram has N_F = x_1 = sum(r) - sum(g) diagonals.  Cells are (i, j) with i
increasing to the south and j to the east; the content of (i, j) is j - i.

Three instruments for s_F are provided and kept independent of one another:
  eval_batch     numpy evaluation of many determinants at one point of F_p, p = 2^31 - 1, by
                 division-free elimination (a zero pivot is redone by exact pivoted elimination);
  jt_poly        the exact polynomial in Z[h_1, h_2, ...], by Laplace expansion along rows with
                 memoization on the set of used columns;
  jt_poly_flint  the exact polynomial again, by fraction-free (Bareiss) elimination over
                 python-flint's fmpz_mpoly.
"""
import random
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import permutations

import numpy as np

P31 = (1 << 31) - 1


# ------------------------------------------------------------------------------------------ profiles
def betas(rows, gaps):
    n = len(rows)
    x, y = [0] * n, [0] * n
    x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return tuple(x), tuple(y)


def valid(rows, gaps):
    return (len(rows) >= 1 and len(gaps) == len(rows) - 1 and min(rows) >= 1
            and all(0 <= g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps)))


def rot(F):
    """Rotation through 180 degrees reverses the rows and the gaps."""
    return tuple(reversed(F[0])), tuple(reversed(F[1]))


def canon(F):
    return min(F, rot(F))


def area(F):
    return sum(F[0])


def span(F):
    """Number of occupied diagonals."""
    return sum(F[0]) - sum(F[1])


def fmt(F):
    return '(' + ','.join(map(str, F[0])) + ';' + ','.join(map(str, F[1])) + ')'


def heights(F):
    """h[c] = number of cells on content c, c = 0..N_F-1 (content of the lowest diagonal is 0)."""
    x, y = betas(*F)
    h = [0] * x[0]
    for a, b in zip(x, y):
        for c in range(b, a):
            h[c] += 1
    return h


def cells(F):
    """Cell set (i, j), normalized to minimal row 0 and minimal column 0."""
    x, y = betas(*F)
    out = []
    for i, (a, b) in enumerate(zip(x, y)):
        for c in range(b, a):
            out.append((i, c + i))
    j0 = min(j for _, j in out)
    return frozenset((i, j - j0) for i, j in out)


def profile_of_cells(S):
    """Profile of a connected skew diagram given as a cell set (asserts legality)."""
    rows = defaultdict(list)
    for i, j in S:
        rows[i].append(j)
    ks = sorted(rows)
    assert ks == list(range(ks[0], ks[0] + len(ks))), 'empty row'
    iv = []
    for k in ks:
        lo, hi = min(rows[k]), max(rows[k])
        assert hi - lo + 1 == len(rows[k]), 'row is not an interval'
        iv.append((lo, hi))
    r = tuple(hi - lo + 1 for lo, hi in iv)
    g = tuple(iv[t + 1][1] - iv[t][0] for t in range(len(iv) - 1))
    assert valid(r, g), (r, g)
    return r, g


def transpose(F):
    return profile_of_cells(frozenset((j, i) for i, j in cells(F)))


def is_ribbon(F):
    return all(g == 0 for g in F[1])


# ------------------------------------------------------------------------------------------ enumeration
def compositions(N, n):
    if n == 1:
        yield (N,)
        return
    for first in range(1, N - n + 2):
        for rest in compositions(N - first, n - 1):
            yield (first,) + rest


def partitions(N, maxpart=None):
    if maxpart is None:
        maxpart = N
    if N == 0:
        yield ()
        return
    for p in range(min(N, maxpart), 0, -1):
        for rest in partitions(N - p, p):
            yield (p,) + rest


def distinct_permutations(parts):
    """Every distinct ordering of a multiset, in lexicographic order."""
    cnt = Counter(parts)
    keys = sorted(cnt)
    n = len(parts)
    out = []
    cur = []

    def rec():
        if len(cur) == n:
            out.append(tuple(cur))
            return
        for k in keys:
            if cnt[k]:
                cnt[k] -= 1
                cur.append(k)
                rec()
                cur.pop()
                cnt[k] += 1
    rec()
    return out


def gap_count(rows):
    t = 1
    for a, b in zip(rows, rows[1:]):
        t *= min(a, b)
    return t


def expand_gaps(row_seqs):
    """All profiles over the given row sequences (equal length n): arrays R (B, n), G (B, n-1), int8."""
    comps = np.array(row_seqs, dtype=np.int64)
    n = comps.shape[1]
    if n == 1:
        return comps.astype(np.int8), np.zeros((len(comps), 0), dtype=np.int8)
    rad = np.minimum(comps[:, :-1], comps[:, 1:])
    tot = np.prod(rad, axis=1)
    B = int(tot.sum())
    rep = np.repeat(np.arange(len(comps)), tot)
    start = np.concatenate([[0], np.cumsum(tot)[:-1]])
    local = np.arange(B, dtype=np.int64) - start[rep]
    R = comps[rep]
    rr = rad[rep]
    G = np.zeros((B, n - 1), dtype=np.int64)
    t = local
    for i in range(n - 2, -1, -1):
        G[:, i] = t % rr[:, i]
        t = t // rr[:, i]
    return R.astype(np.int8), G.astype(np.int8)


def profile_chunks_of_rowset(parts, target=400000):
    """Every connected profile whose row multiset is `parts`, in chunks of about `target` profiles."""
    buf, tot = [], 0
    for seq in distinct_permutations(parts):
        buf.append(seq)
        tot += gap_count(seq)
        if tot >= target:
            yield expand_gaps(buf)
            buf, tot = [], 0
    if buf:
        yield expand_gaps(buf)


def all_profiles(N):
    """Every connected profile of exactly N cells (pure Python generator)."""
    def gapseqs(rows, k):
        if k == len(rows) - 1:
            yield ()
            return
        for g in range(min(rows[k], rows[k + 1])):
            for t in gapseqs(rows, k + 1):
                yield (g,) + t
    for n in range(1, N + 1):
        for rows in compositions(N, n):
            for gaps in gapseqs(rows, 0):
                yield rows, gaps


def dp_counts(NMAX):
    """Number of connected profiles of each area 1..NMAX: f[a][r] counts profiles of area a whose
    last row has length r; appending a row of length r' to such a profile offers min(r, r') gaps."""
    f = [[0] * (NMAX + 1) for _ in range(NMAX + 1)]
    for r in range(1, NMAX + 1):
        f[r][r] = 1
    for a in range(1, NMAX + 1):
        for last in range(1, a + 1):
            if f[a][last]:
                for r in range(1, NMAX - a + 1):
                    f[a + r][r] += f[a][last] * min(last, r)
    return [sum(f[a]) for a in range(NMAX + 1)]


def shard_size(parts):
    """Number of connected profiles with row multiset `parts` (DP over the remaining multiset)."""
    keys = sorted(set(parts))
    start = tuple(Counter(parts)[k] for k in keys)

    @lru_cache(None)
    def f(state, last):
        if not any(state):
            return 1
        tot = 0
        for i, k in enumerate(keys):
            if state[i]:
                s = list(state)
                s[i] -= 1
                tot += (min(last, k) if last else 1) * f(tuple(s), k)
        return tot
    return f(start, 0)


# ------------------------------------------------------------------------------------------ modular evaluation
def make_point(seed, hmax):
    """A random point h_1..h_hmax in F_p^hmax, with h_0 = 1 in position 0."""
    rng = random.Random(seed)
    return np.array([1] + [rng.randrange(1, P31) for _ in range(hmax)], dtype=np.int64)


def betas_array(R, G):
    R = R.astype(np.int64)
    G = G.astype(np.int64)
    B, n = R.shape
    X = np.zeros((B, n), dtype=np.int64)
    Y = np.zeros((B, n), dtype=np.int64)
    X[:, -1] = R[:, -1]
    for i in range(n - 2, -1, -1):
        Y[:, i] = X[:, i + 1] - G[:, i]
        X[:, i] = Y[:, i] + R[:, i]
    return X, Y


def _powmod_vec(a, e):
    res = np.ones_like(a)
    base = a % P31
    while e:
        if e & 1:
            res = res * base % P31
        base = base * base % P31
        e >>= 1
    return res


def det_mod_exact(M, p=P31):
    """Determinant of an integer matrix modulo p by pivoted Gaussian elimination (pure Python)."""
    M = [[int(v) % p for v in row] for row in M]
    n = len(M)
    det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det = det * M[c][c] % p
        inv = pow(M[c][c], p - 2, p)
        for r in range(c + 1, n):
            f = M[r][c] * inv % p
            if f:
                M[r] = [(a - f * b) % p for a, b in zip(M[r], M[c])]
    return det % p


def eval_batch(R, G, h):
    """s_F at the point h (mod p) for every profile (row of R, G).  Division-free elimination: row r
    of the trailing block is replaced by piv * row_r - M[r, c] * row_c, which multiplies the
    determinant by piv^(n-1-c); the product of these factors is divided out once at the end.  Any
    profile meeting a zero pivot is recomputed by det_mod_exact."""
    X, Y = betas_array(R, G)
    B, n = X.shape
    out = np.zeros(B, dtype=np.int64)
    chunk = max(2000, 3000000 // (n * n))
    for s in range(0, B, chunk):
        Xc, Yc = X[s:s + chunk], Y[s:s + chunk]
        D = Xc[:, :, None] - Yc[:, None, :]
        M = np.where(D >= 0, h[np.clip(D, 0, None)], 0)
        b = len(Xc)
        bad = np.zeros(b, dtype=bool)
        den = np.ones(b, dtype=np.int64)
        run = np.ones(b, dtype=np.int64)
        for c in range(n - 1):
            piv = M[:, c, c].copy()
            bad |= piv == 0
            run = run * piv % P31
            den = den * run % P31
            low = M[:, c + 1:, c + 1:]
            M[:, c + 1:, c + 1:] = (piv[:, None, None] * low % P31
                                    - M[:, c + 1:, c:c + 1] * M[:, c:c + 1, c + 1:] % P31) % P31
        diag = np.ones(b, dtype=np.int64)
        for c in range(n):
            diag = diag * M[:, c, c] % P31
        det = diag * _powmod_vec(den, P31 - 2) % P31
        for k in np.nonzero(bad)[0]:
            Mk = [[int(h[d]) if d >= 0 else 0 for d in row] for row in D[k]]
            det[k] = det_mod_exact(Mk)
        out[s:s + chunk] = det
    return out


def eval_one(F, h):
    x, y = betas(*F)
    M = [[int(h[a - b]) if a - b >= 0 else 0 for b in y] for a in x]
    return det_mod_exact(M)


# ------------------------------------------------------------------------------------------ exact polynomials
def jt_poly_lists(x, y):
    """det(h_{x_i - y_j}) in Z[h_1, h_2, ...] as {monomial: coefficient}; a monomial is the weakly
    decreasing tuple of its indices (a partition).  Laplace expansion along rows, memoized on the
    set of used columns."""
    n = len(x)

    @lru_cache(None)
    def rec(i, used):
        if i == n:
            return {(): 1}
        acc = defaultdict(int)
        k = 0
        for j in range(n):
            if used >> j & 1:
                k += 1
                continue
            t = x[i] - y[j]
            if t < 0:
                continue
            sgn = -1 if (j - k) % 2 else 1
            for m, c in rec(i + 1, used | (1 << j)).items():
                mm = tuple(sorted(m + (t,), reverse=True)) if t > 0 else m
                acc[mm] += sgn * c
        return {m: c for m, c in acc.items() if c}
    return rec(0, 0)


def jt_poly(F):
    return jt_poly_lists(*betas(*F))


def poly_key(P):
    return tuple(sorted(P.items()))


_FLINT_CTX = {}


def jt_poly_flint(F):
    """The same determinant by Bareiss elimination over fmpz_mpoly; returned as {partition: coeff}."""
    import flint
    x, y = betas(*F)
    n = len(x)
    N = x[0]
    ctx = _FLINT_CTX.get(N)
    if ctx is None:
        ctx = flint.fmpz_mpoly_ctx.get(('h', N), 'lex')
        _FLINT_CTX[N] = ctx
    gens = ctx.gens()
    one = ctx.from_dict({(0,) * N: 1})
    zero = ctx.from_dict({})

    def ent(t):
        if t < 0:
            return zero
        if t == 0:
            return one
        return gens[t - 1]
    M = [[ent(x[i] - y[j]) for j in range(n)] for i in range(n)]
    sign = 1
    prev = one
    for c in range(n - 1):
        if M[c][c] == zero:
            sw = next((r for r in range(c + 1, n) if M[r][c] != zero), None)
            if sw is None:
                return {}
            M[c], M[sw] = M[sw], M[c]
            sign = -sign
        for r in range(c + 1, n):
            for k in range(c + 1, n):
                num = M[c][c] * M[r][k] - M[r][c] * M[c][k]
                q, rem = divmod(num, prev)
                assert rem == zero
                M[r][k] = q
            M[r][c] = zero
        prev = M[c][c]
    det = M[n - 1][n - 1] * sign
    out = {}
    for exps, c in det.to_dict().items():
        mono = []
        for idx in range(N - 1, -1, -1):
            mono += [idx + 1] * exps[idx]
        out[tuple(mono)] = int(c)
    return out


def dp_counts_self_rotational(NMAX):
    """Number of connected profiles of each area 1..NMAX equal to their own rotation (palindromic rows
    and gaps).  A half profile of area a ending in a row of length r (counted by the same DP as
    dp_counts) is closed either by a middle gap g < r against its mirror image (area 2a, r choices) or
    by a middle row m with gaps min(r, m) on both sides, mirrored (area 2a + m, min(r, m) choices)."""
    f = [[0] * (NMAX + 1) for _ in range(NMAX + 1)]
    for r in range(1, NMAX + 1):
        f[r][r] = 1
    for a in range(1, NMAX + 1):
        for last in range(1, a + 1):
            if f[a][last]:
                for r in range(1, NMAX - a + 1):
                    f[a + r][r] += f[a][last] * min(last, r)
    out = [0] * (NMAX + 1)
    for m in range(1, NMAX + 1):
        out[m] += 1                                  # a single row
    for a in range(1, NMAX + 1):
        for last in range(1, a + 1):
            c = f[a][last]
            if not c:
                continue
            if 2 * a <= NMAX:
                out[2 * a] += c * last
            for m in range(1, NMAX - 2 * a + 1):
                out[2 * a + m] += c * min(last, m)
    return out
