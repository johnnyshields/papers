"""Shared exact machinery for `check_readout_flint.py`.

Independent of `schur_tools.py`.  Instruments:
  * python-flint fmpz_mpoly for exact polynomial arithmetic, gcd and factorization
    (a different instrument from the sympy polynomials of `schur_tools.py`);
  * my own Jacobi-Trudi determinant (row-by-row subset expansion, h_0 = 1, h_<0 = 0);
  * my own skewing operator delta_k = p_k^perp = sum_{j>=k} h_{j-k} d/dh_j, cross-checked
    against an independent Murnaghan-Nakayama rim-hook route (mn_delta);
  * the composition engine _composition_engine.py for marks,
    composition and factorizations (with Hypothesis I).  An EMPTY OUTER is never composed.

Profile convention: (r_1..r_n; g_1..g_{n-1}), rows top to bottom, rows descending
to the left, g_i = (columns shared by rows i and i+1) - 1.
Cell convention (engine): (i, j), i increasing SOUTH, j EAST, content j - i.
"""
import os
import sys
import importlib.util
import random
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from math import gcd, factorial

import flint

HERE = os.path.dirname(os.path.abspath(__file__))
SKEW = os.path.dirname(HERE)
ENGINE_PATH = os.path.join(HERE, '_composition_engine.py')


def _load_engine():
    spec = importlib.util.spec_from_file_location('engine11_v1', ENGINE_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ENG = _load_engine()

# ----------------------------------------------------------------------------------------
# polynomials in the free h-alphabet
# ----------------------------------------------------------------------------------------
NV = 160
CTX = flint.fmpz_mpoly_ctx.get(tuple('h%d' % i for i in range(1, NV + 1)), 'deglex')
GENS = CTX.gens()
ZERO = CTX.from_dict({})
ONE = CTX.from_dict({(0,) * NV: 1})


def h(k):
    if k < 0:
        return ZERO
    if k == 0:
        return ONE
    assert k <= NV, 'raise NV'
    return GENS[k - 1]


def const(c):
    return CTX.from_dict({(0,) * NV: c}) if c else ZERO


def used_indices(f):
    return [i + 1 for i, d in enumerate(f.degrees()) if d > 0]


def delta(f, k):
    """p_k^perp on the h-polynomial: a derivation with h_j -> h_{j-k}."""
    out = ZERO
    for j in used_indices(f):
        if j >= k:
            out += h(j - k) * f.derivative(j - 1)
    return out


def delta_seq(f, ks):
    for k in ks:
        if f.is_zero():
            return f
        f = delta(f, k)
    return f


def weight(f):
    """Weighted degree of a homogeneous polynomial (asserts homogeneity)."""
    ws = {sum(e * (i + 1) for i, e in enumerate(m)) for m in f.monoms()}
    assert len(ws) == 1, 'not homogeneous'
    return ws.pop()


def minsq_monomial(f):
    best = None
    for m in f.monoms():
        s = sum(e * (i + 1) ** 2 for i, e in enumerate(m) if e)
        if best is None or s < best[0]:
            best = (s, m, 1)
        elif s == best[0]:
            best = (s, best[1], best[2] + 1)
    return best


def prim(f):
    """Primitive integral normalization with positive minimum-square h-monomial."""
    assert not f.is_zero()
    c = f.content()
    g = exact_div(f, const(int(c)))
    s, m, mult = minsq_monomial(g)
    assert mult == 1, 'minimum-square monomial not unique'
    if g.coefficient(g.monoms().index(m)) < 0:
        g = -g
    return g


def exact_div(f, g):
    q, r = divmod(f, g)
    assert r.is_zero(), 'inexact division'
    return q


def scalar_ratio(f, g):
    """Return Fraction c with f == c*g, or None if f is not a scalar multiple of g."""
    assert not g.is_zero()
    if f.is_zero():
        return Fraction(0)
    m = g.monoms()[0]
    fm = f.monoms()
    if m not in fm:
        return None
    c = Fraction(int(f.coefficient(fm.index(m))), int(g.coefficient(0)))
    if f * c.denominator == g * c.numerator:
        return c
    return None


def poly_key(f):
    return str(f)


# ----------------------------------------------------------------------------------------
# diagrams: profiles, cells, betas, Jacobi-Trudi
# ----------------------------------------------------------------------------------------
def prof_to_lm(prof):
    rows, gaps = prof
    n = len(rows)
    assert n >= 1 and len(gaps) == n - 1
    lam = [0] * n
    mu = [0] * n
    lam[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        g = gaps[i]
        assert 0 <= g < min(rows[i], rows[i + 1]), prof
        mu[i] = lam[i + 1] - g - 1
        lam[i] = mu[i] + rows[i]
    return lam, mu


def jt_lm(lam, mu):
    """det(h_{lam_i - mu_j - i + j}) by row-by-row subset expansion."""
    n = len(lam)
    x = [lam[i] - i for i in range(n)]
    y = [mu[j] - j for j in range(n)]
    states = {0: ONE}
    for i in range(n):
        new = defaultdict(lambda: ZERO)
        must = 0
        if i + 1 < n:
            for j in range(n):
                if y[j] > x[i + 1]:
                    must |= 1 << j
        for mask, val in states.items():
            for j in range(n):
                if mask >> j & 1:
                    continue
                e = x[i] - y[j]
                if e < 0:
                    continue
                nm = mask | (1 << j)
                if (nm & must) != must:
                    continue
                sgn = -1 if bin(mask >> (j + 1)).count('1') & 1 else 1
                new[nm] = new[nm] + (val * h(e) if sgn > 0 else -(val * h(e)))
        states = {k: v for k, v in new.items() if not v.is_zero()}
        if not states:
            return ZERO
    return states.get((1 << n) - 1, ZERO)


@lru_cache(maxsize=None)
def schur_prof(prof):
    lam, mu = prof_to_lm(prof)
    return jt_lm(lam, mu)


def rot(prof):
    return tuple(reversed(prof[0])), tuple(reversed(prof[1]))


def cells_of_prof(prof):
    lam, mu = prof_to_lm(prof)
    S = set()
    for i in range(len(lam)):
        for j in range(mu[i], lam[i]):
            S.add((i, j))
    return ENG.normalize(frozenset(S))


def prof_of_cells(S):
    """Profile of a connected skew cell set (engine convention)."""
    assert S and ENG.is_connected_skew(frozenset(S)), 'not connected skew'
    ri = ENG.row_intervals(S)
    ks = sorted(ri)
    rows = tuple(ri[i][1] - ri[i][0] + 1 for i in ks)
    gaps = tuple(ri[ks[t + 1]][1] - ri[ks[t]][0] for t in range(len(ks) - 1))
    return rows, gaps


def components(S):
    S = set(S)
    out = []
    while S:
        st = S.pop()
        comp = {st}
        stack = [st]
        while stack:
            i, j = stack.pop()
            for nb in ((i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1)):
                if nb in S:
                    S.remove(nb)
                    comp.add(nb)
                    stack.append(nb)
        out.append(frozenset(comp))
    return out


def schur_cells(S):
    """Skew Schur function of a cell set whose edge components are connected skew shapes."""
    f = ONE
    for comp in components(S):
        f = f * schur_prof(prof_of_cells(ENG.normalize(comp)))
    return f


def transpose_cells(S):
    return ENG.normalize(frozenset((j, i) for i, j in S))


def rotate_cells(S):
    return ENG.normalize(frozenset((-i, -j) for i, j in S))


def span_cells(S):
    cs = [j - i for i, j in S]
    return max(cs) - min(cs) + 1


# ----------------------------------------------------------------------------------------
# enumeration of connected profiles
# ----------------------------------------------------------------------------------------
def compositions(n):
    if n == 0:
        yield ()
        return
    for x in range(1, n + 1):
        for t in compositions(n - x):
            yield (x,) + t


def profiles(n):
    import itertools
    for r in compositions(n):
        for g in itertools.product(*(range(min(a, b)) for a, b in zip(r, r[1:]))):
            yield (r, tuple(g))


# ----------------------------------------------------------------------------------------
# independent Murnaghan-Nakayama route for p_k^perp (cross-check of delta)
# ----------------------------------------------------------------------------------------
def mn_delta_terms(lam, mu, k):
    """p_k^perp s_{lam/mu} = sum over k-rim hooks lam/nu with nu >= mu of (-1)^ht s_{nu/mu}.
    Returns the list of (sign, nu).  Uses beta numbers of lam."""
    n = len(lam)
    beta = [lam[i] + (n - 1 - i) for i in range(n)]
    bs = set(beta)
    out = []
    for b in beta:
        if b - k >= 0 and (b - k) not in bs:
            ht = sum(1 for c in beta if b - k < c < b)
            nb = sorted([c for c in beta if c != b] + [b - k], reverse=True)
            nu = [nb[i] - (n - 1 - i) for i in range(n)]
            if all(nu[i] >= mu[i] for i in range(n)):
                out.append(((-1) ** ht, nu))
    return out


def mn_delta(lam, mu, k):
    f = ZERO
    for sg, nu in mn_delta_terms(lam, mu, k):
        g = jt_lm(nu, mu)
        f = f + g if sg > 0 else f - g
    return f


# ----------------------------------------------------------------------------------------
# power sums, characters
# ----------------------------------------------------------------------------------------
@lru_cache(maxsize=None)
def p_in_h(n):
    """Newton: p_n = n h_n - sum_{i=1}^{n-1} p_i h_{n-i}; integral."""
    f = const(n) * h(n)
    for i in range(1, n):
        f = f - p_in_h(i) * h(n - i)
    return f


def partitions(n, cap=None):
    if n == 0:
        yield ()
        return
    for j in range(min(n, cap or n), 0, -1):
        for t in partitions(n - j, j):
            yield (j,) + t


def zee(nu):
    z = 1
    for part, m in Counter(nu).items():
        z *= part ** m * factorial(m)
    return z


def p_nu_in_h(nu):
    f = ONE
    for part in nu:
        f = f * p_in_h(part)
    return f


def characters(f, a):
    """chi(nu) = delta_nu f (a constant) for nu |- a, f homogeneous of weight a."""
    out = {}
    for nu in partitions(a):
        g = delta_seq(f, nu)
        if g.is_zero():
            out[nu] = 0
        else:
            assert g.is_constant()
            out[nu] = int(g.coefficient(0))
    return out


def from_characters(chi):
    """sum chi(nu) p_nu / z_nu, returned as (integer h-polynomial, denominator L)."""
    L = 1
    for nu, c in chi.items():
        if c:
            fr = Fraction(c, zee(nu))
            L = L * fr.denominator // gcd(L, fr.denominator)
    f = ZERO
    for nu, c in chi.items():
        if c:
            fr = Fraction(c, zee(nu)) * L
            assert fr.denominator == 1
            f = f + const(int(fr.numerator)) * p_nu_in_h(nu)
    return f, L


def power_sum_coeffs(f, a):
    """f homogeneous of weight a as {nu: Fraction} in the power-sum basis."""
    chi = characters(f, a)
    return {nu: Fraction(c, zee(nu)) for nu, c in chi.items() if c}


# ----------------------------------------------------------------------------------------
# full mate space
# ----------------------------------------------------------------------------------------
PRIME = (1 << 61) - 1
_RNG = random.Random(20261001)
NPTS = 3
POINTS = [[_RNG.randrange(1, PRIME) for _ in range(400)] for _ in range(NPTS)]


def det_mod(prof, pt):
    lam, mu = prof_to_lm(prof)
    n = len(lam)

    def hv(k):
        if k < 0:
            return 0
        if k == 0:
            return 1
        return pt[k - 1]
    M = [[hv(lam[i] - mu[j] - i + j) for j in range(n)] for i in range(n)]
    det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det = det * M[c][c] % PRIME
        inv = pow(M[c][c], PRIME - 2, PRIME)
        for r in range(c + 1, n):
            fct = M[r][c] * inv % PRIME
            if fct:
                M[r] = [(u - fct * w) % PRIME for u, w in zip(M[r], M[c])]
    return det % PRIME


def arrangements(prof):
    """Every (R, G): R a rearrangement of the rows, G of the gaps, 0 <= G_i < min(R_i, R_{i+1})."""
    rows, gaps = prof
    n = len(rows)
    rc, gc = Counter(rows), Counter(gaps)
    R, G, out = [], [], []

    def dfs():
        if len(R) == n:
            out.append((tuple(R), tuple(G)))
            return
        for r in sorted(rc):
            if not rc[r]:
                continue
            if R:
                for g in sorted(gc):
                    if gc[g] and g < min(R[-1], r):
                        rc[r] -= 1
                        gc[g] -= 1
                        R.append(r)
                        G.append(g)
                        dfs()
                        R.pop()
                        G.pop()
                        rc[r] += 1
                        gc[g] += 1
            else:
                rc[r] -= 1
                R.append(r)
                dfs()
                R.pop()
                rc[r] += 1
    dfs()
    return out


def full_class(prof, exact=True):
    """Complete connected Schur class of prof: modular screen over the full mate space, then an
    exact flint Jacobi-Trudi comparison for every survivor."""
    sig = [det_mod(prof, pt) for pt in POINTS]
    cands = arrangements(prof)
    surv = [c for c in cands if all(det_mod(c, pt) == s for pt, s in zip(POINTS, sig))]
    if exact:
        P = schur_prof(prof)
        for c in surv:
            assert schur_prof(c) == P, ('modular screen false positive', prof, c)
    return set(surv), len(cands)


# ----------------------------------------------------------------------------------------
# proper roots: a per-period window search, validated against ENG.factorizations
# ----------------------------------------------------------------------------------------
def contents_map(S):
    by = defaultdict(set)
    for (i, j) in S:
        by[j - i].add((i, j))
    return by


def window_inner(F, p):
    """The unique candidate inner of period p from the two extreme windows (paper Lemma
    gluing-local (iii)), or None."""
    by = contents_map(F)
    c0 = min(by)
    N = max(by) - c0 + 1
    w = N % p
    first = set()
    for c in range(c0, c0 + p):
        first |= by[c]
    last = set()
    for c in range(c0 + N - p, c0 + N):
        last |= by[c]
    a = by[c0 + w]
    b = by[c0 + N - p]
    if len(a) != 1 or len(b) != 1:
        return None
    (ai, aj), = a
    (bi, bj), = b
    tr = (ai - bi, aj - bj)
    last_t = {(i + tr[0], j + tr[1]) for (i, j) in last}
    # agreement on E-contents [w, p-1], i.e. F-contents [c0+w, c0+p-1]
    lo, hi = c0 + w, c0 + p - 1
    fa = {x for x in first if lo <= x[1] - x[0] <= hi}
    fb = {x for x in last_t if lo <= x[1] - x[0] <= hi}
    if fa != fb:
        return None
    E = frozenset(first | last_t)
    if not ENG.is_connected_skew(E):
        return None
    return ENG.normalize(E)


def diag_height_shapes(heights):
    """Every connected skew cell set whose diagonal heights are the given sequence."""
    r = len(heights)
    if r == 1:
        if heights[0] == 1:
            return [frozenset({(0, 0)})]
        return []
    if heights[0] != 1 or heights[-1] != 1 or min(heights) < 1:
        return []
    out = []
    # diagonal t occupies rows [l_t, l_t + H_t - 1]; l_{t-1} - l_t = A_t in {0,1}; top endpoint
    # h_t = l_t + H_t - 1, h_{t-1} - h_t = B_t in {0,1}; H_t - H_{t-1} = A_t - B_t.
    def rec(t, l, acc):
        if t == r:
            out.append(frozenset(acc))
            return
        dH = heights[t] - heights[t - 1]
        for A in (0, 1):
            B = A - dH
            if B not in (0, 1):
                continue
            nl = l - A
            cells = [(i, i + t) for i in range(nl, nl + heights[t])]
            rec(t + 1, nl, acc + cells)
    rec(1, 0, [(0, 0)])
    return [ENG.normalize(S) for S in out if ENG.is_connected_skew(ENG.normalize(S))]


_WC_CACHE = {}


def legal_marks(E):
    if E not in _WC_CACHE:
        _WC_CACHE[E] = [(B, T, case, v) for (B, T, case, v, _h) in ENG.w_candidates(E)]
    return _WC_CACHE[E]


def my_roots(F):
    """All proper I-IV roots (D, E, Wsw, Wne, case, v) of the connected cell set F."""
    F = ENG.normalize(frozenset(F))
    by = contents_map(F)
    c0 = min(by)
    N = max(by) - c0 + 1
    found = []
    for p in range(2, N // 2 + 1):
        w = N % p
        r = (N - w) // p
        if r < 2:
            continue
        E = window_inner(F, p)
        if E is None or len(E) < 2:
            continue
        marks = [m for m in legal_marks(E) if m[3][1] - m[3][0] == p]
        if not marks:
            continue
        # private heights of the outer: F cells on contents c0 + t p + w
        heights = [len(by[c0 + t * p + w]) for t in range(r)]
        cands = diag_height_shapes(heights)
        for (B, T, case, v) in marks:
            for D in cands:
                if len(D) < 2:
                    continue
                G = ENG.compose(D, E, B, T, case, v)
                if G == F:
                    found.append((D, E, B, T, case, v))
    return found


def eng_roots(F):
    """Reference: the engine's complete factorization search (Hypothesis I on), cap lifted."""
    ENG.CD_CAP = 10 ** 9
    out = []
    for (D, E, B, T, case) in ENG.factorizations(F):
        v = ENG.v_of_W(E, B, T, case)
        out.append((D, E, B, T, case, v))
    return out


def root_key_set(roots):
    return {(D, E, B, T, case) for (D, E, B, T, case, v) in roots}


def period_of(root):
    v = root[5]
    return v[1] - v[0]


def score(N, p):
    return (N % p, p + N % p)


# ----------------------------------------------------------------------------------------
# large mate spaces: capped enumeration, numpy batch determinants, transposition trick
# ----------------------------------------------------------------------------------------
def arrangements_capped(prof, cap):
    rows, gaps = prof
    n = len(rows)
    rc, gc = Counter(rows), Counter(gaps)
    R, G, out = [], [], []

    class Stop(Exception):
        pass

    def dfs():
        if len(R) == n:
            out.append((tuple(R), tuple(G)))
            if len(out) > cap:
                raise Stop
            return
        for r in sorted(rc):
            if not rc[r]:
                continue
            if R:
                for g in sorted(gc):
                    if gc[g] and g < min(R[-1], r):
                        rc[r] -= 1
                        gc[g] -= 1
                        R.append(r)
                        G.append(g)
                        dfs()
                        R.pop()
                        G.pop()
                        rc[r] += 1
                        gc[g] += 1
            else:
                rc[r] -= 1
                R.append(r)
                dfs()
                R.pop()
                rc[r] += 1
    try:
        dfs()
    except Stop:
        return None
    return out


P31 = 2147483647
_RNG2 = random.Random(777)
PTS31 = [[_RNG2.randrange(2, P31) for _ in range(600)] for _ in range(3)]


def batch_screen(cands, target_prof):
    """Indices of candidates whose JT determinant agrees with the target's at 3 random points mod
    2^31-1 (numpy, no pivoting; zero pivots fall back to exact modular elimination)."""
    import numpy as np
    n = len(target_prof[0])
    idx = np.empty((len(cands), n, n), dtype=np.int64)
    for c, pr in enumerate(cands):
        lam, mu = prof_to_lm(pr)
        for i in range(n):
            li = lam[i] - i
            for j in range(n):
                idx[c, i, j] = li - mu[j] + j
    assert idx.max() <= 600, 'raise the point length'
    keep = np.ones(len(cands), dtype=bool)
    lam, mu = prof_to_lm(target_prof)
    for pt in PTS31:
        table = np.zeros(602, dtype=np.int64)
        table[1] = 1                              # h_0 = 1 at offset 1
        table[2:] = np.array(pt[:600], dtype=np.int64)   # h_k at offset k+1
        tgt = _det_mod31(target_prof, pt)
        M = np.where(idx < 0, 0, table[np.clip(idx, -1, 600) + 1])
        det, bad = _batch_det(M)
        for b in np.nonzero(bad)[0]:
            det[b] = _det_mod31(cands[b], pt)
        keep &= (det == tgt)
    return [i for i in range(len(cands)) if keep[i]]


def _pow_mod_vec(x, e, P):
    import numpy as np
    res = np.ones_like(x)
    base = x % P
    while e:
        if e & 1:
            res = res * base % P
        base = base * base % P
        e >>= 1
    return res


def _batch_det(M):
    import numpy as np
    M = M.copy() % P31
    K, n, _ = M.shape
    det = np.ones(K, dtype=np.int64)
    bad = np.zeros(K, dtype=bool)
    for c in range(n):
        piv = M[:, c, c]
        z = piv == 0
        bad |= z
        piv = np.where(z, 1, piv)
        inv = _pow_mod_vec(piv, P31 - 2, P31)
        det = det * piv % P31
        for r in range(c + 1, n):
            f = M[:, r, c] * inv % P31
            M[:, r, :] = (M[:, r, :] - f[:, None] * M[:, c, :]) % P31
    return det, bad


def _det_mod31(prof, pt):
    lam, mu = prof_to_lm(prof)
    n = len(lam)

    def hv(k):
        if k < 0:
            return 0
        if k == 0:
            return 1
        return pt[k - 1]
    M = [[hv(lam[i] - mu[j] - i + j) for j in range(n)] for i in range(n)]
    det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det = det * M[c][c] % P31
        inv = pow(M[c][c], P31 - 2, P31)
        for r in range(c + 1, n):
            fct = M[r][c] * inv % P31
            if fct:
                M[r] = [(u - fct * w) % P31 for u, w in zip(M[r], M[c])]
    return det % P31


def transpose_prof(prof):
    return prof_of_cells(transpose_cells(cells_of_prof(prof)))


_CLASS_CACHE = {}


def schur_class_full(prof, cap=3000000):
    """Complete connected Schur class of prof (every arrangement of its rows and gaps, screened by
    three random evaluations mod 2^31-1, every survivor confirmed by exact flint JT).  If the row
    arrangement space exceeds cap, the transpose's space is used (s_{H^t} = omega s_H), then
    transposed back.  Returns (set of profiles, size of the mate space searched, which side) or
    None if both spaces exceed cap."""
    if prof in _CLASS_CACHE:
        return _CLASS_CACHE[prof]
    for side in ('rows', 'cols'):
        src = prof if side == 'rows' else transpose_prof(prof)
        cands = arrangements_capped(src, cap)
        if cands is None:
            continue
        if len(cands) > 50:
            # chunked (continuation): identical result, bounded memory for tall parents
            surv = []
            for st in range(0, len(cands), 100000):
                sub = cands[st:st + 100000]
                surv += [sub[i] for i in batch_screen(sub, src)]
        else:
            surv = [c for c in cands if all(_det_mod31(c, pt) == _det_mod31(src, pt) for pt in PTS31)]
        P = schur_prof(src)
        for c in surv:
            assert schur_prof(c) == P, ('screen false positive', src, c)
        if side == 'cols':
            surv = [transpose_prof(c) for c in surv]
        res = (set(surv), len(cands), side)
        for m in res[0]:
            _CLASS_CACHE[m] = res
        return res
    return None


# ----------------------------------------------------------------------------------------
# keys
# ----------------------------------------------------------------------------------------
ROTCASE = {'a': 'a', 'b': 'b', 'c': 'd', 'd': 'c'}


def rotate_mark(E, B, T, case):
    R = frozenset((-i, -j) for i, j in E)
    i0 = min(i for i, _ in R)
    j0 = min(j for _, j in R)

    def tr(S):
        return frozenset((-i - i0, -j - j0) for i, j in S)
    return ENG.normalize(R), tr(T), tr(B), ROTCASE[case]


def mark_repr(E, B, T, case):
    return (tuple(sorted(E)), tuple(sorted(B)), tuple(sorted(T)), case)


def key_orbit(root):
    """All representations of the key of a root modulo transported rotation and ordinary gauge."""
    D, E, B, T, case, v = root
    p = v[1] - v[0]
    Q = poly_key(schur_cells(D))
    reps = set()
    reps.add((mark_repr(E, B, T, case), Q))
    reps.add((mark_repr(*rotate_mark(E, B, T, case)), Q))
    if case in ('a', 'b'):
        other = 'b' if case == 'a' else 'a'
        duals = [m for m in legal_marks(E) if m[2] == other and m[3][1] - m[3][0] == p]
        assert len(duals) <= 1
        if duals:
            B2, T2, c2, v2 = duals[0]
            Qw = poly_key(schur_cells(transpose_cells(D)))
            reps.add((mark_repr(E, B2, T2, c2), Qw))
            reps.add((mark_repr(*rotate_mark(E, B2, T2, c2)), Qw))
    return frozenset(reps)


def canonical_key(root):
    return min(key_orbit(root))


def sm_analysis(prof):
    """Roots of a profile, their periods, the source-minimal roots and their canonical keys."""
    F = cells_of_prof(prof)
    roots = my_roots(F)
    if not roots:
        return {'rooted': False, 'periods': []}
    N = span_cells(F)
    periods = sorted({period_of(r) for r in roots})
    best = min(score(N, p) for p in periods)
    sm = [r for r in roots if score(N, period_of(r)) == best]
    keys = {canonical_key(r) for r in sm}
    return {'rooted': True, 'periods': periods, 'sm_period': period_of(sm[0]), 'keys': keys,
            'nroots': len(roots), 'roots': roots}
