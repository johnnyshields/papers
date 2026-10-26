"""Shared exact machinery for the cofactor census scripts.  Imported, never run.

Everything is built from the paper's own definitions, in exact integer (and
`Fraction`) arithmetic on signed multisets of h-monomials, with no floating point:

  * the cap coordinates A_i = L - lambda_i + i and d_j = L - mu_{j-1} + j - 1,
    d_0 = 0 (`eq:Adef`, `eq:dexplicit`);
  * the capped cofactor vector C_j(X) = (-1)^j det of M_{ic} = h_{d_c - A_i} with
    column j deleted (`eq:capmatrix`, `eq:cofactor`), expanded over all
    permutations by `skew_core.det_h`, so a vanishing entry h_{<0} drops its
    term rather than merely evaluating to zero;
  * admissible convex weights (`def:convex-weight`), the weight of a monomial
    and of a polynomial, its initial face, and the defect, normalized action
    and tilted cost of a pair.

A monomial is a tuple of positive indices (h_0 = 1 contributes nothing).
"""
import os
import sys
from collections import defaultdict
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from skew_core import det_h, h, padd, pmul, s_poly                        # noqa: E402,F401
from skew_harness import connected, gen_shapes, rotate, size             # noqa: E402,F401

# ------------------------------------------------------------------ weights

SQ = lambda k: k * k                                                     # noqa: E731
CU = lambda k: k ** 3                                                    # noqa: E731
RX = lambda k: 0 if k == 0 else 7 ** k                                   # noqa: E731
RG = lambda k: Fraction(7 * k * k + k ** 3, 7)                           # noqa: E731

WEIGHTS = {"square": SQ, "cubic": CU, "radix7": RX, "ragged": RG}
INF = None          # the action of a vanishing coordinate


def admissible(om, kmax=14):
    """`def:convex-weight`: omega(0)=0, increments positive and strictly increasing."""
    if om(0) != 0:
        return False
    inc = [om(k) - om(k - 1) for k in range(1, kmax + 1)]
    return all(x > 0 for x in inc) and all(a < b for a, b in zip(inc, inc[1:]))


def wmon(m, om):
    return sum(om(e) for e in m)


def wpoly(f, om):
    """Minimum weight over the support, or None (= +infinity) for the zero polynomial."""
    return min(wmon(m, om) for m in f) if f else None


def init_face(f, om):
    """(minimum weight, {monomial: coefficient} attaining it)."""
    w = wpoly(f, om)
    return w, {m: c for m, c in f.items() if wmon(m, om) == w}


def neg(f):
    return {m: -c for m, c in f.items()}


def sub(f, g):
    return padd(f, g, -1)


def deg(f):
    ds = {sum(m) for m in f}
    assert len(ds) <= 1, "polynomial is not homogeneous"
    return ds.pop() if ds else None


# ------------------------------------------------------------------ cap coordinates

def grid(sh):
    """(A, d): the row parameters and the cap grid of a shape (lam, mu)."""
    lam, mu = sh
    n = len(lam)
    mu = tuple(mu) + (0,) * (n - len(mu))
    L = lam[0]
    A = [L - lam[i] + i for i in range(n)]
    d = [0] + [L - mu[j - 1] + j - 1 for j in range(1, n + 1)]
    return A, d


def det_dp(entries):
    """Determinant of a matrix of h-INDICES by Laplace expansion along the last row, memoized
    on the surviving column set: O(2^n n) polynomial operations in place of n! terms.  A negative
    index is a zero entry (h_{<0} = 0) and drops its term.  Agrees with `skew_core.det_h`."""
    n = len(entries)
    if n == 0:
        return {(): 1}
    memo = {(): {(): 1}}

    def go(cols):                       # cols: sorted tuple of columns, len r = rows used
        if cols in memo:
            return memo[cols]
        r = len(cols)
        out = {}
        for pos, c in enumerate(cols):
            e = entries[r - 1][c]
            if e < 0:
                continue
            sub_det = go(cols[:pos] + cols[pos + 1:])
            if not sub_det:
                continue
            term = pmul(sub_det, h(e)) if e else sub_det
            out = padd(out, term if (r - 1 + pos) % 2 == 0 else neg(term))
        memo[cols] = out
        return out

    return go(tuple(range(n)))


_COF = {}


def cofvec(sh):
    """The signed maximal cofactors (C_0, ..., C_n) of the capped matrix h_{d_c - A_i}."""
    if sh in _COF:
        return _COF[sh]
    A, d = grid(sh)
    n = len(A)
    out = []
    for j in range(n + 1):
        cols = [c for c in range(n + 1) if c != j]
        f = det_dp([[d[c] - A[i] for c in cols] for i in range(n)])
        out.append(f if j % 2 == 0 else neg(f))
    _COF[sh] = out
    return out


def cofvec_reference(sh):
    """The same vector by full permutation expansion (`skew_core.det_h`): the independent route
    the memoized `det_dp` is checked against."""
    A, d = grid(sh)
    n = len(A)
    out = []
    for j in range(n + 1):
        cols = [c for c in range(n + 1) if c != j]
        f = det_h([[d[c] - A[i] for c in cols] for i in range(n)])
        out.append(f if j % 2 == 0 else neg(f))
    return out


def rows(sh):
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return [lam[i] - mu[i] for i in range(len(lam))]


def Pk(vec, d, k):
    """P_k = sum_j vec_j h_{k + d_j} over a column-indexed vector."""
    out = {}
    for j, f in enumerate(vec):
        if f and k + d[j] >= 0:
            out = padd(out, pmul(f, h(k + d[j])))
    return out


def extend(sh, a):
    """X.(a): a row of length a attached to the northeast, meeting the top row in one column."""
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return ((lam[0] + a - 1,) + tuple(lam), (lam[0] - 1,) + tuple(mu))


def first_row_deleted(sh):
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return (tuple(lam[1:]), tuple(mu[1:]))


# ------------------------------------------------------------------ pairs

def buckets(shapes, key):
    out = defaultdict(list)
    for s in shapes:
        out[key(s)].append(s)
    return out


class Pair:
    """Two connected diagrams on a common inner boundary and a common cap grid."""

    def __init__(self, X, Y):
        self.X, self.Y = X, Y
        self.AX, self.d = grid(X)
        self.AY, dY = grid(Y)
        assert self.d == dY
        self.n = len(X[0])
        CX, CY = cofvec(X), cofvec(Y)
        self.CX, self.CY = CX, CY
        self.G = [sub(CX[j], CY[j]) for j in range(self.n + 1)]
        diff = [i for i in range(self.n) if self.AX[i] != self.AY[i]]
        assert diff, (X, Y)
        self.v = diff[0]
        self.q = self.v + 1

    def alpha(self, om):
        return [None if not g else wpoly(g, om) + om(self.d[j]) for j, g in enumerate(self.G)]

    def sigma(self, parent, om):
        vec = self.CX if parent == "X" else self.CY
        return [wpoly(f, om) + om(self.d[j]) for j, f in enumerate(vec)]

    def F(self, i, om, alpha=None, A=None):
        """F_i(j) = alpha_j + omega(d_j - A_i) - omega(d_j) where G_j != 0 and d_j >= A_i."""
        alpha = alpha if alpha is not None else self.alpha(om)
        Ai = (A if A is not None else self.AX)[i] if i >= 0 else None
        out = {}
        for j, a in enumerate(alpha):
            if a is None or self.d[j] < Ai:
                continue
            out[j] = a + om(self.d[j] - Ai) - om(self.d[j])
        return out


def argmin(dct):
    m = min(dct.values())
    return m, sorted(j for j, x in dct.items() if x == m)


def cap_fixed_pairs(size_cap, row_cap):
    """Every ordered-once pair of distinct connected diagrams with a common inner boundary,
    a common number of rows and a common top row."""
    shapes = gen_shapes(size_cap, row_cap)
    bk = buckets(shapes, lambda s: (s[1], s[0][0], len(s[0])))
    for key, mem in sorted(bk.items()):
        for a in range(len(mem)):
            for b in range(a + 1, len(mem)):
                yield Pair(mem[a], mem[b])
