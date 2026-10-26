"""Original Jacobi--Trudi matrices of tile chains, with exact series arithmetic in t = h_1.

Import-only module.  A tile is a connected skew diagram whose southeast interior consists of
isolated cells (so its corner inventory is a power of h_1 and the maximal-span prime is
psi = h_1, a = 1, N = 1, with multiplicity r = number of interior cells).  A chain is a
sequence of tiles joined by empty horizontal or vertical joins.  Every h_j other than h_1
is an exact rational number supplied by an assignment; h_1 = t is a truncated power series
variable.  Nothing here uses the eliminated response model: matrices are the full
original matrices of the cell sets built from the paper's definitions.
"""
from fractions import Fraction as F
from itertools import product
from diagram_tools import (canonical, components, connected_skew, interior, jt_indices,
                           span, translate)


def join(first, second, kind):
    ne = max(first, key=lambda z: z[1]-z[0])
    sw = min(second, key=lambda z: z[1]-z[0])
    target = (ne[0], ne[1]+1) if kind == 'H' else (ne[0]-1, ne[1])
    out = first | translate(second, (target[0]-sw[0], target[1]-sw[1]))
    assert connected_skew(out) and span(out) == span(first)+span(second)
    return canonical(out)


def chain(tile, edges):
    out = tile
    for edge in edges:
        out = join(out, tile, edge)
    return out


def assignment(seed):
    """Reproducible rational values for h_2, h_3, ...; distinct seeds give independent assignments."""
    def h(index):
        return F((index*index*7+index*13+seed*seed*5+seed*17) % 97+3, (index+seed) % 11+2)
    return h


# --- truncated series ---------------------------------------------------------

def zero(L):
    return [F(0)]*L


def const(c, L):
    return [F(c)]+[F(0)]*(L-1)


def smul(a, b, L):
    out = zero(L)
    for i, x in enumerate(a):
        if x:
            for j in range(min(len(b), L-i)):
                out[i+j] += x*b[j]
    return out


def sadd(a, b, sign=1):
    return [x+sign*y for x, y in zip(a, b)]


def sinv(a, L):
    assert a[0] != 0
    out = zero(L)
    out[0] = 1/a[0]
    for k in range(1, L):
        out[k] = -sum(a[i]*out[k-i] for i in range(1, k+1))/a[0]
    return out


def entry(index, L, h, N, free=None):
    """Series of h_index.  The variable t is h_N (the maximal-span prime psi = h_N, so a = 1,
    c = 0); every other generator is an exact rational from the assignment `h`, except that
    `free` = (generator index, value) overrides one of them."""
    if index < 0:
        return zero(L)
    if index == 0:
        return const(1, L)
    if index == N:
        out = zero(L)
        out[1] = F(1)
        return out
    if free is not None and index == free[0]:
        return const(free[1], L)
    return const(h(index), L)


def series_matrix(indices, L, h, N, free=None):
    return [[entry(x, L, h, N, free) for x in row] for row in indices]


def det(matrix, L):
    """Determinant over truncated series by fraction-free-style elimination with
    constant-term pivoting; falls back to cofactor recursion when no pivot is a unit."""
    n = len(matrix)
    a = [[list(x) for x in row] for row in matrix]
    sign = 1
    result = const(1, L)
    for c in range(n):
        pivot = next((r for r in range(c, n) if a[r][c][0] != 0), None)
        if pivot is None:
            return cofactor_det(matrix, L)
        if pivot != c:
            a[c], a[pivot] = a[pivot], a[c]
            sign = -sign
        result = smul(result, a[c][c], L)
        inv = sinv(a[c][c], L)
        for r in range(c+1, n):
            if any(a[r][c]):
                f = smul(a[r][c], inv, L)
                for k in range(c, n):
                    a[r][k] = sadd(a[r][k], smul(f, a[c][k], L), -1)
    return [sign*x for x in result]


def cofactor_det(matrix, L):
    n = len(matrix)
    if n == 0:
        return const(1, L)
    if n == 1:
        return list(matrix[0][0])
    total = zero(L)
    for j in range(n):
        if not any(matrix[0][j]):
            continue
        minor = [row[:j]+row[j+1:] for row in matrix[1:]]
        term = smul(matrix[0][j], cofactor_det(minor, L), L)
        total = sadd(total, term, (-1)**j)
    return total


def solve_right(P, B, L):
    """P^{-1} B for series matrices, P(0) invertible."""
    n = len(P)
    m = len(B[0]) if B else 0
    a = [[list(x) for x in P[i]]+[list(x) for x in B[i]] for i in range(n)]
    for c in range(n):
        pivot = next(r for r in range(c, n) if a[r][c][0] != 0)
        a[c], a[pivot] = a[pivot], a[c]
        inv = sinv(a[c][c], L)
        a[c] = [smul(inv, x, L) for x in a[c]]
        for r in range(n):
            if r != c and any(a[r][c]):
                f = a[r][c]
                a[r] = [sadd(x, smul(f, y, L), -1) for x, y in zip(a[r], a[c])]
    return [row[n:] for row in a]


def schur_complement(matrix, rows_keep, cols_keep, L):
    """Retained block minus B P^{-1} C, with P the removed block."""
    n = len(matrix)
    rows_drop = [i for i in range(n) if i not in rows_keep]
    cols_drop = [j for j in range(n) if j not in cols_keep]
    A = [[matrix[i][j] for j in cols_keep] for i in rows_keep]
    if not rows_drop:
        return A, const(1, L)
    P = [[matrix[i][j] for j in cols_drop] for i in rows_drop]
    Bm = [[matrix[i][j] for j in cols_keep] for i in rows_drop]
    Cm = [[matrix[i][j] for j in cols_drop] for i in rows_keep]
    X = solve_right(P, Bm, L)
    out = []
    for r, i in enumerate(rows_keep):
        row = []
        for c in range(len(cols_keep)):
            value = A[r][c]
            for k in range(len(rows_drop)):
                value = sadd(value, smul(Cm[r][k], X[k][c], L), -1)
            row.append(value)
        out.append(row)
    return out, det(P, L)


def tile_data(shape):
    """(N, selected interior rows, tie count) for a tile whose interior components are rows
    or other connected diagrams: psi = h_N is the row component(s) of maximal span N.
    Returns None when no maximal-span component is a single row."""
    comps = components(interior(shape))
    if not comps:
        return None
    N = max(span(c) for c in comps)
    selected = [c for c in comps if span(c) == N and len({i for i, _ in c}) == 1
                and len(c) == N]
    if not selected:
        return None
    return N, len(selected)


def selected_positions(shape, N):
    """JT position j of every selected interior component: the component sits in shape row
    i, which is the j-th row from the top; its entry in the matrix is (j+1, j)."""
    rows = sorted({i for i, _ in shape})
    position = {i: k for k, i in enumerate(rows)}
    out = []
    for comp in components(interior(shape)):
        if span(comp) == N and len({i for i, _ in comp}) == 1 and len(comp) == N:
            (i, _), = [min(comp)]
            out.append(position[i])
    return sorted(out)


def tile_domain(max_area=8):
    """Tiles with a row prime of maximal span: (shape, N, r) in a fixed order."""
    from diagram_tools import shapes_of_area
    out = []
    for n in range(3, max_area+1):
        for T in shapes_of_area(n):
            data = tile_data(T)
            if data:
                out.append((T, data[0], data[1]))
    return out


def window_edges(b, v):
    """Edge words of length b-1 whose first and last v tiles agree with matching cuts."""
    for edges in product('HV', repeat=b-1):
        w = ''.join(edges)
        if w[:v-1] == w[b-v:] and w[v-1] == w[b-v-1]:
            yield w


class Retained:
    """The retained Hessenberg block of a chain U in the normal coordinate t = h_N."""

    def __init__(self, U, N, L, h, free=None):
        self.U, self.N, self.L = U, N, L
        self.indices = jt_indices(U)
        n = len(self.indices)
        self.n = n
        self.sel = selected_positions(U, N)
        for j in self.sel:
            assert self.indices[j+1][j] == N, 'selected entry is not h_N'
        self.rows = [0]+[j+1 for j in self.sel]
        self.cols = list(self.sel)+[n-1]
        assert len(self.rows) == len(self.cols)
        removed_rows = [i for i in range(n) if i not in self.rows]
        removed_cols = [j for j in range(n) if j not in self.cols]
        assert len(removed_rows) == len(removed_cols)
        self.removed_rows, self.removed_cols = removed_rows, removed_cols
        M = series_matrix(self.indices, L, h, N, free)
        self.S, self.removed_det = schur_complement(M, self.rows, self.cols, L)
        self.full = M

    def det(self):
        return smul(det(self.S, self.L), self.removed_det, self.L)


def exact_det(rows):
    a = [list(r) for r in rows]
    n, d = len(a), F(1)
    for c in range(n):
        p = next((r for r in range(c, n) if a[r][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            a[c], a[p] = a[p], a[c]
            d = -d
        d *= a[c][c]
        for r in range(c+1, n):
            if a[r][c] != 0:
                f = a[r][c]/a[c][c]
                for k in range(c, n):
                    a[r][k] -= f*a[c][k]
    return d


def full_det_series(indices, L, h, N, free=None):
    """Determinant of the full original matrix as a series in t = h_N, by evaluation at
    n+1 integer points and Newton interpolation (the degree in t is at most n)."""
    n = len(indices)

    def value(index, t):
        if index < 0:
            return F(0)
        if index == 0:
            return F(1)
        if index == N:
            return F(t)
        if free is not None and index == free[0]:
            return F(free[1])
        return F(h(index))

    pts = list(range(n+1))
    vals = [exact_det([[value(x, t) for x in row] for row in indices]) for t in pts]
    coef = list(vals)
    for k in range(1, len(pts)):
        for i in range(len(pts)-1, k-1, -1):
            coef[i] = (coef[i]-coef[i-1])/(pts[i]-pts[i-k])
    poly = [F(0)]
    for i in range(len(pts)-1, -1, -1):
        shifted = [F(0)]+poly
        poly = [shifted[k]-pts[i]*(poly[k] if k < len(poly) else 0) for k in range(len(shifted))]
        poly[0] += coef[i]
    return (poly+[F(0)]*L)[:L]
