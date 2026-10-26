r"""Paper section `app:empty` (Empty overlaps and zero span remainder).

Witt annihilator and window current at empty marks (`prop:empty-exit`, case mu = 1).

For a skew diagram W of span g and H = W near-concatenated with itself k times (span N = k g),
with f = s_H / kappa_H (the Schur complement h_N - w A^{-1} b) and
L_s = V_s - (N - s) delta_s, this checks:

1. L_g f = 0 (the row-power identity), and L_s f = 0 for s = i g + j g' combinations reachable
   in the paper's setting is not needed here -- only the identity actually used downstream:
2. for s with 1 <= s < N and m = N - s, the four-term Witt sum equals
   - balanced(m, 0) on the shifted rows (x - s) against the columns, with the full coframes of H,
   i.e. sum_{x,y} L(x) R(y) (x - y - N) h_{x-y-s} = - sum L(x) R(y) (m - (x - s) + y) h_{(x-s)-y}.
3. the restrictions of R to columns <= m and of L(. + s) to rows in [0, m] satisfy the window row
   and column equations (the contact equations of the two windows).
"""
import itertools
import sympy as sp

H = sp.symbols('h1:40')


def h(k):
    if k < 0:
        return sp.Integer(0)
    if k == 0:
        return sp.Integer(1)
    return H[k - 1]


def near(a, b):
    """Near concatenation of two cell sets: top-right cell of b immediately left of the
    bottom-left cell of a, in the same row."""
    ra = max(r for r, c in a)
    ca = min(c for r, c in a if r == ra)
    rb = min(r for r, c in b)
    cb = max(c for r, c in b if r == rb)
    dr, dc = ra - rb, ca - 1 - cb
    return a | {(r + dr, c + dc) for r, c in b}


def betas(D):
    """Row and column beta labels (content-based): row r contributes its rightmost content + 1
    shifted, column labels from leftmost contents.  Normalized so the last column beta is 0."""
    rows = sorted({r for r, c in D})
    X = [max(c for rr, c in D if rr == r) - r + 1 for r in rows]
    Y = [min(c for rr, c in D if rr == r) - r for r in rows]
    t = min(Y)
    return [x - t for x in X], [y - t for y in Y]


def schur(X, Y):
    n = len(X)
    return sp.Matrix(n, n, lambda i, j: h(X[i] - Y[j])).det()


def witt(expr, N, s):
    out = 0
    for k in range(1, len(H) + 1):
        d = sp.diff(expr, H[k - 1])
        if d != 0:
            out += d * (k - N) * h(k - s)
    return sp.simplify(out)


def check(W, k, svals):
    D = W
    for _ in range(k - 1):
        D = near(D, W)
    X, Y = betas(D)
    N = X[0]
    g = betas(W)[0][0]
    I, C = X[1:], Y[:-1]
    n = len(I)
    A = sp.Matrix(n, n, lambda i, j: h(I[i] - C[j]))
    kap = A.det()
    # the Schur complement h_N - w A^{-1} b is (-1)^n s_H / kappa (corner at the last column)
    f = sp.together((-1) ** n * schur(X, Y) / kap)
    # 1. row power identity
    assert sp.simplify(witt(sp.cancel(f), N, g)) == 0, ("row power", W, k)
    Ai = A.inv()
    u = Ai * sp.Matrix([h(i) for i in I])
    v = sp.Matrix([[h(N - c) for c in C]]) * Ai
    L = {N: 1}
    for i, x in enumerate(I):
        L[x] = -v[i]
    R = {0: 1}
    for j, y in enumerate(C):
        R[y] = -u[j]
    # row / column equations of H
    for x in I:
        assert sp.simplify(sum(h(x - y) * R[y] for y in R)) == 0
    for y in C:
        assert sp.simplify(sum(L[x] * h(x - y) for x in L)) == 0
    for s in svals:
        m = N - s
        lhs = sum(L[x] * R[y] * (x - y - N) * h(x - y - s) for x in L for y in R)
        # Witt sum from the derivative formula equals the four-term sum
        assert sp.simplify(witt(sp.cancel(f), N, s) - lhs) == 0, ("four", s)
        bal = sum(L[x] * R[y] * (m - (x - s) + y) * h((x - s) - y) for x in L for y in R)
        assert sp.simplify(lhs + bal) == 0, ("balanced", s)
        # window contact equations
        for x in I:
            if x < m:
                assert sp.simplify(sum(h(x - y) * R[y] for y in R if y <= m)) == 0
        for y in C:
            yy = y - s
            if 0 < yy <= m:
                assert sp.simplify(sum(L[x] * h(x - s - yy) for x in L if 0 <= x - s <= m)) == 0
    return N


ribbon2 = {(0, 1), (0, 2), (1, 0), (1, 1)}         # composition (2, 2)
body = {(0, 1), (0, 2), (1, 0), (1, 1), (1, 2)}     # a non-ribbon connected body
col2 = {(0, 0), (1, 0)}
for W, k in [(ribbon2, 3), (body, 2), (body, 3), (col2, 3)]:
    X, Y = betas(W)
    g = X[0]
    N = check(W, k, [g, g + 1, 2 * g - 1] if k * g > 2 * g else [g])
    print("ok", sorted(W), "k =", k, "N =", N)
print("ALL PASS")
