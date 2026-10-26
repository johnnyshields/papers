"""Sampled periodic sources of the hard comparison and their exact cap data.

A source has full flags `X = (N, I)`, `Y = (C, 0)` (strictly decreasing, `X_i >= Y_i`), span `N`,
the clock parameters `g | p, q` with `p > q >= 2g > c`, `a = N - q - c`, `m = a + c`, and both
boundary words `g`-periodic on the open middle `c < k < N - c`.  Sources are drawn from the word
parametrization (free bits outside the middle, one period of free bits inside) and rejected
unless the height word stays positive and the splice contents `c`, `q + c`, `a - 1`,
`N - c - 1` and the return pins `q - 1`, `m`, `N - m`, `N - m - 1` are singleton diagonals.  Exact `Fraction`
arithmetic at a seeded rational alphabet with a rational `h_0 = nu`.
"""
import random
from fractions import Fraction as Fr

from _schur_common import determinant


def heights(X, Y, N):
    return [sum(y <= k for y in Y) - sum(x <= k for x in X) for k in range(N)]


def sample(rng, want_pins=True, period=None):
    while True:
        g = rng.choice((2, 3))
        c = rng.randint(1, g - 1)
        qm = rng.randint(2, 3)
        pm = rng.randint(qm + 1, qm + 2)
        p, q = pm * g, qm * g
        N = rng.randint(2 * p + c, 2 * p + c + 6)
        a = N - q - c
        m = a + c
        if not a >= q >= 2 * g > c:
            continue
        wI = {k: rng.random() < 0.5 for k in range(1, N)}
        wC = {k: rng.random() < 0.5 for k in range(1, N)}
        for k in range(c + 1, N - c):
            per = g if period is None else p
            if k + per < N - c:
                wI[k + per] = wI[k]
                wC[k + per] = wC[k]
        X = tuple(sorted([N] + [k for k in wI if wI[k]], reverse=True))
        Y = tuple(sorted([k for k in wC if wC[k]] + [0], reverse=True))
        if len(X) != len(Y) or any(x < y for x, y in zip(X, Y)):
            continue
        H = heights(X, Y, N)
        if min(H) < 1 or H[0] != 1:
            continue
        if want_pins and period is None and not all(H[k] == 1 for k in (c, q - 1, q + c, a - 1, N - c - 1, m, N - m, N - m - 1)):
            continue
        return dict(X=X, Y=Y, N=N, g=g, c=c, p=p, q=q, a=a, m=m)


def splice(X, Y, N, u, v):
    d = v - u
    Xn = tuple(sorted([x for x in X if 1 <= x <= u] + [x - d for x in X if v < x <= N], reverse=True))
    Yn = tuple(sorted([y for y in Y if 0 <= y <= u] + [y - d for y in Y if v < y < N], reverse=True))
    return Xn, Yn, N - d


def alphabet(rng, nmax):
    base = {k: Fr(rng.randint(1, 30), rng.randint(1, 9)) * rng.choice((1, -1)) for k in range(1, nmax + 3)}
    nu = Fr(rng.randint(2, 30), rng.randint(1, 9))

    def h(k):
        return Fr(0) if k < 0 else (nu if k == 0 else base[k])
    return h


def solve(A, rhs):
    """Solve the square system `A x = rhs` over Fractions (Gauss--Jordan); None if singular."""
    n = len(A)
    M = [list(A[i]) + [rhs[i]] for i in range(n)]
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        inv = 1 / M[col][col]
        M[col] = [v * inv for v in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]


def coframes(X, Y, N, h):
    """`R(z) = 1 - sum_j (A^-1 b)_j z^j`, `L(z) = 1 - sum_i (w A^-1)_i z^(N-i)` as dicts exponent -> coeff,
    for the proper matrix `A = (h_{i-j})`, `i in I = X \\ {N}`, `j in C = Y \\ {0}`."""
    I, C = list(X[1:]), list(Y[:-1])
    R, L = {0: Fr(1)}, {0: Fr(1)}
    if I:
        A = [[h(i - j) for j in C] for i in I]
        u = solve(A, [h(i) for i in I])
        wv = solve([[A[r][s] for r in range(len(I))] for s in range(len(C))], [h(N - j) for j in C])
        if u is None or wv is None:
            return None
        for j, val in zip(C, u):
            R[j] = R.get(j, 0) - val
        for i, val in zip(I, wv):
            L[N - i] = L.get(N - i, 0) - val
    return R, L


def pmul(P, Q):
    out = {}
    for i, a in P.items():
        for j, b in Q.items():
            out[i + j] = out.get(i + j, 0) + a * b
    return out


def bracket(T, m, h):
    """`<T> = [z^m] H T`, `H(z) = nu + sum_{j>0} h_j z^j`."""
    return sum(coef * h(m - e) for e, coef in T.items() if m - e >= 0)


def fS(X, Y, N, h):
    I, C = list(X[1:]), list(Y[:-1])
    if not I:
        return h(N)
    A = [[h(i - j) for j in C] for i in I]
    u = solve(A, [h(i) for i in I])
    if u is None:
        return None
    return h(N) - sum(h(N - j) * v for j, v in zip(C, u))


def source_data(s, h):
    """Window coframes, frames, cap vectors and returns of a sampled source; None if a system is singular."""
    X, Y, N, c, q, a, m = (s[k] for k in ('X', 'Y', 'N', 'c', 'q', 'a', 'm'))
    I, C = list(X[1:]), list(Y[:-1])
    # base windows: rows/columns below a (resp. above N - a)
    ri = [i for i in I if i < a]; rc = [j for j in C if j < a]
    li = [i for i in I if i > N - a]; lc = [j for j in C if j > N - a]
    R0, L0 = {0: Fr(1)}, {0: Fr(1)}
    if ri:
        u = solve([[h(i - j) for j in rc] for i in ri], [h(i) for i in ri])
        if u is None:
            return None
        for j, v in zip(rc, u):
            R0[j] = R0.get(j, 0) - v
    if li:
        v_ = solve([[h(i - j) for i in li] for j in lc], [h(N - j) for j in lc])
        if v_ is None:
            return None
        for i, v in zip(li, v_):
            L0[N - i] = L0.get(N - i, 0) - v
    IR = [i - a for i in I if a <= i <= m]; CR = [j - a for j in C if a <= j <= m]
    IL = [i - q for i in I if q <= i <= q + c]; CL = [j - q for j in C if q <= j <= q + c]
    Ip = [i - (N - c) for i in I if N - c <= i < N]; Cp = [j - (N - c) for j in C if N - c <= j < N]
    Im = [i for i in I if 1 <= i <= c]; Cm = [j for j in C if 1 <= j <= c]
    Ucap = sorted({c} | set(Ip), reverse=True)
    Vcap = sorted({0} | set(Cm))
    l = {c: Fr(1)}
    others = [i for i in Ucap if i != c]
    if Cp:
        sol = solve([[h(i - j) for i in others] for j in Cp], [-h(c - j) for j in Cp])
        if sol is None:
            return None
        l.update(zip(others, sol))
    r = {0: Fr(1)}
    others = [j for j in Vcap if j != 0]
    if Im:
        sol = solve([[h(i - j) for j in others] for i in Im], [-h(i) for i in Im])
        if sol is None:
            return None
        r.update(zip(others, sol))
    lpoly = {c - i: v for i, v in l.items()}          # l(z) = sum l_i z^{c-i}
    rpoly = dict(r)                                   # r(z) = sum r_j z^j
    return dict(R0=R0, L0=L0, IR=IR, CR=CR, IL=IL, CL=CL, Ip=Ip, Cp=Cp, Im=Im, Cm=Cm,
                l=l, r=r, lpoly=lpoly, rpoly=rpoly, Ucap=Ucap, Vcap=Vcap)


def theta(T):
    return {e: e * v for e, v in T.items()}


def padd(*Ps):
    out = {}
    for P in Ps:
        for e, v in P.items():
            out[e] = out.get(e, 0) + v
    return out


def pscale(P, k):
    return {e: k * v for e, v in P.items()}
