r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Mark datum: a positive coincident mark calibrates in e-coordinates iff v_0 = 1 - r(E)
(window a row segment), in h-coordinates iff v_0 = 2 - r(E) (window a column), asserted in census.
Positive coincident section of prop:noncell-realization (eq:positive-section, eq:phi).

Own construction from the definitions: Row_j o E is the union of the translates E + k v
(k < j); Phi(h_j) = A^(j-1) s_{Row_j o E} with A = s_W (eq:phi); the lower native coframe g is
1 - sum u_i z^{C_i} for the probe's full beta lists; the section is eq:positive-section.
Reports, for the smallest reported instance and a random census of positive coincident marks,
whether Phi(h_j) = mu xi^j Y_j (paper) or Phi(e_j) = mu xi^j Y_j (e-coordinates), where
e_2 = h_1^2 - h_2, e_3 = h_1^3 - 2 h_1 h_2 + h_3.  Asserts: h-coordinates fail, e-coordinates hold on the smallest instance; the census reports marks
where neither coordinate calibrates (open).
"""
import random
from fractions import Fraction as Fr
from check_row_probe_caps import (betas, probe, legal_marks, is_cs, tr, normalize, content,
                                  is_skew, connected, random_skew)


def det(M):
    n = len(M); M = [r[:] for r in M]; d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return d


def schur(cells, h):
    xi, ze = betas(cells)
    f = lambda m: Fr(0) if m < 0 else (Fr(1) if m == 0 else h[m])
    return det([[f(a - b) for b in ze] for a in xi])


def smul(a, b, n):
    return [sum(a[i] * b[k - i] for i in range(k + 1) if i < len(a) and k - i < len(b)) for k in range(n)]


def sinv(a, n):
    r = [Fr(0)] * n; r[0] = 1 / a[0]
    for k in range(1, n):
        r[k] = -sum(a[i] * r[k - i] for i in range(1, k + 1) if i < len(a)) / a[0]
    return r


def lower_coframe(cells, h, q):
    xi, ze = betas(cells)
    I, C = xi[1:], ze[:-1]; n = len(I)
    f = lambda m: Fr(0) if m < 0 else (Fr(1) if m == 0 else h[m])
    A = [[f(I[i] - C[j]) for j in range(n)] for i in range(n)]
    # solve A u = (h_I)
    M = [A[i][:] + [f(I[i])] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                t = M[r][c] / M[c][c]
                M[r] = [x - t * y for x, y in zip(M[r], M[c])]
    u = [M[i][n] / M[i][i] for i in range(n)]
    g = [Fr(0)] * q; g[0] = Fr(1)
    for j in range(n):
        if C[j] < q:
            g[C[j]] -= u[j]
    return g


def window(E, w, v):
    cs = [content(x) for x in E]; lo, hi = min(cs), max(cs)
    band = sorted(x for x in E if content(x) < lo + w)
    out = []
    for mask in range(1, 1 << len(band)):
        W = {band[k] for k in range(len(band)) if mask >> k & 1}
        if len({content(x) for x in W}) == w and is_cs(W):
            r0 = min(x[0] for x in W if content(x) == lo + w - 1)
            nr = min(x[0] for x in E if content(x) == hi)
            if (nr - r0, nr + hi - r0 - (lo + w - 1)) == tuple(v) and tr(W, v) <= set(E):
                out.append(normalize(W))
    return out


def run(E, w, v, tau, seed, J=3):
    q = max(map(content, E)) - min(map(content, E)) + 1 - w
    P = {j: probe(E, v, j) for j in range(1, J + 1)}
    W = window(E, w, v)[0]
    rng = random.Random(seed)
    nc = J * q + w + 2
    lo = {m: Fr(rng.randint(-5, 5), rng.randint(1, 4)) for m in range(1, q)}
    h = dict(lo)
    for m in range(q, 4 * q + w + 8):
        h[m] = Fr(rng.randint(-9, 9), rng.randint(1, 5))
    try:
        g = lower_coframe(P[2], h, q)
    except StopIteration:
        return None
    if g[tau] == 0:
        return None
    l = smul([Fr(1)] + [lo[m] for m in range(1, q)], g, q)
    def phi(Y, S):
        Sq = [Fr(0)] * nc; Yq = [Fr(0)] * nc
        for j, s in enumerate(S):
            if j * q < nc: Sq[j * q] = s
        for j, y in enumerate(Y):
            if j * q < nc: Yq[j * q] = y
        YS = smul(Yq, Sq, nc)
        G = [Fr(0)] * nc; L = [Fr(0)] * nc
        for k in range(q): G[k] = g[k]; L[k] = l[k]
        for k in range(nc - tau):
            G[k + tau] += g[tau] * (Sq[k] - (k == 0))
            L[k + tau] += l[tau] * (YS[k] - (k == 0))
        H = smul(L, sinv(G, nc), nc)
        hv = {m: H[m] for m in range(1, nc)}
        assert all(hv[m] == lo[m] for m in range(1, q))
        A = schur(W, hv)
        return [A ** (j - 1) * schur(P[j], hv) for j in range(1, J + 1)]
    return phi


def main():
    E = frozenset([(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1)])
    marks = [m for m in legal_marks(E) if m[0] == 2 and m[1] == (-2, 1)]
    assert marks and marks[0][2] == (1, 1), marks
    w, v, ph = marks[0]; tau = 1
    cnt = {'h': 0, 'e': 0, 'neither': 0, 'degenerate': 0}
    for seed in range(1, 40):
        phi = run(E, w, v, tau, seed)
        if phi is None:
            continue
        cnt[classify(phi, seed)] += 1
    print('smallest instance (v=(-2,1))', cnt)
    assert cnt['e'] > 0 and cnt['h'] == 0 and cnt['neither'] == 0, cnt
    w2, v2, ph2 = [m for m in legal_marks(E) if m[0] == 2 and m[1] == (-1, 2)][0]
    cnt2 = {'h': 0, 'e': 0, 'neither': 0, 'degenerate': 0}
    for seed in range(1, 40):
        phi = run(E, w2, v2, 1, seed)
        if phi is not None:
            cnt2[classify(phi, seed)] += 1
    print('same E, v=(-1,2)', cnt2)
    assert cnt2['h'] > 0 and cnt2['e'] == 0 and cnt2['neither'] == 0, cnt2
    census()
    print('PASS: every positive coincident legal mark calibrates in exactly one of the h- or e-coordinates')


def classify(phi, seed):
    """'h' if Phi(h_j) = xi^j Y_j, 'e' if Phi(e_j) = xi^j Y_j, else 'neither'."""
    rng = random.Random(1000 + seed)
    Y = [Fr(1)] + [Fr(rng.randint(1, 7), rng.randint(1, 3)) for _ in range(3)]
    S = [Fr(1)] + [Fr(rng.randint(-6, 6), rng.randint(1, 3)) for _ in range(3)]
    p = phi(Y, S)
    e2 = p[0] ** 2 - p[1]; e3 = p[0] ** 3 - 2 * p[0] * p[1] + p[2]
    rh = [p[j] / Y[j + 1] for j in range(3)]
    re = [p[0] / Y[1], e2 / Y[2], e3 / Y[3]]
    geo = lambda r: r[1] == r[0] ** 2 and r[2] == r[0] ** 3
    if geo(rh) and geo(re): return 'degenerate'
    if geo(rh) and not geo(re): return 'h'
    if geo(re) and not geo(rh): return 'e'
    return 'neither'


def census(marks=8):
    """Every positive coincident legal mark of random inners: Phi(e_j)/Y_j = xi^j, never Phi(h_j)."""
    rng = random.Random(7); seen = set(); tries = 0
    stat = {'e': 0, 'h': 0, 'neither': 0, 'degenerate': 0}; mus = set()
    while sum(stat.values()) < marks and tries < 40000:
        tries += 1
        E = random_skew(rng, rng.randint(2, 4))
        if E in seen or not is_skew(E) or not connected(E) or not 2 <= len(E) <= 9:
            continue
        seen.add(E)
        for w, v, ph in legal_marks(E):
            if ph is None or ph[0] != ph[1] or not 0 < ph[0] < w:
                continue
            q = max(map(content, E)) - min(map(content, E)) + 1 - w
            if not all(is_skew(probe(E, v, j)) and connected(probe(E, v, j)) for j in (1, 2, 3)):
                continue
            phi = None
            for seed in range(1, 30):
                phi = run(E, w, v, ph[0], seed)
                if phi:
                    break
            if not phi:
                continue
            t = classify(phi, 5)
            stat[t] += 1
            rows = len({x[0] for x in E})
            # datum: the upper copy shares no row with the lower one (v_0 = 1 - r(E)) iff e-type
            assert t == ('e' if v[0] == 1 - rows else 'h'), (t, sorted(E), w, v)
    print('census', stat)
    assert stat['e'] > 0 and stat['h'] > 0 and stat['neither'] == 0, stat

if __name__ == '__main__':
    main()
