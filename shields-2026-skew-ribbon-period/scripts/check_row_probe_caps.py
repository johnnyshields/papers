r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Row-probe caps below the period.

Section: app:aligned, lem:conormal-caps (eq:whole-cap-product, the native window coframes).

For a connected inner E and a mark of width w and period q = N_E - w, the row probe
Row_K o U is the union of the translates E + j v, 0 <= j < K.  With full beta lists
X = (N, I), Y = (C, 0) of the probe, A = JT(I, C), u = A^-1 (h_i), v = (h_{N-c}) A^-1, the
endpoint coframes are R = 1 - sum u_j z^{C_j} and L = 1 - sum v_i z^{N - I_i}.

The script asserts, for every legal mark (conditions I-IV, checked on a finite window of the
periodic union) of random inners, and K = 2, 3, 4:
  * the probe has singleton height cuts H(q - 1) = 1 and H(N - q) = 1;
  * the coefficients [z^t] R L, t < q, do not move when the labels h_m, m >= q, are resampled
    (exact rational arithmetic at random points);
  * those coefficients do not depend on K.
The legality filter is load-bearing: over all overlap marks whose end windows are translates,
legal or not, the height cuts fail on a quarter of the cases.
"""
import random
from fractions import Fraction


def normalize(cells):
    mi = min(i for i, _ in cells)
    mj = min(j for _, j in cells)
    return frozenset((i - mi, j - mj) for i, j in cells)


def is_skew(cells):
    rows = {}
    for i, j in cells:
        rows.setdefault(i, []).append(j)
    for i, js in rows.items():
        js.sort()
        if js != list(range(js[0], js[-1] + 1)):
            return False
    ks = sorted(rows)
    if ks != list(range(ks[0], ks[-1] + 1)):
        return False
    for a, b in zip(ks, ks[1:]):  # row a is north of row b
        la, ra = rows[a][0], rows[a][-1]
        lb, rb = rows[b][0], rows[b][-1]
        if not (lb <= la and rb <= ra):
            return False
    return True


def connected(cells):
    cells = set(cells)
    st = [next(iter(cells))]
    seen = {st[0]}
    while st:
        i, j = st.pop()
        for d in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            x = (i + d[0], j + d[1])
            if x in cells and x not in seen:
                seen.add(x)
                st.append(x)
    return len(seen) == len(cells)


def content(x):
    return x[1] - x[0]


def betas(cells):
    rows = {}
    for i, j in cells:
        rows.setdefault(i, []).append(j)
    ks = sorted(rows)
    lam = [max(rows[i]) + 1 for i in ks]
    mu = [min(rows[i]) for i in ks]
    R = len(ks)
    xi = [lam[r] - r for r in range(R)]
    ze = [mu[r] - r for r in range(R)]
    c = ze[-1]
    return [x - c for x in xi], [z - c for z in ze]


def solve(A, b):
    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]


def coframe_product(cells, hv):
    xi, ze = betas(cells)
    N = xi[0]
    I, C = xi[1:], ze[:-1]
    n = len(I)

    def h(m):
        return Fraction(0) if m < 0 else (Fraction(1) if m == 0 else hv[m])
    A = [[h(I[i] - C[j]) for j in range(n)] for i in range(n)]
    u = solve(A, [h(I[i]) for i in range(n)])
    At = [[A[j][i] for j in range(n)] for i in range(n)]
    v = solve(At, [h(N - C[j]) for j in range(n)])
    Rp = [Fraction(0)] * (N + 1)
    Lp = [Fraction(0)] * (N + 1)
    Rp[0] += 1
    Lp[0] += 1
    for j in range(n):
        Rp[C[j]] -= u[j]
    for i in range(n):
        Lp[N - I[i]] -= v[i]
    prod = [sum(Rp[a] * Lp[t - a] for a in range(t + 1)) for t in range(N + 1)]
    return prod, xi, ze, N


def height(xi, ze, j):
    return sum(1 for y in ze if y <= j) - sum(1 for x in xi if x <= j)


def probe(E, v, K):
    return normalize({(i + k * v[0], j + k * v[1]) for k in range(K) for i, j in E})


def is_cs(D):
    return len(D) > 0 and is_skew(D) and connected(D)


def tr(D, v):
    return {(i + v[0], j + v[1]) for i, j in D}


def diag_rows(D, c):
    return [x[0] for x in D if content(x) == c]


def legal_marks(E):
    """Every legal mark (conditions I-IV) on E, with its phases (None for the empty mark)."""
    E = set(E)
    cs = [content(x) for x in E]
    lo, hi = min(cs), max(cs)
    N = hi - lo + 1
    sw = (min(diag_rows(E, lo)), min(diag_rows(E, lo)) + lo)
    ne = (min(diag_rows(E, hi)), min(diag_rows(E, hi)) + hi)
    out = [(0, (ne[0] - sw[0], ne[1] - sw[1] + 1), None)]
    for w in range(1, N):
        band = sorted(x for x in E if content(x) <= lo + w - 1)
        for mask in range(1, 1 << len(band)):
            W = {band[k] for k in range(len(band)) if mask >> k & 1}
            if sw not in W or not is_cs(W) or len({content(x) for x in W}) != w:
                continue
            Wne = (min(diag_rows(W, lo + w - 1)), min(diag_rows(W, lo + w - 1)) + lo + w - 1)
            v = (ne[0] - Wne[0], ne[1] - Wne[1])
            up = tr(W, v)
            if not up <= E:
                continue
            q = v[1] - v[0]
            if not (0 <= w < q):
                continue
            if not (is_cs(E - W) and is_cs(E - up)):
                continue
            # I: maximality
            maximal = True
            for mask2 in range(1 << len(band)):
                W2 = {band[k] for k in range(len(band)) if mask2 >> k & 1}
                if not (W < W2) or not is_skew(W2):
                    continue
                if any(tr(W2, (ne[0] - x[0], ne[1] - x[1])) <= E for x in W2):
                    maximal = False
                    break
            if not maximal:
                continue
            # IV on a finite window of the periodic union
            O = E - W - up
            per = set()
            for k in range(-6, 7):
                per |= tr(E, (k * v[0], k * v[1]))
            ok = True
            for k in range(-3, 4):
                Ok = tr(O, (k * v[0], k * v[1]))
                hm = {x for x in Ok if (x[0] + 1, x[1] + 1) in Ok}
                for m in range(-3, 4):
                    Wm = tr(W, (m * v[0], m * v[1]))
                    hw = {x for x in per if (x[0] + 1, x[1] + 1) in Wm} | \
                        {x for x in Wm if (x[0] + 1, x[1] + 1) in per}
                    if any(abs(x[0] - y[0]) + abs(x[1] - y[1]) == 1 for x in hm for y in hw):
                        ok = False
            if not ok:
                continue
            p = v[0]

            def lo_(a):
                return min(diag_rows(E, lo + a))

            def hi_(a):
                return max(diag_rows(E, lo + a))

            def tl(a):
                return lo_(a + q) - p - lo_(a) > 0 or hi_(a + q) - p - hi_(a) < 0

            def tu(a):
                return lo_(a + q) - p - lo_(a) < 0 or hi_(a + q) - p - hi_(a) > 0
            s_ = next((a for a in range(w) if tl(a)), w)
            t_ = max((a + 1 for a in range(w) if tu(a)), default=0)
            out.append((w, v, (s_, t_)))
    return out


def random_skew(rng, rows):
    r = []
    left, right = 0, rng.randint(0, 3)
    for _ in range(rows):
        r.append((left, right))
        nl = rng.randint(left, right)
        nr = rng.randint(nl, right + 3)
        nr = max(nr, nl)
        left, right = nl + rng.randint(0, 0), nr
    cells = set()
    for k, (a, b) in enumerate(r):
        for j in range(a, b + 1):
            cells.add((-k, j))
    return normalize(cells)


def main():
    rng = random.Random(7)
    tested = fails = 0
    seen = set()
    for _ in range(4000):
        E = random_skew(rng, rng.randint(1, 3))
        if E in seen or not is_skew(E) or not connected(E) or len(E) < 2:
            continue
        seen.add(E)
        for w, v, ph in legal_marks(E):
            N_E = max(map(content, E)) - min(map(content, E)) + 1
            q = N_E - w
            if q < 2:
                continue
            results = {}
            lo = {m: Fraction(rng.randint(-9, 9), rng.randint(1, 5)) for m in range(1, q)}
            for K in (2, 3, 4):
                G = probe(E, v, K)
                if not (is_skew(G) and connected(G)):
                    break
                xi, ze = betas(G)
                N = xi[0]
                assert N == K * q + w, (E, w, v, K, N)
                hs = [height(xi, ze, q - 1), height(xi, ze, N - q)]
                vals = []
                for _ in range(2):
                    hv = dict(lo)
                    for m in range(q, N + 1):
                        hv[m] = Fraction(rng.randint(-9, 9), rng.randint(1, 5))
                    try:
                        prod, *_ = coframe_product(G, hv)
                    except (StopIteration, ZeroDivisionError):
                        prod = None
                    vals.append(prod)
                if None in vals:
                    continue
                low_fixed = vals[0][:q] == vals[1][:q]
                results[K] = (hs, low_fixed, lo, vals[0][:q])
                tested += 1
                if hs != [1, 1] or not low_fixed:
                    fails += 1
                    print('FAIL', sorted(E), 'w', w, 'v', v, 'phases', ph, 'K', K,
                          'heights', hs, 'low fixed', low_fixed)
            ks = [results[K][3] for K in results]
            if len(set(map(tuple, ks))) > 1:
                fails += 1
                print('FAIL K-dependence', sorted(E), 'w', w, 'v', v)
    print('tested', tested, 'failures', fails, 'inners', len(seen))
    assert tested > 50
    assert fails == 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
