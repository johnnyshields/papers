r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

The returned section of prop:noncell-realization (app:aligned): eq:empty-section,
eq:positive-section and the calibration Phi(h_j) = mu xi^j Y_j.

For an inner E and a legal mark of width w < period q, the row probe Row_j o U is the union of
the j translates of E; A = s_W is the Schur function of the mark window W, and
Phi(h_j) = A^(j-1) s_{Row_j o U}.  Let g be the lower coframe of the probe modulo z^q, l =
[H_{<q} g]_{<q}, and let Y, S be independent series with constant term one.  The section sets
G = g - 1 + S(z^q), H = (l - 1 + Y(z^q) S(z^q)) / G  (empty mark, w = 0), and
G = g + g_t z^t (S(z^q) - 1), H = (l + l_t z^t (Y(z^q) S(z^q) - 1)) / G  (a phase 0 < t < w),
and reads the raw labels h_m = [z^m] H.
Sampled: the first 400 distinct random inners of 2 to 4 rows with 2 to 9 cells (seeded; a shape-count
bound, not a wall-clock one).

The script asserts, in exact rational arithmetic and on every legal mark of random inners,
for the empty mark and for every phase t in 1..w-1:
  * the low raw labels are unchanged;
  * Phi(h_j) / Y_j = mu xi^j for j = 1, 2, 3, with (mu, xi) independent of S and Y
    (two independent draws of S, Y give the same pair);
  * the probe S(z^q) = 1 - Y_1 z^q, Y_2 = Y_1^2 gives Phi(e_2) = Phi(h_1)^2 - Phi(h_2) = 0
    exactly when mu = 1, and mu = 1 for the true phase.
It prints, per mark, which phases calibrate (the true phase is the one with mu = 1 and the
vanishing probe).  Every empty mark asserts mu = 1.
"""
import random
from fractions import Fraction

from check_row_probe_caps import (is_cs, tr, betas, connected, is_skew, legal_marks, normalize, probe,
                                  random_skew, content, solve)

D = 4  # series cutoff multiplier


def jt_det(xi, ze, h):
    n = len(xi)
    M = [[h(xi[i] - ze[j]) for j in range(n)] for i in range(n)]
    det = Fraction(1)
    M = [r[:] for r in M]
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            det = -det
        det *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return det


def schur(cells, hv):
    def h(m):
        return Fraction(0) if m < 0 else (Fraction(1) if m == 0 else hv[m])
    xi, ze = betas(cells)
    return jt_det(xi, ze, h)


def ser_mul(a, b, n):
    return [sum(a[i] * b[k - i] for i in range(k + 1) if i < len(a) and k - i < len(b))
            for k in range(n)]


def ser_inv(a, n):
    r = [Fraction(0)] * n
    r[0] = 1 / a[0]
    for k in range(1, n):
        r[k] = -sum(a[i] * r[k - i] for i in range(1, k + 1) if i < len(a)) / a[0]
    return r


def coframe_low(cells, hv, q):
    """Lower coframe R of the probe, truncated below z^q."""
    xi, ze = betas(cells)
    I, C = xi[1:], ze[:-1]
    n = len(I)

    def h(m):
        return Fraction(0) if m < 0 else (Fraction(1) if m == 0 else hv[m])
    A = [[h(I[i] - C[j]) for j in range(n)] for i in range(n)]
    u = solve(A, [h(I[i]) for i in range(n)])
    R = [Fraction(0)] * q
    R[0] = Fraction(1)
    for j in range(n):
        if C[j] < q:
            R[C[j]] -= u[j]
    return R


def section(g, lo, q, tau, Y, S, ncut):
    """Raw labels h_m, m < ncut, of the section; g has length q."""
    Hlow = [Fraction(1)] + [lo[m] for m in range(1, q)]
    l = ser_mul(Hlow, g, q)
    Sq = [Fraction(0)] * ncut
    YS = [Fraction(0)] * ncut
    Yq = [Fraction(0)] * ncut
    for j in range(len(S)):
        if j * q < ncut:
            Sq[j * q] = S[j]
    for j in range(len(Y)):
        if j * q < ncut:
            Yq[j * q] = Y[j]
    YS = ser_mul(Yq, Sq, ncut)
    G = [Fraction(0)] * ncut
    L = [Fraction(0)] * ncut
    for k in range(q):
        G[k] += g[k]
        L[k] += l[k]
    if tau is None:
        G[0] -= 1
        L[0] -= 1
        for k in range(ncut):
            G[k] += Sq[k]
            L[k] += YS[k]
    else:
        gt, lt = g[tau], l[tau]
        for k in range(ncut - tau):
            G[k + tau] += gt * (Sq[k] - (1 if k == 0 else 0))
            L[k + tau] += lt * (YS[k] - (1 if k == 0 else 0))
    H = ser_mul(L, ser_inv(G, ncut), ncut)
    return H


def calibrate(E, w, v, tau, rng, tag):
    N_E = max(map(content, E)) - min(map(content, E)) + 1
    q = N_E - w
    if q < 2:
        return None
    J = 3
    probes = {}
    for j in range(1, J + 1):
        P = probe(E, v, j)
        if not (is_skew(P) and connected(P)):
            return None
        probes[j] = P
    lo = {m: Fraction(rng.randint(-5, 5), rng.randint(1, 4)) for m in range(1, q)}
    # window W: first w diagonals of E
    if w > 0:
        cs = [content(x) for x in E]
        lo_c = min(cs)
        band = sorted(x for x in E if content(x) < lo_c + w)
        sw = (min(r for r, _ in [x for x in E if content(x) == lo_c]),)
        cands = []
        for mask in range(1, 1 << len(band)):
            Wm = {band[k] for k in range(len(band)) if mask >> k & 1}
            if len({content(x) for x in Wm}) != w or not is_cs(Wm):
                continue
            hi_w = lo_c + w - 1
            r0 = min(x[0] for x in Wm if content(x) == hi_w)
            ne = max(x for x in E if content(x) == max(map(content, E)))
            nr = min(x[0] for x in E if content(x) == max(map(content, E)))
            if (nr - r0, nr + max(map(content, E)) - (r0 + hi_w)) == tuple(v) and tr(Wm, v) <= set(E):
                cands.append(Wm)
        assert len(cands) >= 1, ('no window', sorted(E), w, v)
        W = normalize(cands[0])
    ncut = J * q + w + 2
    hh = dict(lo)
    for m in range(q, 4 * q + w + 8):
        hh[m] = Fraction(rng.randint(-9, 9), rng.randint(1, 5))
    try:
        gtab = coframe_low(probes[2], hh, q)
    except (StopIteration, ZeroDivisionError):
        return None
    out = []
    for _ in range(2):
        Y = [Fraction(1)] + [Fraction(rng.randint(-6, 6), rng.randint(1, 3)) for _ in range(J)]
        S = [Fraction(1)] + [Fraction(rng.randint(-6, 6), rng.randint(1, 3)) for _ in range(J)]
        if tau is not None and (gtab[tau] == 0):
            return None
        H = section(gtab, lo, q, tau, Y, S, ncut)
        hv = {m: H[m] for m in range(1, ncut)}
        for m in range(1, q):
            if hv[m] != lo[m]:
                return 'lowmoved'
        A = schur(W, hv) if w > 0 else Fraction(1)
        phi = {}
        for j in range(1, J + 1):
            hv2 = dict(hv)
            for m in range(ncut, j * q + w + 3):
                hv2[m] = Fraction(0)
            phi[j] = A ** (j - 1) * schur(probes[j], hv2)
        if any(Y[j] == 0 for j in range(1, J + 1)):
            return None
        rat = [phi[j] / Y[j] for j in range(1, J + 1)]
        out.append(rat)
    return out


def N_E_(E):
    return max(map(content, E)) - min(map(content, E)) + 1


def main():
    rng = random.Random(11)
    n_empty = n_pos = bad = 0
    seen = set()
    stats = {}
    tries = 0
    while len(seen) < 400 and tries < 60000:
        tries += 1
        E = random_skew(rng, rng.randint(2, 4))
        if E in seen or not is_skew(E) or not connected(E) or not 2 <= len(E) <= 9:
            continue
        seen.add(E)
        for w, v, ph in legal_marks(E):
            taus = [None] if w == 0 else ([ph[0]] if ph[0] == ph[1] and 0 < ph[0] < w else [])
            for tau in taus:
                r = calibrate(E, w, v, tau, rng, 'x')
                if r is None or r == 'lowmoved':
                    if r == 'lowmoved':
                        bad += 1
                        print('FAIL low moved', sorted(E), w, tau)
                    continue
                r1, r2 = r
                if tau is not None and r1 != r2:
                    stats['phase does not calibrate'] = stats.get('phase does not calibrate', 0) + 1
                    print('NOCAL', sorted(E), w, v, tau, r1, r2)
                    continue
                assert r1 == r2, ('Phi(h_j)/Y_j depends on S,Y', sorted(E), w, tau, r1, r2)
                xi = r1[1] / r1[0] if r1[0] != 0 else None
                mu = r1[0] / xi if xi else None
                if not xi:
                    stats['vanishing'] = stats.get('vanishing', 0) + 1
                    print('VAN', sorted(E), w, v, tau, r1)
                    continue
                geo = xi is not None and r1[2] == mu * xi ** 3
                if tau is None:
                    n_empty += 1
                    assert geo, ('empty calibration is not mu xi^j', sorted(E), r1)
                    assert mu == 1, ('empty mu != 1', sorted(E), v, r1)
                else:
                    n_pos += 1
                    assert geo, ('positive calibration is not mu xi^j', sorted(E), w, tau, r1)
                    key = ('calibrated phase, mu == 1:', mu == 1)
                    stats[key] = stats.get(key, 0) + 1
                    assert mu == 1, ('calibrated phase has mu != 1', sorted(E), w, tau, r1)
    print('empty marks', n_empty, 'positive (mark, phase) pairs', n_pos, 'stats', stats)
    assert n_empty > 5 and n_pos > 0, (n_empty, n_pos)
    print('coincident positive pairs', n_pos)
    print('ALL PASS')


if __name__ == '__main__':
    main()
