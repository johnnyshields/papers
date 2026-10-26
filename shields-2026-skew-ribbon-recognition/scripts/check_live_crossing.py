"""The live crossing on the actual ordinary chart (ph:finite-block).

Paper section `sec:comparison` (Finite comparisons on actual composition charts), proof of ph:finite-block,
ph:ordinary-source-chart, ph:effective-current, and the response series before ph:finite-block.

Build the actual ordinary composition source E = V o_mu J: fixed rows j r + b (b in B_0,
0 <= j < M) with the partial end block M r + b (b <= v), coarse rows j r + s (j in X_V); columns
likewise with C_0, t and Y_V.  Take the chart H_full = P_full / G_full of ph:ordinary-source-chart,
K_Q = (h_{Q + x - y}), and the compression W K_Q U of ph:effective-current.  Differentiate exactly
(hyper-dual numbers) in outside pulses at the point where every outside coordinate and every
positive coarse return R_1, ..., R_M is zero (the grade-zero part, which is all that meets the
first nonzero grade of the coarse array), and compare with

  one wave   d_alpha (W K_Q U)_{j,k} = -[k >= a] F_{j-k+a,i},       F_{P_i} = Lambda_{i-delta},
  two waves  d_alpha d_alpha' (W K_Q U)_{j,k}
               = -[k >= a] d_alpha' F_{j-k+a,i} - [k >= b] d_alpha F_{j-k+b,i'},
  high wave  d_{alpha_{b,i'}} F_n = d_{P'_{i'}} F_{n-(M-b)},
  denominator pulse  d_beta (W K_Q U)_{j,k} = -[k >= a] Theta_{j-k+a, j'-delta} up to one sign.

Asserts all four on the sampled legal boards satisfying the open mate implications ph:UM.  The
first also records where it FAILS off that point: with positive returns or outside coordinates
nonzero, or without ph:UM, so the identity is a grade-zero, base-point identity only.
"""

import random
import sys
from fractions import Fraction as Fr
from itertools import combinations


class HD:
    """a + b e1 + c e2 + d e1 e2 with e1^2 = e2^2 = 0."""
    __slots__ = ("a", "b", "c", "d")

    def __init__(self, a, b=0, c=0, d=0):
        self.a, self.b, self.c, self.d = Fr(a), Fr(b), Fr(c), Fr(d)

    @staticmethod
    def lift(o):
        return o if isinstance(o, HD) else HD(o)

    def __add__(self, o):
        o = HD.lift(o)
        return HD(self.a + o.a, self.b + o.b, self.c + o.c, self.d + o.d)

    __radd__ = __add__

    def __neg__(self):
        return HD(-self.a, -self.b, -self.c, -self.d)

    def __sub__(self, o):
        return self + (-HD.lift(o))

    def __mul__(self, o):
        o = HD.lift(o)
        return HD(self.a * o.a, self.a * o.b + self.b * o.a, self.a * o.c + self.c * o.a,
                  self.a * o.d + self.d * o.a + self.b * o.c + self.c * o.b)

    __rmul__ = __mul__

    def inv(self):
        a = self.a
        return HD(1 / a, -self.b / a**2, -self.c / a**2,
                  2 * self.b * self.c / a**3 - self.d / a**2)

    def nz(self):
        return self.a != 0


Z = HD(0)


def series_div(P, G, n):
    out = []
    g0 = G[0].inv()
    for m in range(n):
        acc = P[m] if m < len(P) else Z
        for k in range(1, min(m, len(G) - 1) + 1):
            acc = acc - G[k] * out[m - k]
        out.append(acc * g0)
    return out


def mat_inv(A):
    n = len(A)
    M = [row[:] + [HD(1 if i == j else 0) for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c].nz())
        M[c], M[p] = M[p], M[c]
        piv = M[c][c].inv()
        M[c] = [x * piv for x in M[c]]
        for r in range(n):
            if r != c:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def matmul(A, B):
    if not A or not B:
        return [[Z] * (len(B[0]) if B else 0) for _ in A]
    return [[sum((A[i][k] * B[k][j] for k in range(len(B))), Z) for j in range(len(B[0]))]
            for i in range(len(A))]


def ps_mat_inv(D, nt):
    k = len(D)
    D0i = mat_inv([[D[b][c][0] for c in range(k)] for b in range(k)])
    E = [D0i]
    for n in range(1, nt):
        acc = [[Z] * k for _ in range(k)]
        for m in range(1, n + 1):
            prod = matmul([[D[b][c][m] for c in range(k)] for b in range(k)], E[n - m])
            acc = [[acc[i][j] + prod[i][j] for j in range(k)] for i in range(k)]
        E.append([[-x for x in row] for row in matmul(D0i, acc)])
    return E


class Board:
    def __init__(self, r, v, M, XW, YW, s, t, Bm, Cm, w, XV, YV):
        self.__dict__.update(locals())
        self.NJ, self.S = r + v, M * r + v
        self.delta = v - w
        self.Q = M * r + self.delta
        self.B0 = sorted((set(XW) - {s}) | set(Bm))
        self.C0 = sorted((set(YW) - {t}) | set(Cm))
        self.XJ = {r + x for x in XW} | set(Bm) | (set(XW) - {s})
        self.YJ = {r + y for y in set(YW) - {t}} | set(Cm) | set(YW)
        self.rows_av = [i for i in range(v + 1, self.NJ) if i not in self.XJ]
        self.cols_av = [j for j in range(v + 1, self.NJ) if j in self.YJ]
        self.frows = [j * r + b for j in range(M) for b in self.B0] + \
            [M * r + b for b in self.B0 if b <= v]
        self.fcols = [k * r + c for k in range(M) for c in self.C0] + \
            [M * r + c for c in self.C0 if c <= v]
        self.crows = [j * r + s for j in sorted(XV)]
        self.ccols = [k * r + t for k in sorted(YV)]

    def legal(self):
        """The beta lists of a connected finer of span N_J, a square source."""
        return (all(1 <= x <= self.NJ for x in self.XJ) and all(0 <= y < self.NJ for y in self.YJ)
                and len(self.XJ) == len(self.YJ) and self.NJ in self.XJ and 0 in self.YJ
                and len(self.frows) == len(self.fcols))

    def mates(self):
        """ph:UM on the actual source."""
        XE = set(self.frows) | set(self.crows)
        YE = set(self.fcols) | set(self.ccols)
        w, Q, S = self.w, self.Q, self.S
        return (all(Q + x in XE for x in XE if 0 < x < w)
                and all(y - Q in YE for y in YE if Q < y < S))


def evaluate(bd, rng, pulses, returns, outside, fine=None):
    """W K_Q U and the responses at one chart point.  `pulses` maps (kind, a, i) to its
    infinitesimal (an HD); `fine` = (i', HD) perturbs the seed coefficient P'_{i'}."""
    rnd = lambda: Fr(rng.randint(-9, 9), rng.randint(1, 5))
    r, M = bd.r, bd.M
    Pp = [HD(0)] * (bd.NJ + 1)
    Gp = [HD(0)] * (bd.NJ + 1)
    for e in range(bd.NJ + 1):
        if e not in bd.XJ:
            Pp[e] = HD(rnd())
        if e in bd.YJ:
            Gp[e] = HD(rnd())
    Gp[bd.t] = HD(1)
    if fine is not None:
        Pp[fine[0]] = Pp[fine[0]] + fine[1]
    deg = bd.S + 1
    Pf, Gf = [Z] * deg, [Z] * deg
    for e in range(bd.NJ + 1):
        Pf[e], Gf[e] = Pf[e] + Pp[e], Gf[e] + Gp[e]
    for j in range(1, M + 1):
        Pf[bd.s + j * r] = Pf[bd.s + j * r] + (rnd() if returns else 0)
    for a in range(1, M):
        for i in bd.rows_av:
            Pf[(M - a) * r + i] = Pf[(M - a) * r + i] + (rnd() if outside else 0) + \
                pulses.get(("P", a, i), 0)
        for j in bd.cols_av:
            Gf[(M - a) * r + j] = Gf[(M - a) * r + j] + (rnd() if outside else 0) + \
                pulses.get(("G", a, j), 0)
    if not Gf[0].nz():
        return None
    nh = max(bd.Q + deg, (2 * M + 6) * r) + 3 * r + 5
    h = series_div(Pf, Gf, nh)
    H = lambda m: h[m] if 0 <= m < nh else Z

    def blk(rows, cols, sh):
        return [[H(sh + x - y) for y in cols] for x in rows]

    K11 = blk(bd.crows, bd.ccols, bd.Q)
    if bd.frows:
        try:
            Di = mat_inv(blk(bd.frows, bd.fcols, 0))
        except StopIteration:
            return None
        BD = matmul(blk(bd.crows, bd.fcols, 0), Di)
        DC = matmul(Di, blk(bd.frows, bd.ccols, 0))
        t1 = matmul(BD, blk(bd.frows, bd.ccols, bd.Q))
        t2 = matmul(blk(bd.crows, bd.fcols, bd.Q), DC)
        t3 = matmul(matmul(BD, blk(bd.frows, bd.fcols, bd.Q)), DC)
        n1, n2 = len(bd.crows), len(bd.ccols)
        WKU = [[K11[p][q] - t1[p][q] - t2[p][q] + t3[p][q] for q in range(n2)] for p in range(n1)]
    else:
        WKU = K11
    # responses from the same H
    nt = 2 * M + 6
    resp = lambda d: [H(n * r + d) for n in range(nt)]
    k = len(bd.B0)
    try:
        Ei = ps_mat_inv([[resp(b - c) for c in bd.C0] for b in bd.B0], nt) if k else []
    except StopIteration:
        return None

    def conv(x, y):
        return [sum((x[m] * y[n - m] for m in range(n + 1)), Z) for n in range(nt)]

    def vecmat(row):  # row (indexed by C0) times D(u)^{-1}
        return {b: [sum((row[ci][m] * Ei[n - m][ci][bi] for m in range(n + 1)
                         for ci in range(k)), Z) for n in range(nt)]
                for bi, b in enumerate(bd.B0)}

    L = vecmat([resp(bd.s - c) for c in bd.C0])

    def Lam(b):
        if b < 0:
            return [Z] * nt
        q, rem = divmod(b, r)
        base = [HD(-1)] + [Z] * (nt - 1) if rem == bd.s else L.get(rem, [Z] * nt)
        return [Z] * q + base[: nt - q]

    def Theta(d):
        th = resp(bd.s - d)
        for b in bd.B0:
            th = [x - y for x, y in zip(th, conv(L[b], resp(b - d)))]
        return th

    return WKU, Lam, Theta


def sample_boards(rng):
    for r in range(2, 5):
        for v in range(0, r):
            for M in (3, 4):
                pts = list(range(v + 1))
                for nx in range(1, v + 2):
                    for XW in combinations(pts, nx):
                        for YW in combinations(pts, nx):
                            for s in XW:
                                for t in YW:
                                    priv = list(range(v + 1, r))
                                    for nb in range(len(priv) + 1):
                                        Bm, Cm = rng.sample(priv, nb), rng.sample(priv, nb)
                                        for w in range(r):
                                            if w == v:
                                                continue
                                            XV = {M} | {j for j in range(1, M) if rng.random() < .5}
                                            YV = {0} | set(rng.sample(range(1, M), len(XV) - 1))
                                            bd = Board(r, v, M, XW, YW, s, t, Bm, Cm, w, XV, YV)
                                            if bd.legal() and bd.rows_av:
                                                yield bd


def entries(bd):
    for p, j in enumerate(sorted(bd.XV)):
        for q, k in enumerate(sorted(bd.YV)):
            yield p, j, q, k


def one_wave(bd, rng, returns=False, outside=False):
    a, i = rng.randint(1, bd.M - 1), rng.choice(bd.rows_av)
    out = evaluate(bd, rng, {("P", a, i): HD(0, 1)}, returns, outside)
    if out is None:
        return None
    WKU, Lam, _ = out
    F = Lam(i - bd.delta)
    bad = 0
    for p, j, q, k in entries(bd):
        n = j - k + a
        rhs = -F[n].a if (k >= a and n >= 0) else 0
        bad += WKU[p][q].b != rhs
    return bad


def two_waves(bd, rng):
    a, i = rng.randint(1, bd.M - 1), rng.choice(bd.rows_av)
    b, i2 = rng.randint(1, bd.M - 1), rng.choice(bd.rows_av)
    if (a, i) == (b, i2):
        return None
    out = evaluate(bd, rng, {("P", a, i): HD(0, 1), ("P", b, i2): HD(0, 0, 1)}, False, False)
    if out is None:
        return None
    WKU, Lam, _ = out
    F1, F2 = Lam(i - bd.delta), Lam(i2 - bd.delta)
    bad = 0
    for p, j, q, k in entries(bd):
        rhs = 0
        if k >= a and j - k + a >= 0:
            rhs -= F1[j - k + a].c      # d_{alpha_{b,i2}} F_{j-k+a,i}
        if k >= b and j - k + b >= 0:
            rhs -= F2[j - k + b].b      # d_{alpha_{a,i}} F_{j-k+b,i2}
        bad += WKU[p][q].d != rhs
    return bad


def high_wave(bd, rng):
    """d_{alpha_{b,i2}} F_n = d_{P'_{i2}} F_{n-(M-b)}: the high variation is u^{M-b} times the
    fine variation."""
    b, i2 = rng.randint(1, bd.M - 1), rng.choice(bd.rows_av)
    i = rng.choice(bd.rows_av)
    st = rng.getstate()
    hi = evaluate(bd, rng, {("P", b, i2): HD(0, 1)}, False, False)
    rng.setstate(st)
    lo = evaluate(bd, rng, {}, False, False, fine=(i2, HD(0, 1)))
    if hi is None or lo is None:
        return None
    Fh, Fl = hi[1](i - bd.delta), lo[1](i - bd.delta)
    c = bd.M - b
    return sum(Fh[n].b != (Fl[n - c].b if n >= c else 0) for n in range(len(Fh)))


def denominator(bd, rng):
    """A denominator pulse: the response is Theta, with one sign common to all boards."""
    if not bd.cols_av:
        return None
    a, j0 = rng.randint(1, bd.M - 1), rng.choice(bd.cols_av)
    out = evaluate(bd, rng, {("G", a, j0): HD(0, 1)}, False, False)
    if out is None:
        return None
    WKU, _, Theta = out
    F = Theta(j0 - bd.delta)
    res = {1: 0, -1: 0}
    for sign in (1, -1):
        for p, j, q, k in entries(bd):
            n = j - k + a
            rhs = sign * F[n].a if (k >= a and n >= 0) else 0
            res[sign] += WKU[p][q].b != rhs
    return res


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    stats = {}
    den_signs = {1: 0, -1: 0}
    den_tested = 0
    for bd in sample_boards(rng):
        um = bd.mates()
        for label, f in (("one", lambda: one_wave(bd, rng)),
                         ("one+returns", lambda: one_wave(bd, rng, returns=True)),
                         ("one+outside", lambda: one_wave(bd, rng, outside=True)),
                         ("two", lambda: two_waves(bd, rng)),
                         ("high", lambda: high_wave(bd, rng))):
            res = f()
            if res is None:
                continue
            key = (label, um)
            t, bad = stats.get(key, (0, 0))
            stats[key] = (t + 1, bad + (res > 0))
        if um:
            res = denominator(bd, rng)
            if res is not None:
                den_tested += 1
                for sg in (1, -1):
                    den_signs[sg] += res[sg] > 0
    for key in sorted(stats):
        print(f"{key[0]:12s} UM={key[1]!s:5s} tested {stats[key][0]:4d} failing {stats[key][1]:4d}")
    print("denominator pulse, UM boards:", den_tested, "failing with sign +1:", den_signs[1],
          "with sign -1:", den_signs[-1])
    for label in ("one", "two", "high"):
        t, bad = stats[(label, True)]
        assert t > 0 and bad == 0, label
    assert stats[("one+returns", True)][1] > 0 and stats[("one+outside", True)][1] > 0
    assert den_tested > 0 and min(den_signs.values()) == 0
    print("ALL PASS")


if __name__ == "__main__":
    main()
