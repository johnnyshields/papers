r"""Paper section `sec:boundary` (Boundary comparisons and actual marked factors), ge:crossed-cover and
ge:carried-signed (the signed-window comparisons).

Instances are built from compositions rather than from a parent: for every ordinary inner K with a
legal mark mu (case (a) or (b)) of period g = f >= 2 and width a, every connected outer A, B of at
least two cells, put S = A o_mu K, and T = B o_mu K (carried) or T = B o_{mu*} K (crossed, mu* the
half-turned mark), of one span H = m f + a with m >= 2.  For every D and L the pair is kept when
the real signed comparisons hold exactly:

  X_T(x + D) - X_S(x) = [x = p],   Y_T(x + D) - Y_S(x) = -[x = q]      (0 <= x <= V = H - D),
  X_T(x - L) - X_S(x) = -[x = l],  Y_T(x - L) - Y_S(x) = [x = j]       (L <= x <= H),

with R = D + L and the parameter ranges g <= L <= p <= V - q, L <= l <= V, R <= j <= H.  This is the
(+X, -Y) / (-X, +Y) order of the first row of the four-order table; the other three orders are
transports of it by antitransposition and are not run separately.  Instances failing only the
parameter ranges are counted as controls.

ge:crossed-cover.  Crossed instances: the crossed full mark is carried (mu = mu*), or T is the
half-turn of S (hence B = A* by composition through the same mark).  Asserted on every instance with
mu != mu*; counted otherwise.
ge:carried-signed.  Carried instances with S != T: g divides L or g divides D.  The root of period
d = gcd(g, L, D) and the case g = 1 are not constructed here (see the coverage table).
"""
from _gluing_common import compose, normalize, rotate, rotated_mark, span
from check_two_copy_flags import betas, diagrams, marks

INNER = 5
OUTER = 8
LIMIT = 22


def indicator(L, size):
    return [1 if x in L else 0 for x in range(size + 1)]


def main():
    outers = [A for A in diagrams(OUTER) if len(A) >= 2]
    counts = {'crossed': 0, 'crossed_nonself': 0, 'carried': 0, 'out_of_range': 0}
    for K in diagrams(INNER):
        for mu in marks(K):
            if not mu.lower or mu.case not in 'ab' or mu.period < 2:
                continue
            f, a = mu.period, mu.width
            nu = rotated_mark(mu)
            sources = {}
            for A in outers:
                S = compose(A, mu)
                H = span(S)
                if H // f >= 2 and H % f == a and len(S) <= LIMIT:
                    sources.setdefault(H, []).append(S)
            for mode, mark2 in (('carried', mu), ('crossed', nu)):
                targets = {}
                for B in outers:
                    T = compose(B, mark2)
                    H = span(T)
                    if H // f >= 2 and H % f == a and len(T) <= LIMIT:
                        targets.setdefault(H, []).append(T)
                for H, Ss in sources.items():
                    for S in Ss:
                        XS, YS = betas(S)
                        xs, ys = indicator(XS, H + 1), indicator(YS, H + 1)
                        for T in targets.get(H, []):
                            if mode == 'carried' and S == T:
                                continue
                            XT, YT = betas(T)
                            xt, yt = indicator(XT, H + 1), indicator(YT, H + 1)
                            for D in range(1, H):
                                V = H - D
                                dx = [xt[x + D] - xs[x] for x in range(V + 1)]
                                dy = [yt[x + D] - ys[x] for x in range(V + 1)]
                                if sorted(dx) != sorted([0] * V + [1]) or \
                                        sorted(dy) != sorted([-1] + [0] * V):
                                    continue
                                p, q = dx.index(1), dy.index(-1)
                                for L in range(1, H):
                                    ex = [xt[x - L] - xs[x] for x in range(L, H + 1)]
                                    ey = [yt[x - L] - ys[x] for x in range(L, H + 1)]
                                    if sorted(ex) != sorted([0] * (H - L) + [-1]) or \
                                            sorted(ey) != sorted([1] + [0] * (H - L)):
                                        continue
                                    l, j = L + ex.index(-1), L + ey.index(1)
                                    R = D + L
                                    if not (f <= L <= p <= V - q and L <= l <= V and R <= j <= H):
                                        counts['out_of_range'] += 1
                                        continue
                                    if mode == 'crossed':
                                        counts['crossed'] += 1
                                        if nu != mu:
                                            counts['crossed_nonself'] += 1
                                            assert T == normalize(rotate(S)), \
                                                (sorted(K), sorted(S), sorted(T))
                                    else:
                                        counts['carried'] += 1
                                        assert L % f == 0 or D % f == 0, \
                                            (sorted(S), sorted(T), f, L, D)
    assert counts['carried'] > 0 and counts['crossed'] > 0 and counts['out_of_range'] > 0
    print(f'ge:crossed-cover / ge:carried-signed: {counts}')
    print('ALL PASS')


if __name__ == '__main__':
    main()
