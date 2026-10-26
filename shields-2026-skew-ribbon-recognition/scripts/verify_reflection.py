r"""Paper section `sec:boundary` (Boundary comparisons and actual marked factors), ge:ordinary-reflection
and ge:zero-port (the orientation and mixed-impossibility clauses).

ge:ordinary-reflection.  For an ordinary inner J (case (a) mark mu of period r, width v, contacts
s, t) put B = X_W u B_- (row native word, return slot s filled by one) and C = Y_W u C_- (column
native word, return slot t filled), both read modulo r.  If B(z) = C((s + t - z) mod r) for all
0 <= z < r, then s + t = v and the half-turn of the full marked inner is the full marked inner.
Read literally with sigma = s, tau = t, c = sigma + tau, a = v.  Every connected J up to CELLS cells
and every case (a) mark is tried; the number satisfying the hypothesis is asserted positive.

ge:zero-port.  Two charts S = A o_mu K, T = B o_nu K with H = m f + a, m >= 2 and a window
X_T(x + u) = X_S(x), 0 <= x <= H - u, H - u >= f - 1.  The "row-port phases align" clause is not
transcribed (the sentence does not say which quantity "phase" is).  Checked: when nu is the half-turned
mark of mu (crossed) and the mark is mixed, no such window exists (crossed mixed orientations are
impossible); when it is ordinary the half-turn of the mark equals the mark ("becomes carried").
Outers: every connected A, B of at most OUTER cells with span at least 2.
"""
from _gluing_common import compose, rotated_mark, span
from check_two_copy_flags import betas, diagrams, marks, phases

CELLS = 11
KCELLS = 7
OUTER = 6


def main():
    refl = hit = 0
    for J in diagrams(CELLS):
        XJ, YJ = betas(J)
        for mu in marks(J):
            if mu.case != 'a' or not mu.lower:
                continue
            r, v = mu.period, mu.width
            s, t = phases(mu)
            XW, YW = betas(mu.lower)
            B = (set(XW) | {x for x in XJ if v < x < r})
            C = (set(YW) | {y for y in YJ if v < y < r})
            if all((z in B) == (((s + t - z) % r) in C) for z in range(r)):
                refl += 1
                assert s + t == v, (sorted(J), s, t, v)
                assert rotated_mark(mu) == mu, sorted(J)
    assert refl > 0
    print(f'ge:ordinary-reflection: {refl} marks with B(z) = C(s + t - z); each has s + t = v and '
          f'equals its half-turn')
    outers = [A for A in diagrams(OUTER) if span(A) >= 2]
    windows = crossed_mixed = ordinary_selfrot = 0
    for K in diagrams(KCELLS):
        for mu in marks(K):
            if not mu.lower or mu.period < 2:
                continue
            nu = rotated_mark(mu)
            f, a = mu.period, mu.width
            mixed = mu.case in 'cd'
            if not mixed and nu == mu:
                ordinary_selfrot += 1
            Ss = {}
            Ts = {}
            for A in outers:
                S = compose(A, mu)
                T = compose(A, nu)
                Ss[S] = betas(S)[0]
                Ts[T] = betas(T)[0]
            for S, XS in Ss.items():
                H = span(S)
                if H // f < 2 or H % f != a:
                    continue
                for T, XT in Ts.items():
                    if span(T) != H:
                        continue
                    for u in range(0, H - f + 2):
                        if all((x + u in XT) == (x in XS) for x in range(H - u + 1)):
                            windows += 1
                            if mixed:
                                crossed_mixed += 1
                            else:
                                assert nu == mu, (sorted(K), sorted(mu.lower), u)
    assert crossed_mixed == 0, crossed_mixed
    print(f'ge:zero-port: {windows} crossed windows (ordinary ones all on self-rotational marks); '
          f'crossed mixed windows: {crossed_mixed}')
    print('ALL PASS')


if __name__ == '__main__':
    main()
