r"""Paper section `app:cofaces` (Cofaces, two-copy identities, and native residues), ph:zero-matrix and
the word conclusions.

This script checks the native signature consumed by ph:zero-matrix and ge:zero-matrix-finish,
not the vanishing of the rational response matrix or the whole Schur-equal comparison.
For each legal type (d) mark, use B=X_W union B_- and
C=(Y_W without t) union C_- union {s}.  Require complete row closure under delta modulo r,
but require column closure only on classes foreign to the two actual port residues.
The exceptional classes are retained with their actual occupancies; they are not made full.

For every connected J through CELLS cells and every 0<w<r, w!=v, at gcd g>=2, assert the
complete row classes, full/empty foreign column classes, distinct port residues, total port
occupancy r/g, |T|=|R|-1, and 0<v mod g<g.  For v<g, southwest-normalize the proposed
root flags and assert a direct proper factorization of J through that root, retaining the
literal overlap, type (d), contacts, and legal period and width.  Independently search actual
legal compositions for a smaller-period chart on every J.  The whole-parent equality and
improved source minimum remain outside this check.
"""
from math import gcd

from _gluing_common import compose, is_connected_skew, legal, normalize, span
from check_two_copy_flags import betas, diagrams, marks, phases
from verify_endpoint_splice import from_flags

CELLS = 13
OUTER = 9
TABLE_IN = 9
TABLE_OUT = 9


def main():
    outers = list(diagrams(max(OUTER, TABLE_OUT)))
    table = {}
    for K in diagrams(TABLE_IN):
        for nu in marks(K):
            for A in outers:
                if len(A) <= TABLE_OUT and len(A) * len(K) <= 60 \
                        and span(A) * nu.period + nu.width <= CELLS:
                    P = compose(A, nu)
                    if len(P) <= CELLS:
                        table.setdefault(P, set()).add((nu.period, nu.width))
    hyp = d0 = rooted = partial_ports = 0
    for J in diagrams(CELLS):
        XJ, YJ = betas(J)
        for mu in marks(J):
            if mu.case != 'd' or not mu.lower:
                continue
            r, v = mu.period, mu.width
            s, t = phases(mu)
            XW, YW = betas(mu.lower)
            B = set(XW) | {x for x in XJ if v < x < r}
            C = (set(YW) - {t}) | {y for y in YJ if v < y < r} | {s}
            for w in range(1, r):
                if w == v:
                    continue
                dd = (v - w) % r
                g = gcd(r, v - w)
                ports = {s % g, t % g}
                if g < 2 or not all(((b + dd) % r) in B for b in B) or \
                        not all(((c + dd) % r) in C for c in C if c % g not in ports):
                    continue
                hyp += 1
                # ge:zero-matrix-finish / ge:zero-second-response: a proper full legal factor of
                # period g | r, 2 <= g < r and width v mod g.
                assert (g, v % g) in table.get(J, set()) and g < r, (sorted(J), r, v, w, g)
                m = r // g
                a, d = v % g, v // g
                assert 0 < a < g
                R = {b % g for b in B}
                assert all(((cl + k * g) in B) for cl in R for k in range(m))
                ports = {s % g, t % g}
                assert len(ports) == 2
                occ = lambda cl: sum(1 for k in range(m) if (cl + k * g) in C)
                for cl in range(g):
                    if cl not in ports:
                        assert occ(cl) in (0, m), (sorted(J), cl)
                assert occ(s % g) + occ(t % g) == m
                partial_ports += any(0 < occ(cl) < m for cl in ports)
                T = {cl for cl in range(g) if cl not in ports and occ(cl) == m}
                assert len(T) == len(R) - 1
                if d == 0:
                    d0 += 1
                    XK = sorted(R | {g + x for x in R if x <= a}, reverse=True)
                    YK = sorted(T | {g + x for x in T if x <= a} | {t, s}, reverse=True)
                    assert len(XK) == len(YK), (XK, YK)
                    K = normalize(from_flags(XK, YK))
                    assert is_connected_skew(K) and betas(K) == (XK, YK), (XK, YK)
                    ok = False
                    for nu in marks(K):
                        if not (nu.lower == mu.lower and nu.case == 'd' and legal(nu)
                                and (nu.period, nu.width) == (g, a) and phases(nu) == (s, t)):
                            continue
                        for A in outers:
                            if compose(A, nu) == J:
                                assert 2 <= len(K) < len(J) and 2 <= len(A) < len(J)
                                ok = True
                                break
                        if ok:
                            break
                    assert ok, (sorted(J), XK, YK, g, a, s, t)
                    rooted += 1
    assert hyp > 0 and d0 > 0 and partial_ports > 0
    print(f'ph:zero-matrix: {hyp} native signatures, {partial_ports} retaining partial port classes; '
          f'all word conclusions and smaller-period chart searches hold; '
          f'{d0} short-width root flag sets, {rooted} recovered directly from those flags')
    print('ALL PASS')


if __name__ == '__main__':
    main()
