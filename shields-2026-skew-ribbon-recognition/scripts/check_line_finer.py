r"""A line finer and the grouped cofactor deck (rt:line-finer).

Paper section `app:boundary` (Boundary constructions and exceptional entrances), rt:line-finer,
rt:line-companion, rt:line-negative-deck, rt:tail-product.

Reading: the lemma concludes a comparison the main theorem excludes, so it is tested through the
finite objects the proof builds on, assembled backwards from the finer.  J = Row_{r+v} with the
horizontal mark Row_v (period r, width v), V ranges over connected outers up to V_CELLS cells
with span M >= 3 and m >= 2 rows, E = V o_mu J.  On each such E:

* X_E = r X_V + v and Y_E = r Y_V, S = N_E = M r + v;
* for every upper Row_w mark omega of E with r not dividing Q = S - w (w = 0 is the empty mark),
  the row companion F_R has 2m - 1 rows and the column companion F_C has 2m rows (m the rows of
  E), and s_E^2 = h_w s_{F_R} + s_{F_C} at random integer letters, exact; every restored index
  Q + (least native label) = a_E + b_E - w is positive and a_E, b_E >= w;
* with generic letters f_1..f_M, f_0 = 1, J_V = JT_f(V), e = det J_V, N_V the first-row /
  last-column deletion, c = (-1)^{m-1} det N_V: c = [f_M] e, gcd(e, c) = 1, the grouped sums C_q,
  D_q satisfy C_q = d e / d f_q for q > 0, C_0 = m e - sum f_j d e / d f_j, and likewise
  D_q = (-1)^{m-1} d det N_V / d f_q, D_0 = (m-1) c - sum f_j d c / d f_j;
* the Dodgson product: c C_{q*} - e D_{q*} = det A_{(1),(1)} det A_{(m),(m)} at the least original
  label q* = x_m - y_1, where A_{(1),(1)} and A_{(m),(m)} delete the first row and column and the
  last row and column (the Jacobi--Trudi matrices of the first-row and last-row deletions).

Uncovered: the negative-deck identity itself, the divisibility steps over the whole source
alphabet, and the gcd > 1 inflation.
"""
import random
from fractions import Fraction

import sympy as sp

from _gluing_common import compose, empty_mark, intersection_mark, legal, span
from check_mixed_empty import det, JT
from check_two_copy_flags import betas, diagrams

V_CELLS = 5
rng = random.Random(5)


def letters():
    vals = {n: Fraction(rng.randint(1, 5)) for n in range(1, 120)}
    vals[0] = Fraction(1)
    return lambda n: vals[n] if n >= 0 else Fraction(0)


def rows_of(shape):
    return len({i for i, _ in shape})


def row_lengths(shape):
    lens = {}
    for i, _ in shape:
        lens[i] = lens.get(i, 0) + 1
    return lens[min(lens)], lens[max(lens)]


def uppers(E):
    yield empty_mark(E)
    for cell in E:
        try:
            om = intersection_mark(E, cell)
        except AssertionError:
            continue
        if legal(om) and om.case == 'a' and rows_of(om.lower) == 1:
            yield om


def cofactor_sums(XV, YV, f, m, deleted=None):
    """Grouped signed cofactor sums C_q of the matrix (f_{x-y})."""
    A = sp.Matrix(len(XV), len(YV), lambda i, j: f(XV[i] - YV[j]))
    sums = {}
    for i, x in enumerate(XV):
        for j, y in enumerate(YV):
            sums[x - y] = sums.get(x - y, 0) + A.cofactor(i, j)
    return A, sums


def main():
    outers = [V for V in diagrams(V_CELLS) if span(V) >= 3 and rows_of(V) >= 2]
    built = companions = algebra = dodgson = 0
    for r in (2, 3):
        for v in range(1, r):
            J = frozenset((0, j) for j in range(r + v))
            mu = intersection_mark(J, (0, r))
            assert mu.period == r and mu.width == v and legal(mu)
            for V in outers:
                E = compose(V, mu)
                M, m = span(V), rows_of(V)
                XV, YV = betas(V)
                XE, YE = betas(E)
                S = XE[0]
                assert XE == sorted((r * x + v for x in XV), reverse=True)
                assert YE == sorted((r * y for y in YV), reverse=True)
                assert S == M * r + v and rows_of(E) == m
                built += 1
                aE, bE = row_lengths(E)
                for om in uppers(E):
                    w, Q = om.width, S - om.width if om.lower else S
                    if Q % r == 0:
                        continue
                    h = letters()
                    FR = betas(compose(frozenset({(0, 0), (0, 1)}), om))
                    FC = betas(compose(frozenset({(0, 0), (1, 0)}), om))
                    assert len(FR[0]) == 2 * m - 1 and len(FC[0]) == 2 * m
                    sE = det(JT(h, XE, YE))
                    assert sE ** 2 == h(w) * det(JT(h, *FR)) + det(JT(h, *FC)), (sorted(E), w)
                    assert aE >= w and bE >= w and aE + bE - w > 0
                    assert Q + (XE[-1] - YE[0]) == aE + bE - w
                    companions += 1
                # grouped decks of the coarse board in generic letters
                fs = sp.symbols('f1:%d' % (M + 1))
                f = lambda n, fs=fs: 0 if n < 0 else 1 if n == 0 else fs[n - 1]  # noqa: E731
                A, C = cofactor_sums(XV, YV, f, m)
                e = sp.expand(A.det())
                eps = (-1) ** (m - 1)
                Nmat = A[1:, :-1]
                c = sp.expand(eps * Nmat.det())
                assert sp.expand(c - sp.diff(e, fs[M - 1])) == 0
                assert sp.gcd(e, c) == 1
                for q in range(1, M + 1):
                    assert sp.expand(C.get(q, 0) - sp.diff(e, fs[q - 1])) == 0
                euler = m * e - sum(fs[j] * sp.diff(e, fs[j]) for j in range(M))
                assert sp.expand(C.get(0, 0) - euler) == 0
                XN, YN = XV[1:], YV[:-1]
                Bn = sp.Matrix(len(XN), len(YN), lambda i, j: f(XN[i] - YN[j]))
                Dsum = {}
                for i, x in enumerate(XN):
                    for j, y in enumerate(YN):
                        Dsum[x - y] = Dsum.get(x - y, 0) + eps * Bn.cofactor(i, j)
                dn = sp.expand(eps * Bn.det())
                assert sp.expand(dn - c) == 0
                for q in range(1, M + 1):
                    assert sp.expand(Dsum.get(q, 0) - sp.diff(c, fs[q - 1])) == 0
                eulerc = (m - 1) * c - sum(fs[j] * sp.diff(c, fs[j]) for j in range(M))
                assert sp.expand(Dsum.get(0, 0) - eulerc) == 0
                algebra += 1
                qs = XV[-1] - YV[0]
                assert qs == min(XV[i] - YV[j] for i in range(m) for j in range(m))
                Tp = A[1:, 1:].det()
                Tm = A[:-1, :-1].det()
                assert sp.expand(c * C[qs] - e * Dsum[qs] - Tp * Tm) == 0, (XV, YV)
                dodgson += 1
    print(f'compositions {built}; companion identities {companions}; deck identities {algebra}; Dodgson products {dodgson}')
    assert built > 10 and companions > 10 and algebra > 10
    print('ALL PASS')


if __name__ == '__main__':
    main()
