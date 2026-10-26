r"""Self-reflecting inner factors (rt:self-inner).

Paper section `app:endpoints` (Endpoint scalars and ordinary reflection), rt:self-inner.

Reading: the lemma sits inside a comparison that the main theorem excludes, so the finite step
tested is its geometric opening claim, built backwards from the inner.  For every connected J
with at most J_CELLS cells and J = J^* (the half-turn of the normalized diagram), every legal
ordinary or empty mark mu of J of period r and width v, and every connected outer V with at
most V_CELLS cells and span M >= 3, the actual composition E = V o_mu J has the property that
every legal upper mark omega of E with narrow width 0 <= w < r and w != v is ordinary (case (a)
or (b)); the empty mark is included at w = 0.  The control runs the same enumeration over inners
with J != J^*, where narrow mixed uppers do occur, so the symmetry hypothesis is load-bearing.
For the empty finer (v = 0), the beta lists of a self-reflecting J satisfy X_J = {r} u I,
Y_J = C u {0}, I = r - C, and the native matrix K_{ic} = (h_{jr + i - c}) is symmetric after
indexing row i by r - i.

Also the native row equations of the empty finer (g = K^{-1}Z over series in T = z^r) hold exactly,
with a perturbation control.  Uncovered: the counting of rational coordinates at a raw cutoff and the vertical-finer transport.
"""
from _gluing_common import compose, empty_mark, intersection_mark, legal, rotate, span
import random

import sympy as sp

from check_two_copy_flags import betas, diagrams

J_CELLS = 6
V_CELLS = 4


def uppers(E):
    yield empty_mark(E)
    for cell in E:
        try:
            yield intersection_mark(E, cell)
        except AssertionError:
            continue


def inner_marks(J):
    yield empty_mark(J)
    for cell in J:
        try:
            mk = intersection_mark(J, cell)
        except AssertionError:
            continue
        if legal(mk) and mk.case in 'ab':
            yield mk


def scan(reflecting):
    outers = [V for V in diagrams(V_CELLS) if span(V) >= 3]
    tested = mixed = 0
    for J in diagrams(J_CELLS):
        if (rotate(J) == J) != reflecting:
            continue
        for mk in inner_marks(J):
            r = mk.period if mk.lower else span(J)
            v = mk.width
            for V in outers:
                try:
                    E = compose(V, mk)
                except AssertionError:
                    continue
                for om in uppers(E):
                    if not legal(om) or not (0 <= om.width < r) or om.width == v:
                        continue
                    tested += 1
                    if om.case in 'cd':
                        mixed += 1
    return tested, mixed


def native_rows():
    """Native row equations of the empty finer: with K_ic, Z_i the series in T = z^r, g = K^{-1} Z
    solved order by order and P = 1 - sum_c g_c(T) z^c, every coefficient [z^{kr+i}] (H P), i in I,
    vanishes through order L.  Control: perturbing one g coefficient breaks it."""
    rng = random.Random(2)
    n = broken = 0
    L = 3
    for J in diagrams(8):
        if rotate(J) != J:
            continue
        X, Y = betas(J)
        r = X[0]
        if len(X) < 2:
            continue
        I = sorted(x for x in X if x != r)
        C = sorted(y for y in Y if y != 0)
        hv = [sp.Integer(1)] + [sp.Rational(rng.randint(1, 9), rng.randint(1, 4)) for _ in range(r * (L + 1) + 2)]
        h = lambda k: hv[k] if 0 <= k < len(hv) else 0  # noqa: E731
        m = len(I)
        K0 = sp.Matrix(m, m, lambda a, b: h(I[a] - C[b]))
        if K0.det() == 0:
            continue
        Kc = [sp.Matrix(m, m, lambda a, b, j=j: h(j * r + I[a] - C[b])) for j in range(L + 1)]
        Zc = [sp.Matrix(m, 1, lambda a, b, j=j: h(j * r + I[a])) for j in range(L + 1)]
        K0i = K0.inv()
        g = []
        for k in range(L + 1):
            g.append(K0i * (Zc[k] - sum((Kc[j] * g[k - j] for j in range(1, k + 1)), sp.zeros(m, 1))))

        def residual(g):
            Pco = {0: sp.Integer(1)}
            for a, c in enumerate(C):
                for k in range(L + 1):
                    Pco[k * r + c] = Pco.get(k * r + c, 0) - g[k][a]
            return [sum(h(k * r + i - e) * cf for e, cf in Pco.items() if k * r + i - e >= 0)
                    for k in range(L) for i in I]
        assert all(v == 0 for v in residual(g)), sorted(J)
        g2 = [x.copy() for x in g]
        g2[1][0] += 1
        broken += any(v != 0 for v in residual(g2))
        n += 1
    return n, broken


def main():
    tested, mixed = scan(True)
    print(f'self-reflecting inners: narrow uppers {tested}, mixed {mixed}')
    assert tested > 50 and mixed == 0
    tested2, mixed2 = scan(False)
    print(f'other inners: narrow uppers {tested2}, mixed {mixed2}')
    assert mixed2 > 0

    n = 0
    for J in diagrams(8):
        if rotate(J) != J:
            continue
        mk = empty_mark(J)
        X, Y = betas(J)
        r = X[0]
        assert Y[-1] == 0
        I = sorted(x for x in X if x != r)
        C = sorted(y for y in Y if y != 0)
        assert I == sorted(r - c for c in C), sorted(J)
        hs = {k: (k * k + 3 if k >= 0 else 0) for k in range(-2 * r - 2, 4 * r + 4)}
        K = {(c1, c): [hs[j * r + (r - c1) - c] for j in range(3)] for c1 in C for c in C}
        assert all(K[c1, c] == K[c, c1] for c1 in C for c in C)
        assert all(K[c1, c] == [hs[j * r + i - c] for j in range(3)]
                         for c1 in C for c in C for i in [r - c1])
        n += 1
    print(f'self-reflecting empty inners with I = r - C: {n}')
    assert n > 10
    nr, br = native_rows()
    print(f'native row equations of the empty finer on {nr} self-reflecting inners; perturbation breaks {br}')
    assert nr > 20 and br == nr
    print('ALL PASS')


if __name__ == '__main__':
    main()
