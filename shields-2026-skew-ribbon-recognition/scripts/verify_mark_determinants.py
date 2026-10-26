r"""Paper section `app:physical` (Whole currents and the first complete grade), ph:ordinary-activation
and ph:mixed-compound.

For every connected source E up to CELLS cells and every legal positive mark of type (a) or (d),
form its actual two-copy row composition and complete Jacobi--Trudi matrices.

For ph:ordinary-activation, A = s_W and B = A_{s,t}(W), the signed contact-deletion cofactor.
The unsigned contact minor is compared symbolically with the full hatted-mark determinant.
Assert B G_Q = (B d_{h_w}A - A d_{h_w}B) s_{Row_2 o E} + (d_{h_w}B) s_E^2
at exact integer letters, retaining the derivative of B and both contact-cofactor parities.
A symbolic vertical-domino-mark example checks the identity and the current independently
through the first variation of the determinant.

For ph:mixed-compound, h = det JT(X_W without its top row, Y_W without t) is unsigned;
K_t deletes the source top row and column t.  Assert the compound identity with its separate
sign (-1)^{k+b}, including raised negative slots and units.  These bounded cross-checks do not
replace the general proofs.
"""
import random

import sympy as sp

from _gluing_common import compose, shift
from check_two_copy_flags import betas, diagrams, marks, phases

CELLS = 8
rng = random.Random(3)
hs = sp.symbols('h1:40')


def hsym(i):
    return 0 if i < 0 else 1 if i == 0 else hs[i - 1]


def JT(h, X, Y):
    return sp.Matrix(len(X), len(Y), lambda i, j: h(X[i] - Y[j]))


def _ordinary_mark(XW, YW, s, t):
    sign = (-1) ** (XW.index(s) + YW.index(t))
    return sign * JT(hsym, [x for x in XW if x != s], [y for y in YW if y != t]).det()


def _check_symbolic_activation():
    E = frozenset({(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1)})
    W = frozenset({(1, 0), (2, 0)})
    F = E | shift(E, (-1, 3))
    X, Y = betas(E)
    A = JT(hsym, *betas(W)).det()
    B = _ordinary_mark(*betas(W), 1, 1)
    assert B == -hs[1] and A == hs[0] ** 2 - hs[1]
    source = JT(hsym, X, Y)
    e, row = source.det(), JT(hsym, *betas(F)).det()
    raised = JT(lambda n: hsym(4 + n), X, Y)
    G = (source.adjugate() * raised * source.adjugate())[Y.index(0), X.index(6)]
    z = sp.Symbol('z')
    current = sp.expand((source + z * raised).det()).coeff(z, 1)
    independent = sp.diff(e, hs[5]) * current - e * sp.diff(current, hs[5]) + e * sp.diff(e, hs[1])
    assert sp.expand(G - independent) == 0
    wronskian = B * sp.diff(A, hs[1]) - A * sp.diff(B, hs[1])
    assert sp.expand(B * G - wronskian * row - sp.diff(B, hs[1]) * e ** 2) == 0


def main():
    _check_symbolic_activation()
    row2 = frozenset({(0, 0), (0, 1)})
    compound = activation = dependent = 0
    signs = set()
    for E in diagrams(CELLS):
        X, Y = betas(E)
        S = X[0]
        for om in marks(E):
            if not om.lower:
                continue
            w, Q = om.width, om.period
            XW, YW = betas(om.lower)
            vals = {hs[i]: rng.randint(1, 6) for i in range(39)}
            hv = lambda i, vals=vals: 0 if i < 0 else 1 if i == 0 else vals[hs[i - 1]]
            AE = JT(hv, X, Y)
            sE = AE.det()
            sR = JT(hv, *betas(compose(row2, om))).det()
            if om.case == 'd':
                s, t = phases(om)
                B = [x for x in X if w < x < Q]
                C0 = [y for y in YW if y != t]
                assert len(XW) - 1 == len(C0) and t in Y
                hh = JT(hv, XW[1:], C0).det()
                rows, cols = [x for x in X if x != S], [y for y in Y if y != t]
                Kt = JT(hv, rows, cols)

                def T(M, R, C):
                    KQ = sp.Matrix(len(R), len(C), lambda i, j: hv(Q + R[i] - C[j]))
                    return (M.adjugate() * KQ).trace()
                lhs = Kt.det() * T(AE, X, Y) - sE * T(Kt, rows, cols)
                assert lhs == (-1) ** (len(XW) + len(B)) * hh * sR, (sorted(E), sorted(om.lower))
                compound += 1
            elif om.case == 'a':
                s, t = phases(om)
                A = JT(hsym, XW, YW).det()
                B0 = _ordinary_mark(XW, YW, s, t)
                sign = (-1) ** (XW.index(s) + YW.index(t))
                signs.add(sign)
                local = E | shift(E, (-om.displacement[0], -om.displacement[1]))
                W = om.lower
                hat = frozenset({(i, j) for i, j in local if (i + 1, j + 1) in W}
                                | {(i, j) for i, j in W if (i + 1, j + 1) in local})
                hat_det = JT(hsym, *betas(hat)).det() if hat else sp.Integer(1)
                assert sp.expand(B0 - sign * hat_det) == 0
                wronskian = sp.expand(B0 * sp.diff(A, hs[w - 1]) - A * sp.diff(B0, hs[w - 1]))
                assert wronskian != 0 and sp.diff(wronskian, hs[w - 1]) == 0
                KQ = sp.Matrix(len(X), len(Y), lambda i, j: hv(Q + X[i] - Y[j]))
                adj = AE.adjugate()
                G = (adj * KQ * adj)[Y.index(0), X.index(S)]
                Av, Bv = A.subs(vals), B0.subs(vals)
                dA = sp.diff(A, hs[w - 1]).subs(vals)
                dB = sp.diff(B0, hs[w - 1]).subs(vals)
                Wd = Bv * dA - Av * dB
                assert Bv * G == Wd * sR + dB * sE ** 2, (sorted(E), s, t)
                dependent += sp.diff(B0, hs[w - 1]) != 0
                activation += 1
    assert compound > 0 and 0 < dependent < activation and signs == {-1, 1}
    print(f'ph:mixed-compound: {compound} marks; ph:ordinary-activation: {activation} marks, '
          f'{dependent} with a top-letter-dependent contact minor; all identities hold')
    print('symbolic activation and independent determinant-variation current agree')
    print('ALL PASS')


if __name__ == '__main__':
    main()
