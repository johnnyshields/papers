r"""Paper section `app:endpoints` (Endpoint scalars and ordinary reflection), ph:structured-dual.

For a source E with full Jacobi--Trudi matrix A = (h_{x-y}), x in X_E, y in Y_E, put e = det A,
K_Q = (h_{Q+x-y}) and G_Q(E) = (adj(A) K_Q adj(A))_{0,S}, the entry in row y = 0 and column x = S,
S the span.  With i the algebra involution h_n -> e_n (e_n the elementary symmetric functions
written in the h's by sum_k (-1)^k e_k h_{n-k} = 0), AT the antitransposition of E, the lemma
asserts, for an ordinary-marked source of upper period Q and width w = S - Q:

    w > 0:   G_Q(AT E) = (-1)^{w+1} i(G_Q(E));        w = 0 (Q = S):   G_S(AT E) = i(e^2 - G_S(E)).

Checked at random positive integer values of h_1, h_2, ... in exact `fractions`/sympy rationals
(i(f)(h) = f(e_1(h), e_2(h), ...) with e_n(h) computed by the recursion), on every connected E of at
most CELLS cells and every legal case (a) or (b) mark, the empty mark included.  """
import random

import sympy as sp

from _gluing_common import antitranspose
from check_two_copy_flags import betas, diagrams, marks

CELLS = 8
SAMPLES = 2


def elementary(hv, n):
    e = [sp.Integer(1)]
    for k in range(1, n + 1):
        e.append(sum((-1) ** (j - 1) * e[k - j] * hv[j] for j in range(1, k + 1)))
    return e


def G(E, Q, hv):
    X, Y = betas(E)
    S = X[0]
    A = sp.Matrix(len(X), len(Y), lambda i, j: hv(X[i] - Y[j]))
    K = sp.Matrix(len(X), len(Y), lambda i, j: hv(Q + X[i] - Y[j]))
    adj = A.adjugate()                      # rows indexed by Y, columns by X
    M = adj * K * adj
    return M[Y.index(0), X.index(S)], A.det()


def main():
    rng = random.Random(7)
    checked = positive = empty = 0
    for E in diagrams(CELLS):
        X, Y = betas(E)
        S = X[0]
        AE = antitranspose(E)
        for om in marks(E):
            if om.case not in 'ab':
                continue
            w = om.width
            Q = S - w
            for _ in range(SAMPLES):
                size = 2 * S + Q + 3
                hs = [None] + [sp.Integer(rng.randint(1, 5)) for _ in range(size)]
                hv = lambda i, hs=hs: 0 if i < 0 else 1 if i == 0 else hs[i]
                ev = elementary(hs, size)
                ehv = lambda i, ev=ev: 0 if i < 0 else ev[i]
                g_at, _ = G(AE, Q, hv)
                g_e_inv, _ = G(E, Q, ehv)               # i(G_Q(E)) evaluated at h
                if w > 0:
                    assert g_at == (-1) ** (w + 1) * g_e_inv, (sorted(E), om.case, w)
                    positive += 1
                else:
                    _, e_det_inv = G(E, Q, ehv)
                    assert g_at == e_det_inv ** 2 - g_e_inv, (sorted(E),)
                    empty += 1
                checked += 1
    assert positive > 0 and empty > 0
    print(f'ph:structured-dual: {positive} positive-width and {empty} empty-upper instances hold; '
          f'{checked} in all')
    print('ALL PASS')


if __name__ == '__main__':
    main()
