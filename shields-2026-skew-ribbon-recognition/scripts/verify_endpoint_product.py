r"""Paper section `app:endpoints` (Endpoint scalars and ordinary reflection), rt:endpoint-product.

For a connected D with m rows, span N, decreasing flags X, Y and signed cofactors C_{ij} of its
complete Jacobi--Trudi matrix (h_{x_i - y_j}), put

    P_L = sum_i C_{i,m} z^{N - x_i},   P_R = sum_j C_{1,j} z^{y_j},   a = C_{1,m},
    L_D = P_L / a,   R_D = P_R / a.

The lemma asserts: for m >= 2, P_L and P_R are irreducible over the rational moment field
Q(h_1, h_2, ...); the pair (N, L_D R_D) determines the unordered pair {D, D^*} (D^* the half-turn);
a one-row diagram is determined by its span alone.

Exact sympy over independent symbols h_1, ..., h_N (h_0 = 1, h_i = 0 for i < 0).  Irreducibility
over Q(h)[z] is tested through Gauss's lemma: a factorization over Z[h, z] has exactly one factor
involving z, with multiplicity one, the rest being z-free content.  Exhaustive over every connected
diagram of at most CELLS cells.
"""
import sympy as sp

from _gluing_common import normalize, rotate
from check_two_copy_flags import betas, diagrams

CELLS = 7
z = sp.Symbol('z')


def signed_cofactor(M, i, j):
    return (-1) ** (i + j) * M.minor_submatrix(i, j).det(method='berkowitz') \
        if M.shape[0] > 1 else sp.Integer(1)


def data(D, h):
    X, Y = betas(D)
    m, N = len(X), X[0]
    M = sp.Matrix(m, m, lambda i, j: h(X[i] - Y[j]))
    a = signed_cofactor(M, 0, m - 1)
    PL = sp.expand(sum(signed_cofactor(M, i, m - 1) * z ** (N - X[i]) for i in range(m)))
    PR = sp.expand(sum(signed_cofactor(M, 0, j) * z ** Y[j] for j in range(m)))
    return N, m, a, PL, PR


def irreducible_in_z(P):
    """One z-dependent irreducible factor of multiplicity one over Z[h, z] (Gauss's lemma)."""
    _, factors = sp.factor_list(P)
    with_z = [(f, e) for f, e in factors if f.has(z)]
    return len(with_z) == 1 and with_z[0][1] == 1


def main():
    hs = sp.symbols(f'h1:{CELLS + 2}')

    def h(i):
        return 0 if i < 0 else 1 if i == 0 else hs[i - 1]
    keys = {}
    rows_by_span = {}
    count = 0
    for D in diagrams(CELLS):
        N, m, a, PL, PR = data(D, h)
        assert a != 0
        if m == 1:
            assert N == len(D)
            keys.setdefault((N, 'row'), []).append(D)
            rows_by_span.setdefault(N, []).append(D)
            continue
        assert irreducible_in_z(PL) and irreducible_in_z(PR), sorted(D)
        key = (N, sp.cancel(PL * PR / a ** 2))
        keys.setdefault(key, []).append(D)
        count += 1
    for N, Ds in rows_by_span.items():
        assert len(Ds) == 1, ('one-row diagrams of one span', N)
    for key, Ds in keys.items():
        if key[1] == 'row':
            continue
        D0 = Ds[0]
        assert set(Ds) == {D0, normalize(rotate(D0))}, ('pair not {D, D*}', [sorted(D) for D in Ds])
    print(f'rt:endpoint-product: {count} diagrams with at least two rows up to {CELLS} cells: '
          f'P_L and P_R irreducible, (N, L_D R_D) fibers are exactly {{D, D*}}; '
          f'one-row diagrams determined by span')
    print('ALL PASS')


if __name__ == '__main__':
    main()
