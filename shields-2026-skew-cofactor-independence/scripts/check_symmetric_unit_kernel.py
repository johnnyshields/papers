r"""Non-vacuity check for the symmetric dense unit kernel (prop:symmetric-unit-kernel).

Paper section `sec:restoration` (Common beta entries and first variations).

WHAT THIS SCRIPT DOES.  It is an EXECUTABLE CHECK.  It establishes non-vacuity
and can refute a universal claim; it does not and cannot establish one.  The
proposition is proved in the manuscript by induction on the order; this script
instantiates that statement on every symmetric dense normalized core within an
enumeration bound and verifies the three assertions below by exact rational
linear algebra.

CONVENTIONS, read off the manuscript.
  core            C=(A,B), A=(a_1>...>a_n), B=(b_1>...>b_n)
  Jacobi-Trudi    M_ij = h_{a_i-b_j}; D_ij is the SIGNED cofactor
  dense           a_n > b_1   (every Jacobi-Trudi index is positive)
  normalized      b_n = 0, hence the span is N = a_1
  symmetric       a_i = N - b_{n+1-i}
  positions       Omega_C = {1,...,N-1} \ (A u B)
  unit            U_z^C = sum_{a_i > z > b_j} D_ij h_{a_i-z} h_{z-b_j}
  kernel          K(C) = { lambda : sum_z lambda_z U_z^C = 0 }

ASSERTIONS.
  (1) U_z^C = U_{N-z}^C for every z in Omega_C.
  (2) K(C) = span{ e_z - e_{N-z} : z in Omega_C, 2z < N }.
  (3) dim K(C) = floor(|Omega_C| / 2).

The h_k are treated as commuting indeterminates with h_0 = 1 and h_k = 0 for
k < 0, so every U_z^C is a polynomial and a relation among them is a linear
relation over Q on the monomial coefficients.
"""

from fractions import Fraction
from itertools import combinations
import sympy


# ---------------------------------------------------------------- core model

def symmetric_dense_cores(max_span, max_order):
    """Every normalized symmetric dense core with span <= max_span.

    a_1 = N is forced by normalization plus symmetry (b_n = 0 gives a_1 = N).
    B is then determined by b_j = N - a_{n+1-j}, so a core is exactly a choice
    of the interior parts a_2 > ... > a_n subject to density 2*a_n > N.
    """
    out = []
    for N in range(2, max_span + 1):
        for n in range(1, max_order + 1):
            if n == 1:
                interior_choices = [()]
            else:
                # a_2 > ... > a_n, all strictly between 0 and N
                interior_choices = combinations(range(N - 1, 0, -1), n - 1)
            for interior in interior_choices:
                A = (N,) + tuple(interior)
                if len(set(A)) != n:
                    continue
                if any(A[i] <= A[i + 1] for i in range(n - 1)):
                    continue
                B = tuple(N - A[n - 1 - j] for j in range(n))
                if any(B[i] <= B[i + 1] for i in range(n - 1)):
                    continue
                if B[-1] != 0:
                    continue
                if not A[-1] > B[0]:        # dense
                    continue
                # symmetry, re-checked rather than assumed from construction
                if any(A[i] != N - B[n - 1 - i] for i in range(n)):
                    continue
                out.append((A, B, N))
    return out


def h(k, sym):
    if k < 0:
        return sympy.Integer(0)
    if k == 0:
        return sympy.Integer(1)
    return sym[k]


def signed_cofactors(A, B, sym):
    """D_ij, the signed cofactor of M_ij = h_{a_i - b_j}, as polynomials."""
    n = len(A)
    M = sympy.Matrix(n, n, lambda i, j: h(A[i] - B[j], sym))
    D = {}
    for i in range(n):
        for j in range(n):
            minor = M.copy()
            minor.col_del(j)
            minor.row_del(i)
            sign = (-1) ** (i + j)
            D[(i, j)] = sympy.expand(sign * (minor.det() if n > 1 else sympy.Integer(1)))
    return D


def unit(z, A, B, D, sym):
    n = len(A)
    total = sympy.Integer(0)
    for i in range(n):
        for j in range(n):
            if A[i] > z > B[j]:
                total += D[(i, j)] * h(A[i] - z, sym) * h(z - B[j], sym)
    return sympy.expand(total)


def kernel_basis(units, positions, sym):
    """Exact rational kernel of the span of {U_z}, as vectors indexed by positions."""
    monomials = set()
    polys = []
    for z in positions:
        d = sympy.expand(units[z]).as_coefficients_dict()
        polys.append(d)
        monomials |= set(d.keys())
    monomials = sorted(monomials, key=lambda m: sympy.default_sort_key(m))
    rows = []
    for m in monomials:
        rows.append([sympy.Rational(d.get(m, 0)) for d in polys])
    Mx = sympy.Matrix(rows) if rows else sympy.zeros(1, len(positions))
    return Mx.nullspace()


# ---------------------------------------------------------------- the check

def main():
    MAX_SPAN, MAX_ORDER = 13, 4
    cores = symmetric_dense_cores(MAX_SPAN, MAX_ORDER)

    checked = 0
    rich = 0          # cores with |Omega_C| >= 3, where the claim has content
    order_two_plus = 0
    midpoint_cores = 0

    for A, B, N in cores:
        n = len(A)
        omega = [z for z in range(1, N) if z not in set(A) | set(B)]
        if not omega:
            continue
        sym = {k: sympy.Symbol(f'h{k}') for k in range(1, 4 * N + 2)}
        D = signed_cofactors(A, B, sym)
        units = {z: unit(z, A, B, D, sym) for z in omega}

        # (1) reflection symmetry of the units
        for z in omega:
            assert N - z in omega, (A, B, N, z, 'Omega not reflection-closed')
            assert sympy.expand(units[z] - units[N - z]) == 0, \
                (A, B, N, z, 'U_z != U_{N-z}')

        # (2) and (3): the kernel is exactly the reflection span
        basis = kernel_basis(units, omega, sym)
        dim = len(basis)
        expected_dim = len(omega) // 2
        assert dim == expected_dim, \
            (A, B, N, 'dim', dim, 'expected', expected_dim, 'omega', omega)

        # every predicted generator really is in the kernel
        idx = {z: i for i, z in enumerate(omega)}
        for z in omega:
            if 2 * z < N:
                v = [sympy.Integer(0)] * len(omega)
                v[idx[z]] = sympy.Integer(1)
                v[idx[N - z]] = sympy.Integer(-1)
                combo = sympy.expand(sum(v[i] * units[omega[i]] for i in range(len(omega))))
                assert combo == 0, (A, B, N, z, 'e_z - e_{N-z} not in kernel')

        # every kernel vector satisfies lambda_z + lambda_{N-z} = 0
        for vec in basis:
            for z in omega:
                lz, lnz = vec[idx[z]], vec[idx[N - z]]
                assert sympy.simplify(lz + lnz) == 0, \
                    (A, B, N, z, 'kernel vector violates lambda_z + lambda_{N-z} = 0')

        # the midpoint, where an off-by-one would hide
        if N % 2 == 0 and (N // 2) in omega:
            midpoint_cores += 1
            for vec in basis:
                assert sympy.simplify(vec[idx[N // 2]]) == 0, \
                    (A, B, N, 'midpoint coefficient not forced to zero')

        checked += 1
        if len(omega) >= 3:
            rich += 1
        if n >= 2:
            order_two_plus += 1

    # ---- non-vacuity: a guard that cannot fail is not a guard ----
    assert checked >= 25, f'too few cores enumerated ({checked}); check is near-vacuous'
    assert rich >= 8, f'too few cores with |Omega_C| >= 3 ({rich}); claim has no content'
    assert order_two_plus >= 10, \
        f'too few cores of order >= 2 ({order_two_plus}); proposition is stated for order >= 2'
    assert midpoint_cores >= 1, \
        'no core with an available midpoint was enumerated; the off-by-one case is untested'

    # ---- dilation preserves symmetry and density (the concluding-remarks claim) ----
    dilation_checked = 0
    for A, B, N in cores[:40]:
        n = len(A)
        for t in (2, 3):
            tA, tB, tN = tuple(t * a for a in A), tuple(t * b for b in B), t * N
            assert tA[-1] > tB[0], (A, B, t, 'dilation broke density')
            assert all(tA[i] == tN - tB[n - 1 - i] for i in range(n)), \
                (A, B, t, 'dilation broke symmetry')
            assert tB[-1] == 0, (A, B, t, 'dilation broke normalization')
            dilation_checked += 1
    assert dilation_checked >= 40, 'dilation claim barely exercised'

    print(f'symmetric dense cores checked: {checked} '
          f'(|Omega_C|>=3: {rich}, order>=2: {order_two_plus}, '
          f'with midpoint: {midpoint_cores})')
    print(f'dilation symmetry/density instances: {dilation_checked}')
    print('ALL PASS')


if __name__ == '__main__':
    main()
