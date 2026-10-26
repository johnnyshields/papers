#!/usr/bin/env python3
r"""`prop:path-expansion`, `eq:schur-complement`, `eq:path-entry`, `eq:first-components`,
`lem:endpoint-cancellation`: the common-beta expansion and the vanishing of the first-variation
polynomial at beta endpoints, over a population rather than three cores.

Population: every connected zero-free core (A, B) with N <= 8 and order k <= 4, dense or not, and for
the path expansion every subset Z of the available positions Omega_C.

  (1) Path expansion.  The full Jacobi-Trudi polynomial of the lifted diagram C[Z], computed by a
      subset recurrence on the genuine board (units h_0 = 1 included), equals eps times the determinant
      of the reduced k x k matrix whose (a, b) entry is the signed path sum
      sum_l (-1)^l sum_{a > z_1 > ... > z_l > b} h_{a-z_1} ... h_{z_l-b}; eps is the product of the two
      regrouping signs.  The ordinary-degree-k and -(k+1) components are eps s_C and -eps sum_{z in Z} U_z.
  (2) Endpoint cancellation.  With the return vectors u_i = h_{a_i-z}, v_j = h_{z-b_j}, each taken to be
      zero unless its gap is positive, the contraction u^T D v is the zero polynomial at every z in
      A u B (and at every integer z outside (0, N) as well), for every core in the population.
      Control: with the gap-zero entry h_0 = 1 retained, the contraction at z = a_l is the nonzero
      determinant det M_C on every dense core, so the strict-return convention is what the lemma needs.
"""
from collections import Counter
from itertools import combinations

import check_cofactor_dilation as K
from check_restoration_edges_and_rigidity import connected_core

NMAX = 8
KMAX = 4


def zero_free_cores():
    for N in range(2, NMAX + 1):
        for k in range(1, KMAX + 1):
            for As in combinations(range(1, N), k - 1):
                for Bs in combinations(range(1, N), k - 1):
                    if set(As) & set(Bs):
                        continue
                    A = (N,) + tuple(sorted(As, reverse=True))
                    B = tuple(sorted(Bs, reverse=True)) + (0,)
                    if connected_core(A, B):
                        yield A, B


def contraction(a, b, z, cofs, strict=True):
    out = Counter()
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            lo = (x - z > 0 and z - y > 0) if strict else (x - z >= 0 and z - y >= 0)
            if lo:
                K.add_to(out, K.multiply(cofs[i][j], {tuple(sorted(t for t in (x - z, z - y) if t)): 1}))
    return out


def main():
    n_cores = n_paths = n_end = n_ctrl = 0
    for a, b in zero_free_cores():
        k = len(a)
        cofs = K.cofactors(a, b)
        dense = a[-1] > b[0]
        omega = K.available(a, b)
        # (2) endpoint cancellation, strict returns
        for z in tuple(a) + tuple(b) + (-2, -1, a[0] + 1, a[0] + 2):
            assert not contraction(a, b, z, cofs), ("endpoint unit must vanish", a, b, z)
            n_end += 1
        if dense:
            det = K.determinant(a, b)
            for z in a:
                got = contraction(a, b, z, cofs, strict=False)
                assert got == det and det, ("gap-zero convention gives det M_C", a, b, z)
                n_ctrl += 1
        # (1) path expansion over every Z
        for z in K.all_subsets(omega):
            x, y = K.lift(a, b, z)
            eps = K.deletion_sign(a, b, z)
            full = K.determinant(x, y)
            expected = K.determinant_dp(K.path_matrix(a, b, z))
            assert full == Counter({u: eps * c for u, c in expected.items()}), ("path expansion", a, b, z)
            assert K.component(full, k) == Counter({u: eps * c for u, c in K.determinant(a, b).items()})
            corr = Counter()
            for site in z:
                K.add_to(corr, K.unit(a, b, site, cofs), -eps)
            assert K.component(full, k + 1) == corr, ("first components", a, b, z)
            assert not any(len(u) < k for u in full)                     # lowest ordinary degree is k
            n_paths += 1
        n_cores += 1
    assert n_cores > 100 and n_paths > 1000 and n_end > 1000 and n_ctrl > 10
    print("%d connected zero-free cores (N <= %d, order <= %d); %d (core, Z) path expansions with both "
          "components; %d endpoint contractions vanish; %d gap-zero controls give det M_C"
          % (n_cores, NMAX, KMAX, n_paths, n_end, n_ctrl))
    print("ALL PASS")


if __name__ == "__main__":
    main()
