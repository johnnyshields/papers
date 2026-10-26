r"""Paper section `sec:weighted-action` (Weighted composition covariance).

A wider sweep than `verify_weighted_action.py`, over the statements that are
quantified over every \(f\in\Lam\), every \(k\), and every legal chart.  Targets:
`eq:weighted-beta-moves` for arbitrary ordered beta lists, `eq:full-normalization`
(the whole signed normalizer) for every connected outer, `rt:mixed-covariance`
with `rt:mixed-intertwining`, and `lem:covariance` with `eq:ordinary-covariance`
and `eq:mixed-covariance`, on every h-monomial of weight up to `--weight` and
every \(k\) up to that weight plus one.

The algebra map \(\Psi_\eta\) is built from its definition `eq:algebra-map` on
the generators, as the image of each \(h_j\) under the actual row composition
\(\operatorname{Row}_j\circ_\eta E\), and extended multiplicatively; the
composites \(s_{D\circ_\eta E}\) are Jacobi--Trudi determinants of the literal
cell sets, so the identity with \(\mathcal N_\eta(D)\) compares two objects built
independently.  SymPy arithmetic is exact.
"""

import argparse
from itertools import product

import sympy as sp

from schur_tools import (compose, delta, dimensions, determinant, h, hats, legal_marks,
                         partitions, schur, shapes)
from _weighted_readout import (beta_det, beta_weighted, coarse, composition_map, mixed_sign,
                               weighted)


def check_beta_moves():
    """eq:weighted-beta-moves for ordered lists with zero and negative entries."""
    count = 0
    values = list(range(-2, 7))
    for lengths in (1, 2, 3):
        lists = list(product(values, repeat=lengths))
        for X, Y in product(lists[::2], lists[::3]):
            raw = beta_det(X, Y)
            for r in range(1, 6):
                moves, rows, cols = beta_weighted(X, Y, r)
                # the left side is V_r applied to the determinant, computed on h-polynomials
                assert moves == weighted(raw, r), (X, Y, r)
                count += 1
    print(f'PASS: V_r det(h_(x-y)) equals the signed beta-move sum for {count} (X, Y, r) with entries '
          f'from -2 to 6, positions kept, including zero and negative entry indices')


def read_outer_map(D, E, W, v, case):
    return composition_map(schur(D), E, W, v, case, read_outer=False)


def check_full_normalization(max_inner, max_outer):
    count = ribbons = 0
    for n in range(2, max_inner + 1):
        for E in shapes(n):
            for W, v, case in legal_marks(E):
                O, What, Ohat = hats(E, W, v)
                A, B, C = (schur(X) for X in (W, What, Ohat))
                for a in range(1, max_outer + 1):
                    for D in shapes(a):
                        r, c, N = dimensions(D)
                        sign = mixed_sign(D) if case in 'cd' else 1
                        normalizer = sign * A ** (a - r) * B ** (a - c) * C ** (a - N)
                        parent = schur(compose(D, E, W, v, case))
                        # the map reads the outer as the paper does, with the involution for case (b)
                        got = composition_map(schur(D), E, W, v, case, read_outer=False)
                        assert got == sp.expand(normalizer * parent), (sorted(E), case, sorted(D))
                        count += 1
                        if case in 'cd' and N == a:                     # a ribbon outer
                            assert sign == (-1) ** (r - 1)
                            ribbons += 1
    print(f'PASS: Psi_eta(s_D) = N_eta(D) s_(D o E), with the full signed normalizer, on {count} charts '
          f'(inners of 2 to {max_inner} cells, every legal mark, all outers of up to {max_outer} cells); '
          f'the mixed sign is (-1)^(r - 1) on {ribbons} ribbon outers')


def monomials(weight):
    for lam in partitions(weight):
        yield sp.prod(h(j) for j in lam)


def check_covariance(max_inner, weight):
    ordinary = mixed = 0
    for n in range(2, max_inner + 1):
        for E in shapes(n):
            for W, v, case in legal_marks(E):
                p = v[1] - v[0]
                O, What, Ohat = hats(E, W, v)
                A, B, C = (schur(X) for X in (W, What, Ohat))
                sE = schur(E)
                if case in 'ab':
                    xi = delta(sE, p)
                    theta = sp.cancel(weighted(sE, p) / xi)
                    local = xi
                else:
                    theta = None
                    local = (-1) ** (-v[0]) * A * B * C
                    rho = sp.cancel(weighted(sE, p) / local)
                    assert rho.is_Integer and rho > 0
                    theta = rho
                for m in range(0, weight + 1):
                    for f in (monomials(m) if m else [sp.Integer(1)]):
                        Phi_f = composition_map(f, E, W, v, case)
                        for k in range(1, m + 2):
                            lhs_w = weighted(Phi_f, k * p)
                            rhs_w = local ** k * composition_map(coarse(f, k, p, theta), E, W, v, case)
                            assert lhs_w == sp.expand(rhs_w), ('V', sorted(E), case, f, k)
                            lhs_d = delta(Phi_f, k * p)
                            rhs_d = (local ** k * composition_map(delta(f, k), E, W, v, case)
                                     if case in 'ab' else 0)
                            assert lhs_d == sp.expand(rhs_d), ('delta', sorted(E), case, f, k)
                if case in 'ab':
                    ordinary += 1
                else:
                    mixed += 1
    print(f'PASS: delta_(kp) Phi = xi^k Phi delta_k and V_(kp) Phi = xi^k Phi (pV_k + theta delta_k) on every '
          f'h-monomial of weight up to {weight}, k up to weight + 1, for {ordinary} ordinary marks; the mixed '
          f'identities (Hall output zero, chi^k and rho) for {mixed} mixed marks')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-inner', type=int, default=5)
    parser.add_argument('--max-outer', type=int, default=4)
    parser.add_argument('--weight', type=int, default=4)
    args = parser.parse_args()
    check_beta_moves()
    check_full_normalization(args.max_inner, args.max_outer)
    check_covariance(args.max_inner, args.weight)
    print('ALL PASS')


if __name__ == '__main__':
    main()
