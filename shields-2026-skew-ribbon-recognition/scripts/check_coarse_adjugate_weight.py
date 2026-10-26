"""Coarse weights of the keyed adjugate (ph:finite-block, ph:one, ph:two).

Paper section `sec:comparison` (Finite comparisons on actual composition charts), ph:finite-block.

The passage from the one- and two-wave currents to ph:one and ph:two separates the prefix sums
C_{a,D} = -sum_{j-k=D, k>=a} DeltaA(j,k) by coarse weight.  This is the hypothesis of
`one_wave_separate` and `two_wave_separate` in the Lean tree: each C_{a,D} is weighted
homogeneous, of a weight that is an injective function of D.

For every connected coarse diagram V with at most CELLS cells, with letters R_l of weight l
(R_0 = rho a weight-zero clock) and the full Jacobi--Trudi matrix (R_{x-y}), check that the keyed
adjugate entry A_V(j,k) at actual row value j and column value k is weighted homogeneous of
weight |V| - (j - k), and that the entries of two coequal diagrams have the same weights, so each
prefix sum C_{a,D} is homogeneous of weight |V| - D.
"""

import os
import sys

import sympy as sp

sys.path.insert(0, os.path.dirname(__file__))

from check_two_copy_flags import betas, diagrams  # noqa: E402

CELLS = 6


def weight_of(poly, letters):
    """The set of weights of the monomials of poly, letter R_l having weight l."""
    if poly == 0:
        return set()
    p = sp.Poly(sp.expand(poly), *letters)
    return {sum(l * e for l, e in zip(range(1, len(letters) + 1), mon)) for mon in p.monoms()}


def main():
    rho = sp.Symbol('rho')
    checked = 0
    for V in diagrams(CELLS):
        X, Y = betas(V)
        n = len(X)
        N = X[0]
        letters = sp.symbols('R1:%d' % (N + 1))

        def R(m):
            if m < 0:
                return 0
            if m == 0:
                return rho
            return letters[m - 1]

        A = sp.Matrix(n, n, lambda i, j: R(X[i] - Y[j]))
        adj = A.adjugate()
        area = len(V)
        for a in range(n):
            for b in range(n):
                entry = adj[b, a]
                wts = weight_of(entry, letters)
                if wts:
                    assert wts == {area - (X[a] - Y[b])}, (sorted(V), X[a], Y[b], wts)
                checked += 1
    print(f'keyed adjugate entries checked: {checked}')
    assert checked > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
