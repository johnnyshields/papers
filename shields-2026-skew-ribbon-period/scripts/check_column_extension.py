r"""Paper section `app:alternative` (An alternative geometric realization of the scalar).

Column-extension Hall lemma (`app:alternative`, `lem:column-extension`, `eq:extension-domain`,
`eq:extension-inclusion`, `eq:extension-null-row-sum`).

Same set-up as `check_contact_currents.py`: a zero-free connected skew diagram `V` (full beta
lists `X, Y`), connected diagrams `E, F` obtained by restoring common-beta sets `Z_E, Z_F`, a
shared column `t`, and `t < v <= m` with `v` either a common core row absent from both full
column sets, or absent from all full row and column sets.  `R_ext` is a null vector on the
columns `Y_E + {v}` of every row of `E`, normalized at global column `0`; `L_F^t` is the
column-`t` contact vector of `F`, normalized at global row `m`; both are SOLVED here from their
defining equations at a fixed rational alphabet with a random rational `h_0 = nu`.  Asserted on
every instance with `Z_F \ Z_E` inside `(t, v)`: the contraction is the displayed sum over
`Z_F \ Z_E` with no self term, and it vanishes exactly when `Z_F` is a subset of `Z_E`.
Instances whose `R_ext` cannot be normalized at column `0` are counted and skipped.
Sampled: diagrams up to 7 cells and up to three restored units per diagram.
"""
import random
import sys
from itertools import combinations

import sympy as sp

from check_regroup_mixed import skew_shapes
from check_contact_currents import beta_lists

RNG = random.Random(7)
HV = {j: sp.Rational(RNG.randint(1, 10 ** 6), RNG.randint(1, 10 ** 3)) * RNG.choice((1, -1)) for j in range(1, 40)}
NU = sp.Rational(RNG.randint(10 ** 5, 10 ** 6), RNG.randint(1, 10 ** 3))


def h(j):
    return sp.Integer(0) if j < 0 else (NU if j == 0 else HV[j])


def mat(rows, cols):
    return sp.Matrix([[h(x - y) for y in cols] for x in rows])


def main():
    max_cells = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    n = skipped = nonempty = 0
    for D in skew_shapes(max_cells, 3, 4):
        if len(D) < 2:
            continue
        X, Y = beta_lists(D)
        if set(X) & set(Y):
            continue
        m = X[0]
        spots = [z for z in range(1, m) if z not in X and z not in Y]
        subsets = [frozenset(c) for k in range(0, min(3, len(spots)) + 1) for c in combinations(spots, k)]
        for ZE in subsets:
            for ZF in subsets:
                XE, YE = sorted(set(X) | ZE, reverse=True), sorted(set(Y) | ZE, reverse=True)
                XF, YF = sorted(set(X) | ZF, reverse=True), sorted(set(Y) | ZF, reverse=True)
                for t in sorted(set(YE) & set(YF)):
                    for v in range(t + 1, m + 1):
                        core_row = v in X and v not in set(Y) | ZE | ZF
                        absent = v not in set(X) | set(Y) | ZE | ZF
                        if not (core_row or absent):
                            continue
                        if not all(t < z < v for z in ZF - ZE):
                            continue
                        cols = sorted(set(YE) | {v}, reverse=True)
                        null = mat(XE, cols).nullspace()
                        assert len(null) == 1
                        R = null[0]
                        i0 = cols.index(0)
                        if R[i0] == 0:
                            skipped += 1
                            continue
                        R = R / R[i0]
                        # left contact vector of F at column t, normalized at row m
                        rows_other = [x for x in XF if x != m]
                        cols_other = [y for y in YF if y != t]
                        A = sp.Matrix([[h(x - y) for x in rows_other] for y in cols_other])
                        rhs = -sp.Matrix([h(m - y) for y in cols_other])
                        sol = A.LUsolve(rhs)
                        L = {m: sp.Integer(1), **{x: sol[i] for i, x in enumerate(rows_other)}}
                        # contraction L M R_ext over the union of row labels
                        MR = {x: sum((h(x - y) * R[j] for j, y in enumerate(cols)), sp.Integer(0))
                              for x in set(XE) | set(XF)}
                        O = sum((L.get(x, 0) * MR[x] for x in set(XF) | set(XE)), sp.Integer(0))
                        # rows of E are annihilated; the sum collapses to Z_F \ Z_E, no self term
                        for x in XE:
                            assert MR[x] == 0
                        assert O == sum((L[z] * MR[z] for z in ZF - ZE), sp.Integer(0))
                        assert (O == 0) == (ZF <= ZE), (sorted(D), sorted(ZE), sorted(ZF), t, v)
                        n += 1
                        nonempty += bool(ZF - ZE)
    print(f"instances {n} ({nonempty} with a nonempty difference), skipped for normalization {skipped}")
    assert n > 0 and nonempty > 0
    print("PASS")


if __name__ == "__main__":
    main()
