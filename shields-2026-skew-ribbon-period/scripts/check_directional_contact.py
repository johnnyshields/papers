r"""Paper section `app:alternative` (An alternative geometric realization of the scalar).

Directional contact rigidity (`app:alternative`, `lem:directional-contact`,
`eq:directional-domain`), on the data of `check_contact_currents.py`.

Same zero-free core `V`, restored common-beta sets `Z_E, Z_F`, contacts `0 <= t < r <= m`, with
the interior domain `eq:contact-interior-domain` replaced by `Z_E \ Z_F` inside `(0, r)` and
`Z_F \ Z_E` inside `(t, m)`.  The contact vectors are solved from their equations
(`check_contact_currents.kernel_data`).  Asserted: the balanced current `B_{r,t}(E, F)` vanishes
exactly when `E = F`; its leading coefficient at `nu^(epsilon_r + epsilon_t - 1)` is
`-sum_{Z_E \ Z_F} (z - t) A_z G_z - sum_{Z_F \ Z_E} (r - z) A_z G_z` with `A_z, G_z` computed from
the anchor-only matrix; and the instances include differing units below `t` and above `r`, the
cases the interior domain excludes.  The sign pattern `sgn(A_z G_z) = eta_0 (-1)^{[z<t] + [z>r]}` is checked in
`check_contact_signs.py`.
# TODO: not yet verified -- the cap-modification table of `eq:modified-cap-table`: that the three
# modified upper and lower list pairs keep the rectangular cardinalities, have differences
# `Delta + 1_sigma` and `Delta - 1_tau`, preserve the height word and give connected skew diagrams
# of the same area.  It needs the actual return frames `(I_R, C_R)`, `(I_L, C_L)` and the Boolean
# pair of a sampled periodic source, which no script here constructs end to end.
"""
import sys
from itertools import combinations

import sympy as sp

from check_regroup_mixed import skew_shapes
from check_contact_currents import NU, K, anchor_forcing, beta_lists, kernel_data, zero_free_diagrams


def main():
    max_cells = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    n = outside = checked = 0
    for D, X, Y in zero_free_diagrams(max_cells, 3, 4):
        m = X[0]
        spots = [z for z in range(1, m) if z not in X and z not in Y]
        if not spots:
            continue
        subsets = [frozenset(c) for k in range(0, min(3, len(spots)) + 1) for c in combinations(spots, k)]
        for ZE in subsets:
            for ZF in subsets:
                shared = ZE & ZF
                for r in sorted(set(X) | shared):
                    for t in sorted(set(Y) | shared):
                        if not (0 <= t < r <= m):
                            continue
                        if not (all(0 < z < r for z in ZE - ZF) and all(t < z < m for z in ZF - ZE)):
                            continue
                        data = kernel_data(X, Y, set(ZE), set(ZF), r, t)
                        if data is None:
                            continue
                        n += 1
                        Bv = data['B']
                        assert (Bv == K.zero) == (ZE == ZF), (sorted(D), sorted(ZE), sorted(ZF), r, t)
                        if ZE == ZF:
                            continue
                        eps_r = 0 if r in X else 1
                        eps_t = 0 if t in Y else 1
                        e = eps_r + eps_t
                        want = sp.Integer(0)
                        for z in ZE ^ ZF:
                            A, G, _, _ = anchor_forcing(X, Y, r, t, z)
                            assert A != 0 and G != 0
                            want -= ((z - t) if z in ZE - ZF else (r - z)) * A * G
                            if z < t or z > r:
                                outside += 1
                        lim = sp.limit(K.to_sympy(Bv) / NU ** (e - 1), NU, sp.oo)
                        assert lim == want, (lim, want)
                        checked += 1
    print(f"instances {n}, leading-coefficient checks {checked}, differing units outside (t, r): {outside}")
    assert n > 0 and checked > 0 and outside > 0
    print("PASS")


if __name__ == "__main__":
    main()
