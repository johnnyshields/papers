r"""Paper section `app:contacts` (Same-core contact currents).

Sign claims of `lem:contact-leading` (all products `A_z G_z` have one nonzero sign at a single
sufficiently separated negative-lex specialization) and of `lem:directional-contact`
(`sgn(A_z G_z) = eta_0 (-1)^{[z<t] + [z>r]}`), tested on actual zero-free cores.

`A_z`, `G_z` are computed from the anchor-only matrix exactly as in
`check_contact_currents.anchor_forcing` (the top `nu`-coefficient of the forcing), with the
alphabet replaced by the explicit specialization `h_j = -T^(B^j)`, `T = 2`, `B` larger than twice
the largest matrix size plus two (exact integers, no limit taken).  For each core, each contact
pair `0 <= t < r <= m`, and each vacancy `z` of the core inside `(t, r)` the product sign is
independent of `z`; for the directional domain, with `z` over all vacancies in `(0, m)`, the
product `sgn(A_z G_z) (-1)^{[z<t] + [z>r]}` is independent of `z`.  A specialization that makes some
`A_z` or `G_z` vanish is a failure.  Sampled: zero-free cores up to 8 cells in at most 4 rows and 4
columns (span at most 5, so `B = 2 * 4 + 3`).
"""
import sys

import sympy as sp

import check_contact_currents as cc
from check_contact_currents import anchor_forcing, zero_free_diagrams

MAXSPAN = 5
MATRIX = MAXSPAN                    # largest anchor matrix has fewer rows than the span
B = 2 * MATRIX + 3
T = 2


def sgn(x):
    assert x != 0
    return 1 if x > 0 else -1


def mixed_under_generic_alphabet():
    """Load-bearing control: at the generic seeded alphabet of `check_contact_currents` some product
    pattern is NOT uniform in sign."""
    saved = dict(cc.HVAL)
    found = False
    for D, X, Y in zero_free_diagrams(8, 4, 4):
        m = X[0]
        vac = [z for z in range(1, m) if z not in X and z not in Y]
        for r in range(1, m + 1):
            for t in range(0, r):
                if (r not in X and r in Y) or (t not in Y and t in X):
                    continue
                zs = [z for z in vac if t < z < r]
                if len(zs) >= 2:
                    prods = {sgn(anchor_forcing(X, Y, r, t, z)[0] * anchor_forcing(X, Y, r, t, z)[1]) for z in zs}
                    found = found or len(prods) > 1
    return found


def main():
    assert mixed_under_generic_alphabet(), "control: generic alphabet should show mixed signs"
    for j in range(1, 40):
        cc.HVAL[j] = sp.Integer(-(T ** (B ** j))) if j <= MAXSPAN else sp.Integer(-1)
    n_int = n_dir = 0
    for D, X, Y in zero_free_diagrams(8, 4, 4):
        m = X[0]
        if m > MAXSPAN:
            continue
        vac = [z for z in range(1, m) if z not in X and z not in Y]
        for r in range(1, m + 1):
            for t in range(0, r):
                # a contact is a core label or a shared unit absent from both core lists
                if (r not in X and r in Y) or (t not in Y and t in X):
                    continue
                zs = [z for z in vac if t < z < r]
                prods = []
                for z in zs:
                    A, G, er, et = anchor_forcing(X, Y, r, t, z)
                    prods.append(sgn(A * G))
                if len(prods) >= 2:
                    assert len(set(prods)) == 1, (sorted(D), r, t, prods)
                    n_int += 1
                zs = [z for z in vac if z != r and z != t]
                prods = []
                for z in zs:
                    A, G, er, et = anchor_forcing(X, Y, r, t, z)
                    prods.append(sgn(A * G) * (-1) ** ((z < t) + (z > r)))
                if len(prods) >= 2:
                    assert len(set(prods)) == 1, (sorted(D), r, t, prods)
                    n_dir += 1
    print(f"interior-domain contact pairs with two or more vacancies {n_int}; directional {n_dir}")
    assert n_int > 0 and n_dir > 0
    print("PASS")


if __name__ == "__main__":
    main()
