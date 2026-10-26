r"""Paper section `app:coincident` (Positive coincident attachment phases).

Schur-equal ribbons whose cut sets have coprime periods are lines (`app:coincident`,
`lem:mark-pair`, `lem:one-coincident-entry`: "its two actual periods `a, b` are coprime ... make
both indicator natives lines in the same orientation"; `ribQ_coprime_periodic` in
`lean/SkewRibbonPeriod/Reduction/CoprimeCuts.lean`).

A ribbon of `L` cells is coded by its cut set `C`, a subset of the internal positions `(0, L)`.
Its Schur function is the alternating coarsening sum

    r_C = sum over K subset C of (-1)^(|C| - |K|) h_{blocks(K)},

where `blocks(K)` is the multiset of gaps cut out of `[0, L]` by `K`.  Since the `h_lambda` are a
basis, `r_C = r_C'` exactly when the two coarsening expansions agree coefficient by coefficient,
which is what is compared here.

`C` is `P`-periodic when `i in C <-> i + P in C` for `0 < i`, `i + P < L`.  The claim: if `C` is
`A`-periodic with `A | L`, `C'` is `B`-periodic, `A, B >= 2` coprime, `A + B <= L`, and
`r_C = r_C'`, then `C` is empty or all of `(0, L)`.  Swept over every such configuration with
`A, B <= 7` and `L <= 16`; the sweep is repeated with `A + B > L` to show that hypothesis is needed.
"""

from collections import Counter
from itertools import product
from functools import lru_cache
from math import gcd

L_MAX = 16
P_MAX = 7


def blocks(K, L):
    pts = [0] + sorted(K) + [L]
    return tuple(sorted(pts[i + 1] - pts[i] for i in range(len(pts) - 1)))


@lru_cache(maxsize=None)
def ribbon(C, L):
    """Coarsening expansion of the ribbon with cut set `C`, as a frozen coefficient map."""
    C = sorted(C)
    n = len(C)
    out = Counter()
    for mask in range(1 << n):
        K = [C[i] for i in range(n) if mask >> i & 1]
        out[blocks(K, L)] += (-1) ** (n - len(K))
    return frozenset((k, v) for k, v in out.items() if v)


def periodic_sets(P, L):
    """Every `P`-periodic subset of `(0, L)`: one bit per residue class mod `P`."""
    return {frozenset(i for i in range(1, L) if bits[i % P]) for bits in product((0, 1), repeat=P)}


def is_periodic(C, P, L):
    return all((i in C) == (i + P in C) for i in range(1, L - P))


def sweep(within):
    """Configurations with `A + B <= L` (`within`) or `A + B > L`; returns
    (configurations tested, counterexamples)."""
    tested, bad = 0, []
    for A in range(2, P_MAX + 1):
        for B in range(2, P_MAX + 1):
            if gcd(A, B) != 1:
                continue
            for L in range(2 * A, L_MAX + 1, A):
                if (A + B <= L) != within:
                    continue
                full = frozenset(range(1, L))
                SB = {}
                for C2 in periodic_sets(B, L):
                    assert is_periodic(C2, B, L)
                    SB.setdefault(ribbon(C2, L), []).append(C2)
                for C in periodic_sets(A, L):
                    assert is_periodic(C, A, L)
                    tested += 1
                    if C in (frozenset(), full):
                        continue
                    r = ribbon(C, L)
                    if r in SB:
                        bad.append((A, B, L, sorted(C), sorted(SB[r][0])))
    return tested, bad


def main():
    # the coarsening expansion separates a ribbon from a non-equivalent one and identifies it
    # with its reversal (rotation by 180 degrees)
    assert ribbon(frozenset({1, 2}), 4) == ribbon(frozenset({2, 3}), 4)
    assert ribbon(frozenset({1}), 4) == ribbon(frozenset({3}), 4)
    assert ribbon(frozenset({1}), 4) != ribbon(frozenset({2}), 4)

    tested, bad = sweep(within=True)
    print(f"A + B <= L: {tested} A-periodic cut sets tested, {len(bad)} non-line Schur-equal")
    assert tested > 0
    assert not bad, bad[:5]

    tested, bad = sweep(within=False)
    print(f"A + B >  L: {tested} A-periodic cut sets tested, {len(bad)} non-line Schur-equal")
    for b in bad[:3]:
        print("   ", b)
    assert len(bad) == 54, len(bad)
    print("PASS")


if __name__ == "__main__":
    main()
