r"""Paper section `app:coincident` (Positive coincident attachment phases).

The degree-two part of a ribbon already separates coprime-periodic cut sets (`app:coincident`,
`lem:mark-pair`; the route of `ribQ_coprime_periodic` in
`lean/SkewRibbonPeriod/Reduction/CoprimeCuts.lean`, which differs from the paper's).

For the ribbon with cut set `C` on `(0, L)`, the two-part terms of the coarsening expansion
`sum over K subset C of (-1)^(|C| - |K|) h_{blocks(K)}` come from the singletons `K = {s}`:

    (-1)^(|C| - 1) sum over s in C of h_{(max(s, L - s), min(s, L - s))}.

So the multiset `{min(s, L - s) : s in C}` is a Schur invariant (the sign is fixed by `|C|`, which
the multiset already records).  Checked first against the full expansion, then swept: an
`A`-periodic `C` (`A | L`) and a `B`-periodic `C'` with `A, B >= 2` coprime, `A + B <= L`, and equal
invariant force `C` empty or all of `(0, L)`.  The sweep is repeated with `A + B > L`, where it
fails, and is checked against the full-ribbon count of `check_periodic_ribbons.py` there.
"""

from collections import Counter
from math import gcd

from check_periodic_ribbons import is_periodic, periodic_sets, ribbon, sweep

L_MAX = 28
A_MAX = 8
B_MAX = 11


def two_part(C, L):
    """Multiset of the two-part coarsenings `min(s, L - s)`."""
    return frozenset(Counter(min(s, L - s) for s in C).items())


def two_part_from_ribbon(C, L):
    """The same multiset read off the full coarsening expansion: its two-part coefficients."""
    out = Counter()
    sign = (-1) ** (len(C) - 1)
    for lam, v in ribbon(frozenset(C), L):
        if len(lam) == 2:
            assert v * sign > 0, (C, L, lam, v)
            out[lam[0]] += v * sign
    return frozenset(out.items())


def two_part_sweep(within):
    tested, bad = 0, []
    for A in range(2, A_MAX + 1):
        for B in range(2, B_MAX + 1):
            if gcd(A, B) != 1:
                continue
            for L in range(2 * A, L_MAX + 1, A):
                if (A + B <= L) != within:
                    continue
                full = frozenset(range(1, L))
                SB = {}
                for C2 in periodic_sets(B, L):
                    SB.setdefault(two_part(C2, L), []).append(C2)
                for C in periodic_sets(A, L):
                    assert is_periodic(C, A, L)
                    tested += 1
                    if C in (frozenset(), full):
                        continue
                    if two_part(C, L) in SB:
                        bad.append((A, B, L, sorted(C), sorted(SB[two_part(C, L)][0])))
    return tested, bad


def main():
    # the invariant is the two-part slice of the full ribbon expansion
    for L in range(2, 11):
        for C in periodic_sets(L, L):
            if C:
                assert two_part(C, L) == two_part_from_ribbon(C, L), (C, L)

    tested, bad = two_part_sweep(within=True)
    print(f"A + B <= L: {tested} A-periodic cut sets tested, {len(bad)} non-line with equal "
          "two-part invariant")
    assert tested > 0
    assert not bad, bad[:5]

    tested, bad = two_part_sweep(within=False)
    print(f"A + B >  L: {tested} tested, {len(bad)} non-line with equal two-part invariant")
    assert bad, "A + B <= L should be needed"

    # in the full-ribbon window the hypothesis is needed with exactly 54 counterexamples
    _, full_bad = sweep(within=False)
    print(f"A + B >  L, full ribbon, A, B <= 7, L <= 16: {len(full_bad)} counterexamples")
    assert len(full_bad) == 54, len(full_bad)
    print("PASS")


if __name__ == "__main__":
    main()
