r"""Paper section `sec:algebra` (Coarsening inventories and unsigned composition).

Targets: `eq:introG` and the worked inventory of the introduction, `eq:K`,
`lem:labels`, `rem:modular-order`, `eq:ribbon-expansion`, `eq:composition-cuts`,
`lem:literal-factor`, `prop:unsigned` (`eq:seam`, `eq:substitution`,
`eq:Psi-laws`, `eq:projection`, `eq:split`), `cor:reversal-suffices`,
`rem:nonlinear`.

Pure exact integer arithmetic (sympy for the ribbon determinant).  Every object is
built from its definition: an inventory by enumerating the retained cut subsets,
`K_b` by enumerating label permutations, the ribbon Schur function by the
Jacobi-Trudi determinant of the skew shape the composition encodes, and the
substitution maps by substituting generators.  No identity the paper proves is used
to construct the object it is then asserted about.
"""
import itertools
from collections import Counter

import sympy as sp

from _ribbon_common import (
    K_brute, K_labeled, G_poly, Psi, circ, compositions, concat, cuts, from_cuts,
    inventory, inventory_key, kappa, literal_decomposition, multiplicity,
    near_power, odot, padd, pmul, pscale, psub, psubst, factor_lists, h, one,
    factor_reversal_orbit, reverse,
)


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


# ---------------------------------------------------------------- eq:introG
def check_intro_example():
    inv = inventory((1, 2, 1))
    assert inv == Counter({(4,): 1, (3, 1): 2, (2, 1, 1): 1}), inv   # introduction
    # multiplicity matters: equal outcome sets, unequal inventories
    a, b = (1, 2, 1), (2, 1, 1)
    assert set(inventory(a)) != set(inventory(b)) or inventory(a) != inventory(b)
    found = False
    for n in range(4, 9):
        for x, y in itertools.combinations(compositions(n), 2):
            if set(inventory(x)) == set(inventory(y)) and inventory(x) != inventory(y):
                found = True
                break
        if found:
            break
    assert found, "no pair with equal outcome sets and unequal inventories up to weight 8"
    print("PASS  eq:introG: the introduction's inventory of (1,2,1); sets of outcomes are "
          "strictly weaker than inventories (witness found by search)")


# ---------------------------------------------------------------- lem:labels
def check_labels_lemma():
    pairs = 0
    for n in range(2, 10):
        comps = list(compositions(n))
        invs = {a: inventory(a) for a in comps}
        for a in comps:
            S = cuts(a)
            for lam in partitions(n):
                r = len(lam)
                if r <= 6:
                    kb = K_brute(S, lam)               # eq:K over permutations
                    assert kb == K_labeled(S, lam), (a, lam)
                else:
                    kb = K_labeled(S, lam)
                m = invs[a].get(lam, 0)
                assert m == multiplicity(S, lam), (a, lam)    # eq:subset-dp cross-route
                assert kb == kappa(lam) * m, (a, lam, kb, m)  # eq:label-factor
        # second assertion: 0 < |dK| <= 2  =>  dm in {+-1,+-2}, at most one repeated pair
        for a, b in itertools.combinations(comps, 2):
            for lam in set(invs[a]) | set(invs[b]):
                dm = invs[a].get(lam, 0) - invs[b].get(lam, 0)
                dK = kappa(lam) * dm
                if 0 < abs(dK) <= 2:
                    pairs += 1
                    assert abs(dm) in (1, 2), (a, b, lam)
                    mult = sorted(Counter(lam).values())
                    assert max(mult) <= 2 and mult.count(2) <= 1, (a, b, lam)
    assert pairs > 0
    print(f"PASS  lem:labels: K_b = kappa*m for every composition and partition of weight "
          f"<= 9 (three routes agree); {pairs} small-discrepancy certificates all have "
          f"dm in +-{{1,2}} and at most one repeated pair")


def check_modular_order_remark():
    S = cuts((1, 1, 1))
    assert K_brute(S, (1, 1, 1)) == 6 and multiplicity(S, (1, 1, 1)) == 1   # rem:modular-order
    # the factorial is not invertible mod 3 here, which is the remark's point
    assert 6 % 3 == 0
    print("PASS  rem:modular-order: K_b(1,1,1) = 6 against ordinary coefficient 1")


# ------------------------------------------------------- eq:ribbon-expansion
def ribbon_det(alpha):
    """Ribbon Schur function as a Jacobi-Trudi determinant, as a Counter over h-monomials.

    The shape: rows listed top to bottom with lengths alpha; each lower row ends in the
    column where the row above it begins.  s_{lam/mu} = det(h_{lam_i - mu_j - i + j}).
    """
    k = len(alpha)
    N = sum(alpha) - (k - 1)
    R, Lm = [], []
    right = N
    for x in alpha:
        left = right - x + 1
        R.append(right)
        Lm.append(left - 1)
        right = left
    syms = {}

    def hh(m):
        if m < 0:
            return 0
        if m == 0:
            return 1
        return syms.setdefault(m, sp.Symbol(f"h{m}"))

    M = sp.Matrix(k, k, lambda i, j: hh(R[i] - Lm[j] - (i + 1) + (j + 1)))
    expr = sp.expand(M.det(method="berkowitz"))
    poly = sp.Poly(expr, *sorted(syms.values(), key=lambda s: int(str(s)[1:]))) if syms else None
    out = Counter()
    if poly is None:
        out[()] = int(expr)
        return out
    gens = poly.gens
    for mon, c in poly.terms():
        part = []
        for g, e in zip(gens, mon):
            part += [int(str(g)[1:])] * e
        out[tuple(sorted(part, reverse=True))] += int(c)
    return Counter({m: c for m, c in out.items() if c})


def check_ribbon_expansion():
    count = 0
    for n in range(1, 8):
        for a in compositions(n):
            rd = ribbon_det(a)
            # r_beta = (-1)^l A(G_beta), A(h_j) = -h_j: a monomial of degree d gets (-1)^(l+d)
            l = len(a)
            expect = Counter({lam: (-1) ** (l + len(lam)) * c for lam, c in inventory(a).items()})
            assert rd == expect, (a, rd, expect)
            count += 1
    # equal ribbon functions iff equal inventories (the ribbon-equality criterion of the cited work)
    for n in range(2, 8):
        comps = list(compositions(n))
        rib = {a: tuple(sorted(ribbon_det(a).items())) for a in comps}
        for a, b in itertools.combinations(comps, 2):
            assert (rib[a] == rib[b]) == (inventory_key(a) == inventory_key(b)), (a, b)
    print(f"PASS  eq:ribbon-expansion: Jacobi-Trudi ribbon determinant equals (-1)^l A(G) for "
          f"all {count} compositions of weight <= 7; ribbon equality iff inventory equality")


# ------------------------------------------------------ eq:composition-cuts
def check_composition_cuts():
    cnt = 0
    for na in range(1, 6):
        for nb in range(1, 6):
            for al in compositions(na):
                for ep in compositions(nb):
                    p = nb
                    lhs = cuts(circ(al, ep))
                    rhs = {p * x for x in cuts(al)}
                    for j in range(na):
                        rhs |= {j * p + x for x in cuts(ep)}
                    assert lhs == rhs, (al, ep)                           # eq:composition-cuts
                    cnt += 1
    for be in [c for n in range(1, 6) for c in compositions(n)]:
        n = sum(be)
        for m in range(1, 5):
            lhs = cuts(near_power(be, m))
            rhs = set()
            for j in range(m):
                rhs |= {j * n + x for x in cuts(be)}
            assert lhs == rhs and not any(j * n in lhs for j in range(1, m)), (be, m)
    # associativity and (alpha o eps)^* = alpha^* o eps^*
    comps = [c for n in range(1, 4) for c in compositions(n)]
    for a, b, c in itertools.product(comps, repeat=3):
        assert circ(circ(a, b), c) == circ(a, circ(b, c)), (a, b, c)
        assert reverse(circ(a, b)) == circ(reverse(a), reverse(b))
    print(f"PASS  eq:composition-cuts on {cnt} pairs (weights <= 5 x <= 5); no cut at a seam "
          f"of a near-power; composition is associative and reversal distributes over it")


# ------------------------------------------------------- lem:literal-factor
def check_literal_factor():
    tot = 0
    for n in range(1, 11):
        for be in compositions(n):
            for p in [d for d in range(1, n + 1) if n % d == 0]:
                # brute force: all (delta, eps) with |delta| = n/p, |eps| = p
                sols = [(d, e) for d in compositions(n // p) for e in compositions(p)
                        if circ(d, e) == be]
                crit = literal_decomposition(be, p)
                assert (crit is not None) == bool(sols), (be, p)
                if sols:
                    assert len(sols) == 1 and sols[0] == crit, (be, p, sols)  # uniqueness
                    S = cuts(be)
                    assert set(cuts(sols[0][1])) == {x for x in S if x < p}
                    assert set(cuts(sols[0][0])) == {j for j in range(1, n // p) if j * p in S}
                tot += 1
    print(f"PASS  lem:literal-factor: periodicity criterion = existence of a literal factor, "
          f"factor unique, inner and outer cuts as stated ({tot} (composition, p) cases, weight <= 10)")


# ------------------------------------------------------------ prop:unsigned
def pi_hom(p):
    return lambda j: h(j // p) if j % p == 0 else Counter()


def check_unsigned():
    comps = {n: list(compositions(n)) for n in range(1, 8)}
    c1 = 0
    for na in range(1, 6):
        for nb in range(1, 6):
            for a in comps[na]:
                for b in comps[nb]:
                    lhs = G_poly(concat(a, b))
                    rhs = padd(pmul(G_poly(a), G_poly(b)), G_poly(odot(a, b)))
                    assert lhs == rhs, (a, b)                              # eq:seam
                    c1 += 1
    # eq:substitution: the inner weight and the weight of alpha are bounded together so that
    # every near-power image stays within 14 parts (a coarsening count of 2^13)
    c2 = 0
    for ne in range(1, 5):
        for e in comps[ne]:
            psi = Psi(e)
            for na in range(1, 7):
                for a in comps[na]:
                    if max(a) * (len(e) - 1) + len(a) + len(e) > 14 and len(e) > 1 and max(a) > 4:
                        continue
                    if max(a) * (len(e) - 1) + 1 > 13:
                        continue
                    assert psi(G_poly(a)) == G_poly(circ(a, e)), (a, e)    # eq:substitution
                    c2 += 1
    # eq:Psi-laws on generators: parts of the (alpha o epsilon)-power stay under 14
    c3 = 0
    for na in range(1, 4):
        for ne in range(1, 4):
            for a in comps[na]:
                for e in comps[ne]:
                    ae = circ(a, e)
                    top = 1
                    while (top + 1) * (len(ae) - 1) + 1 <= 13 and top < 5:
                        top += 1
                    psi_ae, psi_e, psi_a = Psi(ae), Psi(e), Psi(a)
                    for j in range(1, top + 1):
                        if max(a) * 0 + j * (len(a) - 1) + 1 > 10:
                            continue
                        assert psi_ae(h(j)) == psi_e(psi_a(h(j))), (a, e, j)   # Psi_{a o e} = Psi_e Psi_a
                    for j in range(1, 6):
                        assert Psi(reverse(e))(h(j)) == psi_e(h(j)), (e, j)    # Psi_{e*} = Psi_e
                    c3 += 1
    c4 = 0
    for ne in range(1, 5):
        for e in comps[ne]:
            p = ne
            psi = Psi(e)
            for j in range(1, 6):
                img = psi(h(j))
                back = psubst(img, pi_hom(p))
                assert back == h(j), (e, j, back)                           # eq:split
                c4 += 1
    print(f"PASS  prop:unsigned: seam {c1} pairs, substitution {c2} pairs, composition and "
          f"reversal laws {c3} pairs, split {c4} cases (all integer polynomial identities)")


def check_reversal_suffices():
    cnt = 0
    for n in range(1, 13):
        for be in compositions(n):
            key = inventory_key(be)
            for g in factor_reversal_orbit(be):
                assert inventory_key(g) == key, (be, g)
                cnt += 1
    print(f"PASS  cor:reversal-suffices: every factor-reversal image keeps G ({cnt} images, "
          f"weight <= 12), each factorization enumerated from lem:literal-factor")


# ------------------------------------------------------------ rem:nonlinear
def check_nonlinear():
    C = [(1, 1, 4), (1, 2, 3), (1, 4, 1), (2, 1, 3)]
    sg = [1, 1, -1, -1]
    comb = Counter()
    for c, s in zip(C, sg):
        comb = padd(comb, pscale(G_poly(c), s))
    assert not comb, comb                                             # the linear relation
    sq = Counter()
    for c, s in zip(C, sg):
        sq = padd(sq, pscale(G_poly(near_power(c, 2)), s))
    assert sq.get((4, 3, 3, 2), 0) == 1, sq.get((4, 3, 3, 2))
    # no Q-linear map on the span of weight-six inventories sends G_a to G_{a^{odot2}}:
    # the relation holds among the G_a but not among the images
    assert sq, "image combination vanished"
    print("PASS  rem:nonlinear: the weight-six relation holds; its near-square image has "
          "coefficient 1 at h4*h3^2*h2, so no linear extension exists")


def main():
    check_intro_example()
    check_labels_lemma()
    check_modular_order_remark()
    check_ribbon_expansion()
    check_composition_cuts()
    check_literal_factor()
    check_unsigned()
    check_reversal_suffices()
    check_nonlinear()
    print("ALL PASS: verify_algebra")


if __name__ == "__main__":
    main()
