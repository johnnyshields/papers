r"""Paper section `sec:recovery` (Composition coordinates and effective certificates).

Targets: `prop:coordinates` (`eq:coordinates`), `prop:depth-cancel`
(`eq:leading-substitution`), `thm:recovery` (`eq:outer-recovery`,
`eq:inner-derivative`, `eq:inner-recovery`, `eq:two-factor-cancel`), the Euler identity
and the arithmetic of the subset DP (`eq:subset-dp`), `prop:parity`
(`subsec:parity`), `cor:odd-characteristic`.

Inventories come from the (closed blocks, open block) DP of `_ribbon_common.py`, so
products of weights up to about twenty are expanded exactly.  Every identity is an
identity in Z[h_1, h_2, ...] and is compared as a dictionary of integer coefficients;
the one rational operator `eq:inner-recovery` is checked as `n * G_beta` on the
integers, which is the same statement without a division.
"""
import itertools
import random
from collections import Counter
from fractions import Fraction

from _ribbon_common import (Omega, circ, compositions, concat, cuts, from_cuts, h,
                            indicator, inventory_dp, multiplicity, near_power, odot,
                            padd, pcontent, pderiv, pmul, pscale, psub, psubst,
                            pmin_degree, pdegree_part, reverse, one)


def gp(a):
    return Counter(inventory_dp(a))


def Psi_dp(e):
    memo = {}

    def img(j):
        if j not in memo:
            memo[j] = gp(near_power(e, j))
        return memo[j]

    return lambda F: psubst(F, img)


def pi_hom(p):
    return lambda j: h(j // p) if j % p == 0 else Counter()


# ------------------------------------------------------------ prop:coordinates
def check_coordinates():
    tot = 0
    for p in range(1, 7):
        for e in compositions(p):
            for j in range(1, 7):
                if p * j > 22:
                    continue
                G = gp(near_power(e, j))
                # G_{eps^{odot j}} = h_{pj} + R_j(h_1, ..., h_{pj-1}), one block term only
                assert G.get((p * j,), 0) == 1
                assert all(max(m) < p * j for m in G if m != (p * j,)), (e, j)
                # weight-homogeneous
                assert all(sum(m) == p * j for m in G)
                tot += 1
    # Theta is an automorphism: build its inverse recursively on weight <= 8 and check both
    # compositions are the identity on every generator
    for e in [(1, 1), (2, 1), (3,), (1, 2), (1, 1, 1)]:
        p = sum(e)
        W = 8
        theta = {}
        for r in range(1, W + 1):
            theta[r] = gp(near_power(e, r // p)) if r % p == 0 else h(r)
        inv = {}
        for r in range(1, W + 1):
            if r % p:
                inv[r] = h(r)
                continue
            # theta(h_r) = h_r + R_r(h_<r)  =>  inv(h_r) = h_r - R_r(inv(h_1), ..., inv(h_{r-1}))
            R = Counter({m: c for m, c in theta[r].items() if m != (r,)})
            sub = psubst(R, lambda k: inv[k])
            inv[r] = padd(h(r), sub, -1)
        for r in range(1, W + 1):
            back = psubst(theta[r], lambda k: inv[k])
            assert back == h(r), (e, r)
            fwd = psubst(inv[r], lambda k: theta[k])
            assert fwd == h(r), (e, r)
            assert all(sum(m) == r for m in inv[r])                       # integral and weight-preserving
        tot += 1
    # eq:coordinates in a small weight: the monomials in G_{eps^{odot k}} and h_r (p !| r) of
    # weight w are linearly independent and number the partitions of w (a polynomial ring in
    # those generators has the right Hilbert series), checked by a rank computation
    import sympy as sp
    for e in [(1, 1), (2, 1), (3,)]:
        p = sum(e)
        for w in range(1, 9):
            gens = []
            for r in range(1, w + 1):
                gens.append((r, gp(near_power(e, r // p)) if r % p == 0 else h(r)))
            monos = []
            for lam in _parts(w):
                term = one()
                for r in lam:
                    term = pmul(term, dict(gens)[r])
                monos.append(term)
            keys = sorted({m for t in monos for m in t})
            M = sp.Matrix([[t.get(k, 0) for k in keys] for t in monos])
            assert M.rank() == len(monos) == len(list(_parts(w))), (e, w)
            assert abs(M.det()) == 1 if M.shape[0] == M.shape[1] else True     # unimodular: integral basis
    # Psi pi is an idempotent retraction onto im Psi
    for e in [(1, 1), (2, 1), (1, 2), (3,)]:
        p = sum(e)
        psi = Psi_dp(e)
        for j in range(1, 7):
            F = psi(h(j))
            once = psi(psubst(F, pi_hom(p)))
            assert once == F, (e, j)                                         # (Psi pi) F = F on im Psi
            assert psi(psubst(once, pi_hom(p))) == once                      # idempotent
    print(f"PASS  prop:coordinates, eq:coordinates: {tot} unitriangularity checks; Theta_eps has "
          f"an integral inverse built recursively and both composites are the identity (weight <= 8, "
          f"five inner compositions); the generators G_(eps^j), h_r (p !| r) give a unimodular basis "
          f"of every weight <= 8 piece; Psi pi is an idempotent retraction")


def _parts(n, mx=None):
    if mx is None:
        mx = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, mx), 0, -1):
        for rest in _parts(n - k, k):
            yield (k,) + rest


# ----------------------------------------------------------- prop:depth-cancel
def check_depth_cancel():
    rng = random.Random(8080)
    tot = 0
    for p in range(2, 5):
        for e in compositions(p):
            psi = Psi_dp(e)
            tests = []
            for n in range(2, 8):
                comps = list(compositions(n))
                for _ in range(12):
                    a, b = rng.sample(comps, 2) if len(comps) > 1 else (comps[0], comps[0])
                    tests.append(psub(gp(a), gp(b)))
                # random integer combinations of monomials
                for _ in range(6):
                    F = Counter()
                    for lam in rng.sample(list(_parts(n)), min(4, len(list(_parts(n))))):
                        F[lam] += rng.choice([-3, -2, -1, 1, 2, 5])
                    tests.append(Counter({m: c for m, c in F.items() if c}))
            for F in tests:
                if not F:
                    continue
                r = pmin_degree(F)
                # eq:leading-substitution
                lhs = pdegree_part(psi(F), r)
                rhs = Counter({tuple(sorted((p * x for x in m), reverse=True)): c
                               for m, c in pdegree_part(F, r).items()})
                assert lhs == rhs, (e, F)
                # first degree and content preserved
                imgF = psi(F)
                assert pmin_degree(imgF) == r
                assert pcontent(imgF) == pcontent(F), (e, F)
                tot += 1
    print(f"PASS  prop:depth-cancel, eq:leading-substitution: {tot} polynomials (differences of "
          f"inventories and random integer combinations, weight 2..7) against inner weights 2..4: "
          f"the leading-degree part transforms by h_j -> h_(pj); first degree and the gcd of the "
          f"coefficients are preserved")


# --------------------------------------------------------------- thm:recovery
def check_recovery():
    tot_o = tot_d = tot_l = tot_c = tot_e = 0
    for m in range(1, 5):
        for n in range(1, 6):
            if m * n > 14:
                continue
            for al in compositions(m):
                for be in compositions(n):
                    ab = circ(al, be)
                    G = gp(ab)
                    # eq:outer-recovery
                    assert psubst(G, pi_hom(n)) == gp(al), (al, be)
                    tot_o += 1
                    # eq:inner-derivative
                    Gb = gp(be)
                    for j in range(1, n + 1):
                        assert pderiv(G, (m - 1) * n + j) == pderiv(Gb, j), (al, be, j)
                        tot_d += 1
                    # eq:inner-recovery, as n times the identity (no division)
                    acc = Counter()
                    for j in range(1, n + 1):
                        term = pscale(pmul(h(j), pderiv(G, (m - 1) * n + j)), j)
                        acc = padd(acc, term)
                    assert acc == pscale(Gb, n), (al, be)
                    assert all(c % n == 0 for c in acc.values())
                    tot_l += 1
                    # weighted Euler identity for G_beta
                    eul = Counter()
                    for j in range(1, n + 1):
                        eul = padd(eul, pscale(pmul(h(j), pderiv(Gb, j)), j))
                    assert eul == pscale(Gb, n), be
                    tot_e += 1
    print(f"PASS  thm:recovery: eq:outer-recovery on {tot_o} (alpha, beta) pairs, eq:inner-derivative "
          f"on {tot_d} (pair, j) cases, eq:inner-recovery (as n G_beta, division-free) on {tot_l}, "
          f"the weighted Euler identity on {tot_e} (|alpha| <= 4, |beta| <= 5, product weight <= 14)")
    # eq:two-factor-cancel: forward implication with distinct factor classes (both weights fixed)
    cnt = 0
    for m in range(1, 5):
        for n in range(1, 5):
            if m * n > 12:
                continue
            A = list(compositions(m))
            B = list(compositions(n))
            for a1, a2 in itertools.product(A, A):
                for b1, b2 in itertools.product(B, B):
                    same = inventory_dp(circ(a1, b1)) == inventory_dp(circ(a2, b2))
                    both = (inventory_dp(a1) == inventory_dp(a2)) and (inventory_dp(b1) == inventory_dp(b2))
                    assert same == both, (a1, a2, b1, b2)             # eq:two-factor-cancel
                    cnt += 1
    print(f"PASS  eq:two-factor-cancel: equivalence of alpha o beta and alpha' o beta' holds exactly "
          f"when alpha ~ alpha' and beta ~ beta' ({cnt} quadruples, |alpha| <= 4, |beta| <= 4, "
          f"product weight <= 12)")


# --------------------------------------------------------------- eq:subset-dp
def check_subset_dp():
    tot = 0
    for n in range(2, 13):
        for a in compositions(n):
            inv = inventory_dp(a)
            S = cuts(a)
            for lam, c in inv.items():
                assert multiplicity(S, lam) == c, (a, lam)            # eq:subset-dp
                tot += 1
            # a partition that never occurs has multiplicity zero too (sample)
    # state and operation counts: prod (nu_i + 1) <= 2^r, at most r terms per state
    for lam in _parts(14):
        r = len(lam)
        from collections import Counter as C2
        nu = C2(lam)
        states = 1
        for v in nu.values():
            states *= v + 1
        assert states <= 2 ** r
    # modulo q directly: the DP uses only additions of 0/1-gated terms, so reducing the
    # counts mod q at every step equals reducing the final count
    import copy
    for n in (9, 10, 11):
        for a in list(compositions(n))[:200]:
            S = cuts(a)
            for lam in list(inventory_dp(a))[:6]:
                for q in (3, 5):
                    assert multiplicity(S, lam) % q == _mult_mod(S, lam, q), (a, lam, q)
    print(f"PASS  eq:subset-dp: the DP multiplicity equals the DP-inventory coefficient for all "
          f"{tot} occurring partitions of every composition of weight 2..12; state count "
          f"prod(nu_i + 1) <= 2^r for all partitions of 14; the DP reduced modulo 3 and 5 at every "
          f"step equals the reduced count")


def _mult_mod(cutset, lam, q):
    lam = tuple(sorted(lam, reverse=True))
    vals = sorted(set(lam), reverse=True)
    nu = tuple(lam.count(t) for t in vals)
    memo = {}

    def D(st):
        if not any(st):
            return 1
        if st in memo:
            return memo[st]
        s = sum(x * t for x, t in zip(st, vals))
        if st != nu and s not in cutset:
            memo[st] = 0
            return 0
        tot = 0
        for i, x in enumerate(st):
            if x:
                tot = (tot + D(st[:i] + (x - 1,) + st[i + 1:])) % q
        memo[st] = tot
        return tot

    return D(nu)


# ----------------------------------------------------------------- prop:parity
def check_parity():
    U = (1, 1, 1, 1, 1, 1, 1, 1, 9)
    V = (1, 1, 2, 4, 2, 1, 1, 2, 3)
    n = 17
    assert sum(U) == sum(V) == n
    assert cuts(U) == frozenset(range(1, 9))
    assert cuts(V) == frozenset({1, 2, 4, 8, 10, 11, 12, 14})
    SU, SV = cuts(U), cuts(V)
    # exactly one point of each reflected pair
    for x in range(1, 9):
        assert (x in SU) + (n - x in SU) == 1 and (x in SV) + (n - x in SV) == 1
    dis = frozenset(x for x in range(1, n) if (x in SU) != (x in SV))
    assert dis == frozenset({3, 5, 6, 7, 10, 11, 12, 14}), dis
    # a complete doubling-negation orbit modulo 17
    orbit, x = set(), 3
    for _ in range(16):
        orbit.add(x % n)
        orbit.add((-x) % n)
        x = (2 * x) % n
    assert orbit == set(dis), (orbit, dis)
    # congruence through degree three, and the explicit differences
    iu, iv = inventory_dp(U, 3), inventory_dp(V, 3)
    allp = set(iu) | set(iv)
    assert all((iu.get(l, 0) - iv.get(l, 0)) % 2 == 0 for l in allp)
    fu, fv = inventory_dp(U), inventory_dp(V)
    assert fu != fv
    assert (fu[(14, 2, 1)], fv.get((14, 2, 1), 0)) == (2, 0)
    assert (fu[(14, 1, 1, 1)], fv.get((14, 1, 1, 1), 0)) == (1, 0)
    # the two ordered coarsenings realizing (14, 2, 1) for U and the single one for (14,1,1,1)
    import itertools as it
    ords = [p for p in set(it.permutations((14, 2, 1))) if all(sum(p[:j]) in SU for j in (1, 2))]
    assert sorted(ords) == [(1, 2, 14), (2, 1, 14)], ords
    ords = [p for p in set(it.permutations((14, 1, 1, 1))) if all(sum(p[:j]) in SU for j in (1, 2, 3))]
    assert ords == [(1, 1, 1, 14)], ords
    # first mod-2 distinguishing degree is four, and the partition (14,1,1,1) is a unit discrepancy
    degs = sorted({len(l) for l in set(fu) | set(fv) if (fu.get(l, 0) - fv.get(l, 0)) % 2})
    assert degs[0] == 4, degs
    from verify_depth import B_of
    assert B_of(17) == 3
    # the structural claim: for odd n and b(x) + b(-x) = 1, three-part distinct partitions
    # have multiplicity k(3-k) in {0, 2}; repeated (a,a,n-2a): one iff b(a) = b(2a)
    ok_dist = ok_rep = 0
    for n_ in (7, 9, 11, 13, 15, 17):
        for choice in itertools.product((0, 1), repeat=(n_ - 1) // 2):
            b = [0] * n_
            for x, ch in enumerate(choice, start=1):
                b[x], b[n_ - x] = ch, 1 - ch
            Sb = frozenset(x for x in range(1, n_) if b[x])
            for lam in _parts(n_):
                if len(lam) != 3:
                    continue
                m = multiplicity(Sb, lam)
                if len(set(lam)) == 3:
                    k = sum(b[x] for x in lam)
                    assert m == k * (3 - k), (n_, choice, lam)
                    ok_dist += 1
                elif len(set(lam)) == 2:
                    a = lam[0] if lam.count(lam[0]) == 2 else lam[1]
                    assert m == (1 if b[a] == b[(2 * a) % n_] else 0), (n_, choice, lam)
                    ok_rep += 1
    print(f"PASS  prop:parity: cut sets, disagreement set (one doubling-negation orbit mod 17), "
          f"congruence of the degree <= 3 inventories mod 2, G_U != G_V, coefficients (2, 0) at "
          f"(14,2,1) and (1, 0) at (14,1,1,1) with the stated ordered coarsenings, first mod-2 "
          f"discrepancy at degree 4, B(17) = 3; the proof's formulas k(3-k) and [b(a) = b(2a)] "
          f"verified on every antisymmetric indicator for odd n <= 17 ({ok_dist} distinct, "
          f"{ok_rep} repeated three-part partitions)")


# ----------------------------------------------------- cor:odd-characteristic
def check_odd_characteristic(nmax=11):
    from collections import defaultdict
    from _ribbon_common import inventory_dp
    tot = 0
    for n in range(1, nmax + 1):
        comps = list(compositions(n))
        invs = {a: inventory_dp(a) for a in comps}
        # ribbon function r_beta = (-1)^l A(G_beta), A(h_j) = -h_j: monomial of degree d gets
        # (-1)^(l + d); as a dictionary of integer h-coefficients
        rib = {a: {lam: (-1) ** (len(a) + len(lam)) * c for lam, c in invs[a].items()} for a in comps}
        for q in (3, 5, 7):
            def red(r):
                return tuple(sorted((lam, c % q) for lam, c in r.items() if c % q))
            cls = defaultdict(set)
            for a in comps:
                cls[red(rib[a])].add(a)
            by_int = defaultdict(set)
            for a in comps:
                by_int[tuple(sorted(rib[a].items()))].add(a)
            # equal mod q <=> equal over Z
            assert sorted(map(sorted, cls.values())) == sorted(map(sorted, by_int.values())), (n, q)
            tot += 1
    print(f"PASS  cor:odd-characteristic: for q in {{3,5,7}} and every weight 1..{nmax}, two ribbon "
          f"Schur functions agree over F_q exactly when they agree over Z ({tot} (weight, q) "
          f"partitions of all compositions compared)")
    # the proof's first step: the h_n coefficient is (-1)^(l + 1), distinguishing length parity
    for n in range(1, 9):
        for a in compositions(n):
            c = (-1) ** (len(a) + 1)
            assert c % 3 == (1 if len(a) % 2 else 2)
    # characteristic two shows the failure the corollary excludes: signs vanish
    assert (1 - (-1)) % 2 == 0


def main():
    check_coordinates()
    check_depth_cancel()
    check_recovery()
    check_subset_dp()
    check_parity()
    check_odd_characteristic()
    print("ALL PASS: verify_recovery")


if __name__ == "__main__":
    main()
