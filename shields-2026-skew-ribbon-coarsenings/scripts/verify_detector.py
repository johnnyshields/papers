r"""Paper section `sec:detector` (Period masks and marked coarsenings).

Targets: `lem:fiber`, `lem:four-start` (`eq:four-identity`), `lem:antichain`,
`thm:nested` (`eq:chain`, `eq:layers`, `eq:deltaH`, `eq:J`, `eq:nested-product`),
`lem:bottom` (`eq:bottom-probes`, `eq:shifted-reflection`), `lem:selection`
(`eq:probe-bounds`, `eq:sum-congruence`).

Pairs of cut indicators in the normalized setting are drawn from their free
parametrization (`_detector_common.py`), and the defining equations are re-checked on
every built pair.  The labeled difference `Delta K` is always computed from the cut
sets by the chain DP of `eq:K`; the right-hand sides are the paper's closed forms, so
each identity compares two routes.  Exact integers and `fractions` throughout.
"""
import itertools
import random
from fractions import Fraction

from _detector_common import (CONFIGS, H, K_pair, f_y, least_period, least_period_chain,
                              make_setup_v, mask, sample_list, search_probes, supp_v_reps,
                              theta_i)
from _ribbon_common import K_labeled


# ------------------------------------------------------------- lem:fiber
def odd_ternary_functions(N):
    half = (N - 1) // 2
    for combo in itertools.product((-1, 0, 1), repeat=half):
        f = [0] * N
        for x, vv in enumerate(combo, start=1):
            f[x], f[N - x] = vv, -vv
        yield f


def fe(w, f, N):
    for x in range(N):
        for y in range(N):
            s = (x + y) % N
            if w[x] * f[y] + f[x] * w[y] != w[s] * (f[x] + f[y]) + f[s] * (w[x] + w[y]):
                return False
    return True


def check_fiber():
    nw = nf_hit = nzero = 0
    for N0 in range(3, 12):
        for w in odd_ternary_functions(N0):
            if not any(w):
                continue
            e = least_period(w, N0)
            for f in itertools.product((-1, 0, 1), repeat=N0):
                if any(w[x] and f[x] for x in range(N0)):
                    continue                                           # w f = 0
                if not fe(w, f, N0):
                    continue
                nw += 1
                assert all(f[(t + e) % N0] == f[t] for t in range(N0) if t % e), (N0, w, f)   # eq:fiber-period
                if all(f[x] == 0 for x in range(0, N0, e)) and all(
                        sum(f[x] for x in range(N0) if x % e == ρ) == 0 for ρ in range(e)):
                    assert not any(f), (N0, w, f)                      # second assertion
                    nzero += 1
                if any(f):
                    nf_hit += 1
    assert nf_hit > 0 and nzero > 0
    print(f"PASS  lem:fiber: all {nw} (w, f) with w nonzero odd ternary, wf = 0, eq:FE, on Z/N0 "
          f"for N0 = 3..11 and f ternary ({nf_hit} with f != 0); zero-sum conclusion on {nzero}")


# --------------------------------------------------------- lem:antichain
def check_antichain():
    rng = random.Random(11)
    cases = 0
    for r in (3, 4, 5):
        verts = [m for m in range(1, (1 << r) - 1)]
        full = (1 << r) - 1

        def Z(F, I, J):
            """sum over maximal chains I -> J of products of intermediate weights."""
            if I == J:
                return 1
            tot = 0
            rest = J & ~I
            while rest:
                low = rest & -rest
                nxt = I | low
                tot += (F[nxt] if nxt != J else 1) * Z(F, nxt, J)
                rest ^= low
            return tot

        for _ in range(60):
            F = {m: rng.randint(-3, 3) for m in verts}
            # a random antichain: pairwise incomparable vertices
            order = verts[:]
            rng.shuffle(order)
            A = []
            for m in order:
                if all((m & q) != m and (m & q) != q for q in A):
                    A.append(m)
                if len(A) >= rng.randint(1, 4):
                    break
            delta = {m: rng.randint(-3, 3) for m in A}
            F2 = dict(F)
            for m in A:
                F2[m] += delta[m]
            lhs = Z(F2, 0, full) - Z(F, 0, full)
            rhs = sum(delta[m] * Z(F, 0, m) * Z(F, m, full) for m in A)
            assert lhs == rhs, (r, F, A)
            cases += 1
    print(f"PASS  lem:antichain: {cases} random vertex weightings and antichains on 2^M, |M| = 3..5")


# ----------------------------------------------------------- lem:four-start
def check_four_start():
    rng = random.Random(5)
    seen = nonzero = 0
    for (n, e, chain, d) in CONFIGS + [(24, 4, [4, 8], 8), (40, 4, [4, 8], 8), (36, 6, [6, 12], 12)]:
        for _ in range(6):
            S = make_setup_v(n, e, chain, d, rng, free=True)
            for a in supp_v_reps(S):
                for r in range(1, n):
                    if r % d == 0:
                        continue
                    for s in range(1, n):
                        z = n - a - r - s
                        if z < 1 or s % d == 0 or z % d == 0:
                            continue
                        lhs = K_pair(S, (a, r, s, z))
                        w, tau = S.w, S.tau

                        def term(x, y, q):
                            return (w[y % n] + w[q % n]) * (tau[x % n] - tau[(x + a) % n])

                        rhs = Fraction(S.v[a], 2) * (term(r, s, z) + term(s, z, r) + term(z, r, s))
                        assert lhs == rhs, (S.Sb, a, r, s, z, lhs, rhs)        # eq:four-identity
                        assert abs(lhs) <= 2
                        seen += 1
                        nonzero += lhs != 0
    assert nonzero > 0
    print(f"PASS  lem:four-start (eq:four-identity): {seen} (pair, a, r, s, z) four-block cases, "
          f"{nonzero} nonzero, all |Delta K| <= 2")


def check_four_start_periodicity():
    """If every four-block difference vanishes, B_e is d-periodic (exhaustive on small n)."""
    total = ante = 0
    for (n, e, d) in [(24, 4, 8), (30, 5, 10), (40, 4, 8)]:
        # enumerate the free data: sign pattern of w, free even pairs, d-grid values
        resvals = []
        wlist = []
        for combo in itertools.product((-1, 0, 1), repeat=(e - 1) // 2):
            wres = [0] * e
            for r, vv in enumerate(combo, start=1):
                wres[r], wres[e - r] = vv, -vv
            if any(wres):
                wlist.append(wres)
        for wres in wlist:
            w = [wres[x % e] for x in range(n)]
            pairs, seen = [], set()
            for x in range(1, n):
                if x % d == 0 or x in seen:
                    continue
                y = (-x) % n
                seen |= {x, y}
                if w[x] == 0:
                    pairs.append((x, y))
            dgrid = [x for x in range(d, n, d)]
            for pv in itertools.product((0, 1), repeat=len(pairs)):
                for dv in itertools.product((0, 1), repeat=len(dgrid)):
                    b = [0] * n
                    for x in range(1, n):
                        if x % d and w[x] == 1:
                            b[x] = 1
                    for (x, y), val in zip(pairs, pv):
                        b[x] = b[y] = val
                    for x, val in zip(dgrid, dv):
                        b[x] = val
                    c = list(b)
                    for x in dgrid:
                        c[x] = b[(-x) % n]
                    v = [b[x] - c[x] for x in range(n)]
                    if not any(v):
                        continue
                    Sb = frozenset(x for x in range(1, n) if b[x])
                    Sc = frozenset(x for x in range(1, n) if c[x])
                    vanish = True
                    for a in range(1, n):
                        if not v[a] or not vanish:
                            continue
                        for r in range(1, n):
                            if r % d == 0 or not vanish:
                                continue
                            for s in range(1, n):
                                z = n - a - r - s
                                if z < 1 or s % d == 0 or z % d == 0:
                                    continue
                                if K_labeled(Sb, (a, r, s, z)) != K_labeled(Sc, (a, r, s, z)):
                                    vanish = False
                                    break
                            if not vanish:
                                break
                    total += 1
                    if vanish:
                        ante += 1
                        Be = [0 if x % e == 0 else b[x] for x in range(n)]
                        assert all(Be[(x + d) % n] == Be[x] for x in range(n)), (n, e, d, b)
    assert 0 < ante < total
    print(f"PASS  lem:four-start (periodicity clause): {total} normalized pairs on n in "
          f"{{24, 30, 40}}, {ante} with every four-block difference zero; each has B_e d-periodic "
          f"(and {total - ante} do not, so the hypothesis is not vacuous)")


# --------------------------------------------------------------- thm:nested
def check_nested():
    rng = random.Random(2026)
    total = nonzero = 0
    by_L = {}
    for (n, e, chain, d) in CONFIGS:
        L = len(chain) - 1
        for _ in range(8):
            S = make_setup_v(n, e, chain, d, rng)
            for _ in range(250):
                lst = sample_list(S, rng)
                if lst is None:
                    continue
                a, ys, r, s, z = lst
                labels = [a] + ys[::-1] + [r, s, z]          # (a, y_{L-1}, ..., y_0, r, s, z)
                assert sum(labels) == n and len(labels) == L + 4
                lhs = K_pair(S, labels)
                t = ys[L - 1]
                Delta = S.b[(a + t) % n] - S.b[t % n]
                prod = 1
                for i in range(L - 1):
                    prod *= theta_i(S, i, ys[i], ys[i + 1])
                rhs = -S.v[a] * Delta * prod * H(S, ys[0], r, s, z)
                assert lhs == rhs, (n, chain, labels, lhs, rhs)              # eq:nested-product
                assert abs(lhs) <= 2
                total += 1
                nonzero += lhs != 0
                by_L[L] = by_L.get(L, 0) + 1
    assert nonzero > 20 and set(by_L) >= {1, 2, 3}, (nonzero, by_L)
    print(f"PASS  thm:nested (eq:nested-product): {total} lists of L + 4 labels, {nonzero} with "
          f"Delta K != 0, all |Delta K| <= 2; chain lengths L covered: {dict(sorted(by_L.items()))}")


# --------------------------------------------------------------- lem:bottom
def check_bottom():
    rng = random.Random(77)
    checked = 0
    for (n, e, chain, d) in CONFIGS:
        for _ in range(12):
            S = make_setup_v(n, e, chain, d, rng)
            Be = mask(S, e)
            p = least_period(Be, n)
            if p <= e:
                continue
            for y in range(e, n, e):
                if y % p == 0:
                    continue
                # f_y on Z/p: nonzero, vanishes on eZ, zero class sums, w f = 0, shifted reflection
                fy = [f_y(S, y, x) for x in range(p)]
                assert any(fy)
                assert all(fy[x] == 0 for x in range(0, p, e))
                assert all(sum(fy[x] for x in range(p) if x % e == rr) == 0 for rr in range(e))
                assert all(S.w[x % n] * fy[x] == 0 for x in range(p))
                assert all(f_y(S, y, (-y - x) % n) == -f_y(S, y, x) for x in range(n)), "eq:shifted-reflection"
                found = None
                for r in range(1, p):
                    if r % e == 0:
                        continue
                    for s in range(1, p):
                        if s % e == 0:
                            continue
                        z = (-y - r - s) % p
                        if z == 0 or z % e == 0:
                            continue
                        if H(S, y, r, s, z) != 0:
                            found = (r, s, z)
                            break
                    if found:
                        break
                assert found, (n, chain, y, p)                                  # eq:bottom-probes
                checked += 1
    assert checked > 10
    print(f"PASS  lem:bottom: {checked} (mask, y) cases where B_e has least period p > e: "
          f"probes r, s, z in (0, p), off the e-grid, summing to -y mod p, with H_y != 0; "
          f"eq:shifted-reflection holds on all of Z/n")


# ------------------------------------------------------------ lem:selection
def check_selection():
    rng = random.Random(4242)
    checked = 0
    by_L = {}
    for (n, e, chain, d) in CONFIGS:
        L = len(chain) - 1
        for _ in range(60):
            S = make_setup_v(n, e, chain, d, rng)
            ch = least_period_chain(S)
            if ch is None:
                continue
            P = ch[-1]
            for t in range(1, n):
                if t % ch[L - 1] or t % P == 0:
                    continue
                got = search_probes(S, t, ch)
                assert got is not None, (n, ch, t)                               # lem:selection
                ys, (r, s, z) = got
                assert (t + sum(ys[:L - 1]) + r + s + z) % ch[1] == 0           # eq:sum-congruence
                checked += 1
                by_L[L] = by_L.get(L, 0) + 1
    assert checked > 10 and len(by_L) >= 2, by_L
    print(f"PASS  lem:selection: probes meeting eq:probe-bounds, eq:layers, eq:sum-congruence "
          f"found for {checked} (mask chain of least periods, t) cases; L covered: {dict(sorted(by_L.items()))}")


def main():
    check_fiber()
    check_antichain()
    check_four_start()
    check_four_start_periodicity()
    check_nested()
    check_bottom()
    check_selection()
    print("ALL PASS: verify_detector")


if __name__ == "__main__":
    main()
