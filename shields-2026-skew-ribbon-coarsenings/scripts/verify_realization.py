r"""Paper section `sec:realization` (Realization at the original weight).

Targets: `lem:packing` (`eq:packing-ledger`, `eq:packing-budget`,
`eq:original-weight`), `ex:reflection`, `prop:propagation`, `prop:termination`
(`eq:common-factor`), `prop:local-alternative` (`eq:coarse-local-budget`).

Two kinds of object are swept.  Parametrized pairs (`_detector_common.py`) reach the
deep chains (up to L = 3 strict mask increases), and every real pair of compositions
of weight up to 18 with equal three-block data is run through the whole descent: its
normalized setting is built from the two compositions, the chain of least periods is
computed, the four- and (L + 4)-block detectors are found by the selection and packing
of the paper, and their labeled differences come from the chain DP of `eq:K`, never
from the closed forms they are compared with.
"""
import itertools
import random
from collections import Counter, defaultdict

from _detector_common import (CONFIGS, H, K_pair, f_y, least_period, least_period_chain,
                              make_setup_v, mask, search_probes, setup_from_pair,
                              supp_v_reps, theta_i)
from _ribbon_common import (Omega, circ, compositions, cuts, from_cuts, inventory_dp,
                            literal_decomposition, multiplicity, reverse, K_labeled)


def pack(S, a, chain, ys, probes):
    """The positive list of total n built from selected probes as in lem:packing, with the
    reflected variables and the ledger quantities.  `ys` = [y_0, ..., y_{L-1}] with
    y_{L-1} = t."""
    n, L = S.n, len(chain) - 1
    t = ys[L - 1]
    r, s, z = probes
    W = n - a
    p1 = chain[1]
    box = 3 * p1 + sum(chain[2:])                         # eq:packing-ledger
    sigma = sum(ys[:L - 1]) + r + s + z
    if sigma <= W - t:
        orient, (tt, yy, pr) = 'original', (t, list(ys[:L - 1]), [r, s, z])
    else:
        orient = 'reflected'
        tt = W - t
        yy = [chain[i + 2] - ys[i] for i in range(L - 1)]
        pr = [p1 - r, p1 - s, p1 - z]
        assert all(x > 0 for x in yy + pr + [tt])                  # reflected probes stay positive
        assert sum(yy) + sum(pr) == box - sigma                    # Sigma' = C_box - Sigma
        assert sum(yy) + sum(pr) <= W - tt == t, (sigma, W, t, box)   # the reflected list fits: Sigma' <= t
    deficit = W - tt - sum(yy) - sum(pr)
    assert deficit >= 0 and deficit % p1 == 0
    pr[0] += deficit                                               # pad a bottom probe by a multiple of p_1
    lst = [a, tt] + yy[::-1] + pr
    assert sum(lst) == n and len(lst) == L + 4                     # eq:original-weight
    return lst, orient, tt, yy, pr, box


def nested_value(S, a, chain, ys, probes):
    """-v(a) Delta prod(theta_i) H of the ORIGINAL selected probes (eq:nested-product)."""
    n, L = S.n, len(chain) - 1
    t = ys[L - 1]
    probe = S.__class__()
    probe.__dict__.update(S.__dict__)
    probe.chain = list(chain)
    Delta = S.b[(a + t) % n] - S.b[t % n]
    prod = 1
    for i in range(L - 1):
        prod *= theta_i(probe, i, ys[i], ys[i + 1])
    return -S.v[a] * Delta * prod * H(S, ys[0], *probes), Delta, prod


def layer_ok(chain, y, i):
    return y % chain[i] == 0 and y % chain[i + 1] != 0


def check_packing_parametrized():
    rng = random.Random(909)
    tot = refl = orig = 0
    fails_below = 0
    below_total = 0
    for (n, e, chain0, d) in CONFIGS:
        L = len(chain0) - 1
        for _ in range(40):
            S = make_setup_v(n, e, chain0, d, rng)
            ch = least_period_chain(S)
            if ch is None:
                continue
            P = ch[-1]
            p1 = ch[1]
            box = 3 * p1 + sum(ch[2:])
            # strict divisibility gives 2 p_1 + p_2 + ... + p_L <= 2 p_L: the "W >= 2P suffices" clause
            assert 2 * p1 + sum(ch[2:]) <= 2 * P and box - p1 <= 2 * P, ch
            for a in supp_v_reps(S):
                W = n - a
                for t in range(1, W):
                    if t % ch[L - 1] or t % P == 0:
                        continue
                    if S.b[(a + t) % n] == S.b[t]:
                        continue
                    got = search_probes(S, t, ch)
                    assert got is not None
                    ys, probes = got
                    base, Delta, prod = nested_value(S, a, ch, ys, probes)
                    assert base != 0 and abs(base) <= 2, (ch, ys, probes)    # the unpadded product is nonzero
                    if W < box - p1:                                           # below eq:packing-budget
                        sigma = sum(ys[:L - 1]) + sum(probes)
                        below_total += 1
                        if sigma > W - t and (box - sigma) > t:
                            fails_below += 1
                        continue
                    lst, orient, tt, yy, pr, box_ = pack(S, a, ch, ys, probes)
                    assert box_ == box
                    # layers kept (eq:layers), off the e-grid probes (so the pad is harmless)
                    for i in range(L - 1):
                        assert layer_ok(ch, yy[i], i), (ch, yy)
                    assert all(x % e for x in pr)
                    val = K_pair(S, lst)
                    assert val == base, (n, ch, a, t, ys, probes, lst, val, base)  # product unchanged
                    assert val != 0 and abs(val) <= 2
                    tot += 1
                    refl += orient == 'reflected'
                    orig += orient == 'original'
                    if orient == 'reflected':
                        # the three sign facts of the proof
                        probe = S.__class__()
                        probe.__dict__.update(S.__dict__)
                        probe.chain = list(ch)
                        for i in range(L - 1):
                            assert (theta_i(probe, i, yy[i], tt if i == L - 2 else yy[i + 1])
                                    == theta_i(probe, i, ys[i], ys[i + 1])), "theta' = theta"
                        assert S.b[(a + tt) % n] - S.b[tt % n] == -Delta, "Delta' = -Delta"
    assert tot > 100 and refl > 0 and orig > 0, (tot, refl, orig)
    print(f"PASS  lem:packing: {tot} (pair, a, t) cases with W >= C_box - p_1: positive list of "
          f"L + 4 labels, total n, same layers, probes off the e-grid, labeled difference equal "
          f"to the nonzero product of the original probes; {orig} fit as selected, {refl} needed the "
          f"reflection; strict-chain bound 2 p_1 + ... + p_L <= 2 P checked on every chain")
    print(f"NOTE  below the budget: {fails_below} of {below_total} (pair, a, t) cases fit in "
          f"neither orientation" + ("" if fails_below else " in this sample"))


def check_example_reflection():
    n = 30
    pattern = (0, 1, 1, 0, 0, 0, 1, 0, 1, 0)
    b = [pattern[x % 10] for x in range(n)]
    for x, val in ((5, 1), (25, 1), (15, 0), (10, 1), (20, 0)):
        b[x] = val
    c = list(b)
    c[10], c[20] = b[20], b[10]
    Sb = frozenset(x for x in range(1, n) if b[x])
    Sc = frozenset(x for x in range(1, n) if c[x])
    from _detector_common import Setup
    S = Setup()
    S.n, S.b, S.c, S.Sb, S.Sc = n, b, c, Sb, Sc
    S.u = [b[x] - c[(-x) % n] for x in range(n)]
    S.v = [b[x] - c[x] for x in range(n)]
    S.d = 10
    S.w = [S.u[x] if x % 10 else 0 for x in range(n)]
    S.e = least_period(S.w, n)
    assert S.e == 5 and all(S.v[x] == 0 for x in range(n) if x % 10)
    assert all(S.u[x] == S.w[x] for x in range(n) if x % 10) and S.u[10] == 0 == S.u[20]
    assert all(S.u[x] * S.v[x] == 0 for x in range(n))
    assert tuple(mask(S, 5)[x] for x in range(10)) == pattern and least_period(mask(S, 5), n) == 10
    S.chain, S.L = [5, 10], 1
    a, W, t = 10, 20, 15
    assert S.v[a] == 1
    H_t = H(S, t, 9, 8, 8)
    Delta = b[a + t] - b[t]
    assert (H_t, Delta) == (2, 1)
    assert sum((9, 8, 8)) == 25 and W - t == 5
    assert H(S, 5, 1, 2, 2) == -2 and b[a + 5] - b[5] == b[15] - b[5] == -1
    lst = [10, 5, 11, 2, 2]
    assert sum(lst) == n
    dK = K_pair(S, lst)
    assert dK == -2, dK
    lam = (11, 10, 5, 2, 2)
    dm = multiplicity(Sb, lam) - multiplicity(Sc, lam)
    assert dm == -1 and dK == 2 * dm                                      # kappa = 2! for the repeated 2
    lst2, orient, *_ = pack(S, a, [5, 10], [t], (9, 8, 8))
    assert lst2 == lst and orient == 'reflected', (lst2, orient)           # the packing routine reproduces it
    print("PASS  ex:reflection: masks, H_15(9,8,8) = 2, Delta = 1, reflected probes (1,2,2) with "
          "H_5 = -2, Delta' = -1, padded list (10,5,11,2,2) has labeled difference -2 and ordinary "
          "difference -1 at (11,10,5,2,2); the packing routine returns exactly this list")


# ---------------------------------------------------------- prop:propagation
def b_periodic(S, p, per):
    B = mask(S, p)
    return all(B[(x + per) % S.n] == B[x] for x in range(S.n))


def detectors_for(S, ch):
    """Every applicable positive detector at the top level of `ch`:
    (a, t, list, K) with n - a >= 2P, t in p_{L-1}Z \\ PZ, 0 < t < n - a, b(a+t) != b(t)."""
    n, L, P = S.n, len(ch) - 1, ch[-1]
    out = []
    for a in supp_v_reps(S):
        if n - a < 2 * P:
            continue
        for t in range(1, n - a):
            if t % ch[L - 1] or t % P == 0 or S.b[(a + t) % n] == S.b[t]:
                continue
            got = search_probes(S, t, ch)
            assert got is not None, (n, ch, t)
            ys, probes = got
            lst, *_ = pack(S, a, ch, ys, probes)
            out.append((a, t, lst, K_pair(S, lst)))
    return out


def check_propagation():
    rng = random.Random(31337)
    nonper = per_cases = 0
    for (n, e, chain0, d) in CONFIGS:
        for _ in range(60):
            S = make_setup_v(n, e, chain0, d, rng)
            ch = least_period_chain(S)
            if ch is None:
                continue
            P = ch[-1]
            dets = detectors_for(S, ch)
            assert all(K != 0 and abs(K) <= 2 for *_, K in dets)
            if not b_periodic(S, P, d):
                nonper += 1
                assert dets, (n, ch, "B_P is not d-periodic yet every applicable detector vanishes")
            else:
                per_cases += 1
    assert nonper > 20 and per_cases > 0, (nonper, per_cases)
    print(f"PASS  prop:propagation: {nonper} parametrized pairs whose top mask B_P is not "
          f"d-periodic each carry an applicable nonzero positive detector (every one built and "
          f"nonzero with |difference| <= 2); {per_cases} pairs with B_P d-periodic also run")


# --------------------------------------- real pairs: termination and local alternative
def gather_pairs(nmax):
    """All unordered pairs of compositions with equal three-block data, not identical and
    not reversals, as (A, B, n), for n up to nmax (grouped by the three-block inventory)."""
    out = []
    for n in range(4, nmax + 1):
        groups = defaultdict(list)
        for a in compositions(n):
            groups[tuple(sorted(inventory_dp(a, 3).items()))].append(a)
        for g in groups.values():
            for A, B in itertools.combinations(g, 2):
                if A != reverse(B):
                    out.append((A, B, n))
    return out


def check_real_pairs(nmax=18):
    pairs = gather_pairs(nmax)
    levels = Counter()
    nterm = nunequal = 0
    nprobes = 0
    for A, B, n in pairs:
        S = setup_from_pair(A, B)
        assert S is not None, (A, B)
        d, e, ch = S.d, S.e, S.chain
        assert 3 <= e and d % e == 0 and d < n and n // d >= 3                 # eq:basic-periods
        # p_j | p_{j+1} | d is a statement about the iteration AFTER each propagation succeeded
        # (prop:termination), so it is asserted level by level below, only once the detectors
        # of the previous level have vanished
        full_equal = (inventory_dp(A) == inventory_dp(S.gamma))
        # four-block level: all four-block differences vanish iff B_e is d-periodic
        four_nonzero = False
        for a in supp_v_reps(S):
            for r in range(1, n):
                if r % d == 0:
                    continue
                for s in range(1, n):
                    z = n - a - r - s
                    if z < 1 or s % d == 0 or z % d == 0:
                        continue
                    if K_pair(S, (a, r, s, z)) != 0:
                        four_nonzero = True
                        break
                if four_nonzero:
                    break
            if four_nonzero:
                break
        if four_nonzero:
            levels['four-block'] += 1
            assert not full_equal, (A, B)
            continue
        assert b_periodic(S, e, d), (A, B)                                       # lem:four-start
        # strict mask increases: each level L has a detector exactly when B_P is not d-periodic
        found_level = None
        valid = 0
        for L in range(1, len(ch)):
            assert ch[L] % ch[L - 1] == 0 and d % ch[L] == 0, (A, B, ch, L)   # p_(L-1) | p_L | d
            valid = L
            sub = ch[:L + 1]
            P = sub[-1]
            probe = S.__class__()
            probe.__dict__.update(S.__dict__)
            probe.chain, probe.L = sub, L
            dets = detectors_for(probe, sub)
            if not b_periodic(S, P, d):
                assert dets, (A, B, sub)
            nz = [x for x in dets if x[3] != 0]
            nprobes += len(dets)
            if nz:
                assert not full_equal, (A, B)
                assert all(len(x[2]) == L + 4 and abs(x[3]) <= 2 for x in nz)
                found_level = L
                break
        if found_level is not None:
            levels[f'L={found_level} ({found_level + 4} blocks)'] += 1
            continue
        # all detectors vanish: termination at p with literal common factor (eq:common-factor)
        p = ch[-1]
        assert all(ch[j + 1] % ch[j] == 0 and d % ch[j + 1] == 0 for j in range(len(ch) - 1)), (A, B, ch)
        assert len(ch) - 1 <= Omega(d // e) and 4 + Omega(d // e) <= Omega(n) + 2, (A, B)
        da, ea = literal_decomposition(A, p) or (None, None)
        db, eb = literal_decomposition(S.gamma, p) or (None, None)
        assert ea is not None and ea == eb and 3 <= p <= d < n, (A, S.gamma, p, ch)
        nterm += 1
        if not full_equal:
            nunequal += 1
            levels['unequal despite vanishing detectors (outer pair differs)'] += 1
        else:
            levels['equivalent: terminates in a common inner factor'] += 1
    assert nterm > 0
    # 4 + Omega(d/e) <= Omega(n) + 2 on every real pair (the arithmetic of prop:local-alternative)
    for A, B, n in pairs:
        S = setup_from_pair(A, B)
        assert 4 + Omega(S.d // S.e) <= Omega(n) + 2, (A, B)
    print(f"PASS  prop:termination, prop:local-alternative on all {len(pairs)} unequal, unreversed "
          f"pairs equal through three blocks of weight 4..{nmax}: p_j | p_(j+1) | d along the least-"
          f"period chain; the descent ends in "
          + "; ".join(f"{k}: {v}" for k, v in sorted(levels.items()))
          + f"; every terminating pair has a literal common inner factor of weight 3 <= p <= d < n "
          f"and L <= Omega(d/e), 4 + Omega(d/e) <= Omega(n) + 2")


def main():
    check_example_reflection()
    check_packing_parametrized()
    check_propagation()
    check_real_pairs()
    print("ALL PASS: verify_realization")


if __name__ == "__main__":
    main()
