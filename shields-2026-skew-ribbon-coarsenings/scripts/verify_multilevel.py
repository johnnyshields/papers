r"""Paper appendix `app:multilevel` (A multilevel marked detector).

Rebuilds the weight-72 example from the two displayed cut sets, recomputes `v`, the
mask periods `p_0, p_1, p_2`, the packing ledger and the reflection of `lem:packing`,
each factor of the detector, and the labeled and ordinary discrepancies.  The labeled
difference is the chain DP of `eq:K` on the six labels, and the ordinary difference is
the subset DP of `eq:subset-dp` on the partition (36, 24, 6, 4, 1, 1); neither is
computed from the closed form it is compared with.
"""
from _detector_common import H, Setup, least_period, mask, theta_i, K_pair
from _ribbon_common import K_labeled, multiplicity


def main():
    n = 72
    S0 = ({x for x in range(1, 72) if x % 4 == 1}
          | {x for x in range(1, 72) if x % 12 == 6}
          | {x for x in range(1, 72) if x % 24 in (8, 16)}
          | {24, 36})
    T0 = (S0 - {24}) | {48}
    b = [1 if x in S0 else 0 for x in range(n)]
    c = [1 if x in T0 else 0 for x in range(n)]
    S = Setup()
    S.n = n
    S.b, S.c = b, c
    S.Sb, S.Sc = frozenset(S0), frozenset(T0)
    S.u = [b[x] - c[(-x) % n] for x in range(n)]
    S.v = [b[x] - c[x] for x in range(n)]
    S.tau = [b[x] + b[(-x) % n] for x in range(n)]
    assert S.v[24] == 1 and S.v[48] == -1                                 # v(24) = 1, v(48) = -1
    assert {x for x in range(n) if S.v[x]} == {24, 48}
    d = 24
    assert all(S.u[x] * S.v[x] == 0 for x in range(n))                    # disjoint supports
    assert all(S.u[x] == -S.u[(-x) % n] and S.v[x] == -S.v[(-x) % n] for x in range(n))
    assert all(S.u[x] == b[x] - b[(-x) % n] for x in range(n) if x % d)    # u = odd part of b off the d-grid
    S.d = d
    S.w = [S.u[x] if x % d else 0 for x in range(n)]
    S.e = least_period(S.w, n)
    assert S.e == 4                                                         # off-grid odd part has least period 4
    assert all(S.w[x] == -S.w[(-x) % n] for x in range(n)) and any(S.w)
    # the mask periods are least periods 4, 12, 24
    p0 = 4
    p1 = least_period(mask(S, p0), n)
    p2 = least_period(mask(S, p1), n)
    assert (p1, p2) == (12, 24), (p1, p2)
    assert p2 == d
    S.chain, S.L = [p0, p1, p2], 2
    B4 = mask(S, 4)
    assert all(B4[x] == 1 for x in range(n) if x % 4 == 1)                  # active residues 1 mod 4
    assert all(B4[x] == 1 for x in range(n) if x % 12 == 6)                 # the neutral residue 6 mod 12
    assert least_period(B4, n) == 12
    B12 = mask(S, 12)
    assert least_period(B12, n) == 24                                       # 8, 16 mod 24 make it 24
    # a = 24, witness t = 12, y_0 = 20, (r, s, z) = (11, 11, 6): sum 48 against W - t = 36
    a, t, y0, probes = 24, 12, 20, (11, 11, 6)
    W = n - a
    sigma = y0 + sum(probes)
    assert (W, sigma, W - t) == (48, 48, 36) and sigma > W - t              # does not fit
    box = 3 * p1 + p2
    assert box == 60 and W == box - p1                                       # the budget is met with equality
    assert (t + y0 + sum(probes)) % p1 == 0                                  # eq:sum-congruence
    # the original witness is a genuine one: nonzero theta_0 and H, and Delta
    assert theta_i(S, 0, y0, t) != 0 and H(S, y0, *probes) != 0
    assert b[a + t] - b[t] != 0 and S.v[a] != 0
    # reflection is forced: the original orientation does not fit, the reflected one does
    tp = W - t
    y0p = p2 - y0
    pr = tuple(p1 - x for x in probes)
    assert (tp, y0p, pr) == (36, 4, (1, 1, 6))                               # t', y_0', (r', s', z')
    assert sum((y0p,) + pr) == 12                                            # Sigma' = 12 = C_box - Sigma
    assert 12 == box - sigma
    assert a + tp + y0p + sum(pr) == 72                                      # no padding needed
    # the four factors of the detector
    assert S.v[24] == 1
    assert b[60] - b[36] == -1
    assert B12[40] - B12[4] == 1
    assert H(S, y0p, *pr) == -2
    assert theta_i(S, 0, y0p, tp) == B12[(y0p + tp) % n] - B12[y0p] == 1
    # labeled difference is -2, by the chain DP of eq:K on the six labels
    labels = (a, tp, y0p) + pr
    assert labels == (24, 36, 4, 1, 1, 6) and sum(labels) == 72
    dK = K_pair(S, labels)
    assert dK == -2, dK
    assert dK == -S.v[a] * (b[a + tp] - b[tp]) * theta_i(S, 0, y0p, tp) * H(S, y0p, *pr)
    # ordinary discrepancy -1 at (36, 24, 6, 4, 1, 1): the only repeated part is the pair of ones
    lam = (36, 24, 6, 4, 1, 1)
    assert sorted(lam, reverse=True) == list(lam) and sum(lam) == 72
    dm = multiplicity(S.Sb, lam) - multiplicity(S.Sc, lam)
    assert dm == -1 and dK == 2 * dm                                         # kappa = 2! from the pair of ones
    assert sorted(__import__('collections').Counter(lam).values()) == [1, 1, 1, 1, 2]
    print("PASS  app:multilevel: cut sets rebuilt; v(24) = 1, v(48) = -1; e = 4; least mask periods "
          "4, 12, 24; the initial witness (12, 20, (11,11,6)) has sum 48 > 36 and the reflection is "
          "forced; C_box = 60 = W + p_1; reflected list (24,36,4,1,1,6) sums to 72 with factors "
          "1, -1, 1, -2; labeled difference -2 and ordinary difference -1 at (36,24,6,4,1,1)")
    print("ALL PASS: verify_multilevel")


if __name__ == "__main__":
    main()
