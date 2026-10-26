r"""`thm:two-cap`, `eq:two-caps`, `eq:floor-input`, `eq:Phi`, `eq:cap-shift`: the exclusion argument run on
actual h-polynomial vectors, not on integer profiles.

For a vector G of h-polynomials on a grid d_0 = 0 < d_1 < ... the shifted sums are
P_k(G) = sum_j G_j h_{k+d_j}, computed exactly.  Three assertions at the square weight.

  (1) the valuation step of the proof: if G_0 != 0 and the floor input holds, then at every cap shift
      r + k with k > 0 (and, at r = 0, at every shift k > a) the j = 0 summand is the strict unique
      minimizer, so wt(P_{r+k}(G)) = wt(G_0) + (r + k)^2 and in particular P_{r+k}(G) != 0;
  (2) the theorem: no vector satisfying the floor input has both P_{r+a}(G) = h_a P_r(G) and
      P_{r+b}(G) = h_b P_r(G);
  (3) non-vacuity and the load-bearing hypothesis: for every grid in a range the vector G built as
      the 2 x 3 minors of [h_{a+d_j}; h_{b+d_j}] satisfies P_a(G) = P_b(G) = 0 identically with G_0 != 0
      (two vanishing caps), and on every one the floor input FAILS, as the theorem requires.

Vectors for (1) and (2) are drawn at random with a seeded generator, with small coefficients, from
supports that include the zero polynomial, so the floor input holds on some and fails on others.
"""
import random
from itertools import combinations

from skew_core import h, padd, pmul

SEED = 20260102


def sq_wt(f):
    return min(sum(e * e for e in m) for m in f) if f else None


def P(G, d, k):
    out = {}
    for j, f in enumerate(G):
        if f and k + d[j] >= 0:
            out = padd(out, pmul(f, h(k + d[j])))
    return out


def alpha(G, d):
    return [None if not f else sq_wt(f) + d[j] ** 2 for j, f in enumerate(G)]


def floor_input(G, d, gamma):
    al = alpha(G, d)
    return all(al[0] - al[j] <= 2 * gamma * d[j] for j in range(len(G)) if G[j])


def rand_poly(rng):
    if rng.random() < 0.25:
        return {}
    out = {}
    for _ in range(rng.randint(1, 3)):
        m = tuple(sorted((rng.randint(1, 5) for _ in range(rng.randint(1, 3))), reverse=True))
        out = padd(out, {m: rng.choice([-2, -1, 1, 2])})
    return out


def main():
    rng = random.Random(SEED)
    n_val = n_thm = n_floor_true = n_floor_false = 0
    for _ in range(4000):
        m = rng.randint(2, 4)
        d = [0] + sorted(rng.sample(range(1, 9), m))
        G = [rand_poly(rng) for _ in range(m + 1)]
        if not G[0]:
            G[0] = {(rng.randint(1, 5),): 1}
        a = rng.randint(1, 3)
        b = a + rng.randint(1, 3)
        r = rng.randint(0, 3)
        gamma = a if r == 0 else r
        if not floor_input(G, d, gamma):
            n_floor_false += 1
            continue
        n_floor_true += 1
        w0 = sq_wt(G[0])
        shifts = [r + a, r + b] if r > 0 else [b]
        for s in shifts:
            Ps = P(G, d, s)
            assert Ps, ("j = 0 summand must survive", d, s)
            assert sq_wt(Ps) == w0 + s * s, ("valuation of P_{r+k}", d, s)
            n_val += 1
        lhs_a = P(G, d, r + a) == pmul(h(a), P(G, d, r)) if r > 0 else not P(G, d, a)
        lhs_b = P(G, d, r + b) == pmul(h(b), P(G, d, r)) if r > 0 else not P(G, d, b)
        assert not (lhs_a and lhs_b), ("two caps coexist", d, G, r, a, b)
        n_thm += 1
    assert n_floor_true > 200 and n_floor_false > 200 and n_val > 200

    n_ctrl = 0
    for d1, d2 in combinations(range(1, 9), 2):
        d = [0, d1, d2]
        for a in range(1, 4):
            for b in range(a + 1, 5):
                rows2 = [[h(k + dj) for dj in d] for k in (a, b)]
                def minor(c1, c2):
                    return padd(pmul(rows2[0][c1], rows2[1][c2]), pmul(rows2[0][c2], rows2[1][c1]), -1)
                G = [minor(1, 2), padd({}, minor(0, 2), -1), minor(0, 1)]
                assert not P(G, d, a) and not P(G, d, b), ("two vanishing caps by construction", d, a, b)
                if G[0] and all(G):
                    assert not floor_input(G, d, a), ("floor input must fail where two caps hold", d, a, b)
                    n_ctrl += 1
    assert n_ctrl > 50
    print("random vectors: floor input holds %d, fails %d" % (n_floor_true, n_floor_false))
    print("valuation of the j = 0 summand confirmed at %d shifts; no coexisting caps on %d vectors" % (n_val, n_thm))
    print("two-vanishing-cap vectors built from 2x3 minors: %d, floor input fails on every one" % n_ctrl)
    print("ALL PASS")


if __name__ == "__main__":
    main()
