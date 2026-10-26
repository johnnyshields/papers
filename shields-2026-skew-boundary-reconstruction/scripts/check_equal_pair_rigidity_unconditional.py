"""`thm:equal-pair-rigidity` (`subsec:actual-equality`): does actual skew-Schur equality supply the cap-fixed antecedent by itself?

The manuscript reaches its adjacent-edge chain through the ratio identity.
This script tests the claim that an ACTUAL equal pair with a common inner
boundary supplies Theorem cap-fixed-rigidity's hypotheses outright, with no
ratio identity anywhere:

  (1) G_0 = C_0(X) - C_0(Y) = s_X - s_Y = 0, so alpha_0 = +infinity and the
      floor antecedent alpha_0 > m_+ is automatic;
  (2) equality forces lambda_0 = kappa_0, hence a common cap grid, through the
      largest generator index actually occurring in the polynomial;
  (3) equality forces equal row-length multisets, hence equal initial energy;
  (4) so the chain is M_i = {i+1, i+2} for 0 <= i < v -- WITHOUT the virtual
      edge M_{-1} = {0,1}, which belongs to the nonzero-defect ratio problem;
  (5) C_1(X) = -s_{Xbar}, so G_1 != 0 separates the first-row-deleted children;
  (6) P_a(G) != 0 for every a > 0, so one capped observation separates too.

Controls that must FIRE, or the checks below prove nothing:
  * a pair carrying the fingerprint that is NOT equal;
  * a pair with identical row and column overlap partitions that is not equal;
  * the trivial witness A = B = (1): its defect G is zero, so the ratio identities hold vacuously.

Exact integer arithmetic on signed h-monomials throughout.
"""

import itertools
from collections import defaultdict

from check_cofactor_factorization_and_reconstruction import (
    cap_matrix, det, h, padd, pmul, pscal,
)

SIZE_CAP = 13
ROW_CAP = 5
INF = float("inf")


def jt_det(lam, mu):
    """s_{lam/mu} in the h-basis."""
    n = len(lam)
    rows = [[h(lam[i] - mu[t] - i + t) for t in range(n)] for i in range(n)]
    return det(rows)


def cofactors(lam, mu):
    M, a, b = cap_matrix(lam, mu)
    n = len(lam)
    cof = [pscal((-1) ** j, det([r[:j] + r[j + 1:] for r in M]))
           for j in range(n + 1)]
    return cof, [b[0] - b[j] for j in range(n + 1)]


def wt(f, om):
    return INF if not f else min(sum(om(k) for k in m) for m in f)


def sub(f, g):
    return padd(f, pscal(-1, g))


def P(cof, d, k):
    out = {}
    for j, c in enumerate(cof):
        out = padd(out, pmul(c, h(k + d[j])))
    return out


def connected(lam, mu):
    n = len(lam)
    if any(lam[i] < lam[i + 1] for i in range(n - 1)):
        return False
    if any(mu[i] < mu[i + 1] for i in range(n - 1)):
        return False
    if any(lam[i] - mu[i] < 1 for i in range(n)):
        return False
    return all(lam[i + 1] > mu[i] for i in range(n - 1))


def shapes(size_cap, row_cap):
    """Connected lambda/mu with mu_{n-1} = 0 and every row nonempty."""
    for n in range(1, row_cap + 1):
        for rho in itertools.product(range(1, size_cap + 1), repeat=n):
            if sum(rho) > size_cap:
                continue
            for o in itertools.product(range(1, size_cap + 1), repeat=max(n - 1, 0)):
                if any(o[i] > min(rho[i], rho[i + 1]) for i in range(n - 1)):
                    continue
                mu = [0] * n
                lam = [0] * n
                lam[n - 1] = rho[n - 1]
                for i in range(n - 2, -1, -1):
                    mu[i] = lam[i + 1] - o[i]
                    lam[i] = mu[i] + rho[i]
                if any(v < 0 for v in mu) or not connected(lam, mu):
                    continue
                yield tuple(lam), tuple(mu)


SQ = lambda k: k * k
CU = lambda k: k ** 3
RX = lambda k: 0 if k == 0 else 7 ** k
WEIGHTS = [("square", SQ), ("cubic", CU), ("radix7", RX)]

sfun = {}
def S(lam, mu):
    k = (lam, mu)
    if k not in sfun:
        sfun[k] = jt_det(list(lam), list(mu))
    return sfun[k]


def main():
    # ---------------------------------------------------------------- (0) the hypothesis as printed
    one = ((1,), (0,))
    cof1, d1 = cofactors(*one)
    G_triv = [sub(c, c) for c in cof1]
    for (r, a, b) in [(0, 1, 2), (3, 1, 4), (0, 2, 5)]:
        for k in (a, b):
            lhs = P(G_triv, d1, r + k)
            rhs = pmul(h(k), P(G_triv, d1, r))
            assert lhs == {} and rhs == {}, (r, k)
    assert all(not g for g in G_triv)
    print("trivial witness -- A = B = (1) gives G = 0 and satisfies both")
    print("  ratio identities at every (r, a, b).  The second alternative is")
    print("  therefore ALWAYS available, for any input pair.  TAUTOLOGY CONFIRMED.")

    # ---------------------------------------------------------------- census
    pool = list(shapes(SIZE_CAP, ROW_CAP))
    by_mu = defaultdict(list)
    for lam, mu in pool:
        by_mu[mu].append(lam)
    print("\nconnected diagrams, size <= %d, rows <= %d: %d" % (SIZE_CAP, ROW_CAP, len(pool)))


    pairs = []
    for mu, lams in by_mu.items():
        buckets = defaultdict(list)
        for lam in lams:
            buckets[tuple(sorted(S(lam, mu).items()))].append(lam)
        for cls in buckets.values():
            if len(cls) > 1:
                for x, y in itertools.combinations(sorted(cls), 2):
                    pairs.append((mu, x, y))
    print("distinct equal pairs sharing an inner boundary: %d" % len(pairs))

    capalign = rowmult = chain_ok = child_sep = cap_sep = 0
    for mu, lam, kap in pairs:
        n = len(lam)
        assert len(kap) == n
        # (2) cap alignment
        assert lam[0] == kap[0], ("cap alignment fails", mu, lam, kap)
        capalign += 1
        # (3) equal row-length multisets
        rx = sorted(lam[i] - mu[i] for i in range(n))
        ry = sorted(kap[i] - mu[i] for i in range(n))
        assert rx == ry, ("row multisets differ", mu, lam, kap)
        rowmult += 1

        cx, dx = cofactors(list(lam), list(mu))
        cy, dy = cofactors(list(kap), list(mu))
        assert dx == dy
        G = [sub(cx[j], cy[j]) for j in range(n + 1)]
        # (1) the antecedent, free
        assert not G[0], ("G_0 should vanish", mu, lam, kap)
        assert any(G[1:]), "G must be nonzero"
        v = min(i for i in range(n) if lam[i] != kap[i])
        assert v >= 1, ("first change at row 0 contradicts cap alignment", lam, kap)

        A = [dx[0] - (lam[i] - (i + 1)) for i in range(n)]
        A = [lam[0] - 1 - (lam[i] - (i + 1)) for i in range(n)]
        for name, om in WEIGHTS:
            al = [wt(G[j], om) + om(dx[j]) for j in range(n + 1)]
            assert al[0] == INF
            mplus = min(al[1:])
            assert mplus < INF and al[0] > mplus
            # (4) the adjacent chain, with NO virtual edge asserted
            for i in range(0, v):
                F = {}
                for j in range(n + 1):
                    if G[j]:
                        F[j] = wt(G[j], om) + om(dx[j] - A[i])
                lo = min(F.values())
                M = {j for j, val in F.items() if val == lo}
                assert M == {i + 1, i + 2}, ("chain", name, mu, lam, kap, i, sorted(M))
            for j in range(1, v + 2):
                assert G[j], ("support prefix", name, mu, lam, kap, j)
        chain_ok += 1

        # (5) the children separate, via C_1 = -s_bar
        if n >= 2:
            bx, by = (lam[1:], mu[1:]), (kap[1:], mu[1:])
            assert cx[1] == pscal(-1, S(*bx)), "C_1(X) = -s_Xbar"
            assert cy[1] == pscal(-1, S(*by))
            assert S(*bx) != S(*by), ("children equal", mu, lam, kap)
            child_sep += 1

        # (6) one positive cap separates
        for a in range(1, 8):
            assert P(G, dx, a), ("cap response vanishes", mu, lam, kap, a)
        cap_sep += 1

    print("  cap alignment lambda_0 = kappa_0     : %d/%d" % (capalign, len(pairs)))
    print("  equal row-length multisets           : %d/%d" % (rowmult, len(pairs)))
    print("  chain {i+1,i+2} on 3 weights, no ratio identity used: %d/%d" % (chain_ok, len(pairs)))
    print("  s_Xbar != s_Ybar (proper child)      : %d" % child_sep)
    print("  P_a(G) != 0 for a = 1..7             : %d/%d" % (cap_sep, len(pairs)))

    # ---------------------------------------------------------------- injectivity
    seen = {}
    coll = 0
    for lam, mu in pool:
        if len(lam) < 2:
            continue
        key = (mu, tuple(sorted(S(lam, mu).items())),
               tuple(sorted(S(lam[1:], mu[1:]).items())))
        if key in seen and seen[key] != lam:
            coll += 1
        seen[key] = lam
    assert coll == 0
    print("\nX -> (s_X, s_Xbar) injective at fixed mu: 0 collisions over %d diagrams" % len(seen))

    # ---------------------------------------------------------------- controls
    def report(tag, lam, mu, kap):
        dif = sub(S(tuple(lam), tuple(mu)), S(tuple(kap), tuple(mu)))
        return tag, dif

    # a pair carrying the fingerprint that is NOT equal
    lam, kap, mu = (7, 5, 4), (7, 6, 3), (4, 2, 0)
    cx, dx = cofactors(list(lam), list(mu))
    cy, _ = cofactors(list(kap), list(mu))
    G = [sub(cx[j], cy[j]) for j in range(4)]
    al = [wt(G[j], SQ) + SQ(dx[j]) for j in range(4)]
    dif = sub(S(lam, mu), S(kap, mu))
    assert dif, "control must be unequal"
    assert al[0] > min(al[1:]), "control must carry the antecedent"
    print("CONTROL FIRES  (7,5,4)/(4,2,0) vs (7,6,3)/(4,2,0): shifts %s, alpha %s"
          % (dx, ['inf' if x == INF else x for x in al]))
    print("               antecedent holds and yet s_X - s_Y = %s" % sorted(dif.items()))

    # the 8-cell equal pair of ex:actual-equal-chain
    lam, kap, mu = (4, 4, 3, 3), (4, 4, 4, 2), (3, 2, 1, 0)
    assert S(lam, mu) == S(kap, mu), "the named 8-cell pair must be equal"
    bx, by = (lam[1:], mu[1:]), (kap[1:], mu[1:])
    cbx, dbx = cofactors(list(bx[0]), list(bx[1]))
    cby, _ = cofactors(list(by[0]), list(by[1]))
    Gc = [sub(cbx[j], cby[j]) for j in range(4)]
    assert Gc[0] and not P(Gc, dbx, 1), "child carries P_1(G)=0 with G_0 != 0"
    assert S(*bx) != S(*by)
    print("NAMED PAIR     (4,4,3,3)/(3,2,1,0) = (4,4,4,2)/(3,2,1,0), child shifts %s:" % dbx)
    print("               P_1(child G) = 0 while child G_0 != 0, and the children are unequal")

    # matching overlap partitions, still unequal
    lam, kap, mu = (4, 4, 3, 3, 1), (4, 4, 4, 2, 1), (3, 2, 1, 0, 0)
    dif = sub(S(lam, mu), S(kap, mu))
    assert dif.get((1, 1, 2, 5), 0) == 1, ("overlap control", sorted(dif.items())[:4])
    def overlaps(lam, mu):
        n = len(lam)
        return (sorted((lam[i] - mu[i] for i in range(n)), reverse=True),
                sorted((lam[i + 1] - mu[i] for i in range(n - 1)), reverse=True))
    assert overlaps(lam, mu) == overlaps(kap, mu)
    print("CONTROL FIRES  9-cell U, V share row and column overlap partitions and")
    print("               [h_1^2 h_2 h_5](s_U - s_V) = 1, so overlap data does not recognize equality")

    print("\nALL PASS")


if __name__ == "__main__":
    main()
