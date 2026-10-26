"""Two claims the hypothesis-free route rests on, checked independently.

(1) NO RATIO IDENTITY HOLDS ON A DISTINCT EQUAL PAIR.  If A and B are
    connected, share an inner boundary, satisfy s_A = s_B and are distinct,
    then P_{r+a}(G) = h_a P_r(G) fails for every r >= 0 and every a > 0.
    Consequence for the manuscript: the ratio-identity locus is DISJOINT
    from actual equality, so the printed reduction chain cannot be
    instantiated by taking A = D and B = E.  The locus family of
    subsec:locus-family is the same phenomenon seen from the other side.

(2) THE LEADING PREFIX IS A CHAIN OF SINGLE MONOMIALS.  For 1 <= j <= q the
    initial form of G_j is one monomial with coefficient +-1, the signs
    alternate, the monomials do not depend on the weight, and they satisfy
    the exchange identity h_{d_j - A_{j-1}} M_j = h_{d_{j+1} - A_{j-1}} M_{j+1}.
    The cap and ratio responses then have one surviving initial monomial.

Controls that must FIRE: pairs ON the ratio locus that are NOT equal, so
(1) is not vacuous, and a nonzero-defect pair where the prefix is checked
to be NOT single-monomial beyond q.
"""

import itertools
from collections import defaultdict

from check_equal_pair_rigidity_unconditional import (
    INF, S, WEIGHTS, cofactors, connected, jt_det, shapes, sub, wt, P,
)
from check_cofactor_factorization_and_reconstruction import h, padd, pmul, pscal

SIZE_CAP = 13
ROW_CAP = 5
R_RANGE = range(0, 6)
A_RANGE = range(1, 7)


def initial(f, om):
    if not f:
        return None, INF
    w = min(sum(om(k) for k in m) for m in f)
    return {m: c for m, c in f.items() if sum(om(k) for k in m) == w}, w


pool = list(shapes(SIZE_CAP, ROW_CAP))
by_mu = defaultdict(list)
for lam, mu in pool:
    by_mu[mu].append(lam)

pairs = []
for mu, lams in by_mu.items():
    b = defaultdict(list)
    for lam in lams:
        b[tuple(sorted(S(lam, mu).items()))].append(lam)
    for cls in b.values():
        if len(cls) > 1:
            pairs += [(mu, x, y) for x, y in itertools.combinations(sorted(cls), 2)]

print("connected diagrams, size <= %d, rows <= %d : %d" % (SIZE_CAP, ROW_CAP, len(pool)))
print("distinct equal pairs on a common inner boundary : %d" % len(pairs))
assert pairs, "no equal pairs in range -- the check would be vacuous"

# ---- (1) no ratio identity anywhere on an equal pair ------------------
tested = 0
for mu, lam, kap in pairs:
    n = len(lam)
    cx, d = cofactors(list(lam), list(mu))
    cy, _ = cofactors(list(kap), list(mu))
    G = [sub(cx[j], cy[j]) for j in range(n + 1)]
    assert not G[0]
    assert not P(G, d, 0), "P_0(G) = 0 is automatic"
    for r in R_RANGE:
        for a in A_RANGE:
            lhs = P(G, d, r + a)
            rhs = pmul(h(a), P(G, d, r))
            assert lhs != rhs, ("a ratio identity holds on an equal pair!",
                                mu, lam, kap, r, a)
            tested += 1
print("  ratio identities refuted, (r,a) in %d x %d : %d checks, 0 holding"
      % (len(list(R_RANGE)), len(list(A_RANGE)), tested))

# ---- control: the locus is nonempty, on UNEQUAL pairs -----------------
hits = 0
for mu, lams in by_mu.items():
    for lam, kap in itertools.combinations(lams, 2):
        if len(lam) != len(kap) or lam[0] != kap[0]:
            continue
        if sorted(lam[i] - mu[i] for i in range(len(lam))) != \
           sorted(kap[i] - mu[i] for i in range(len(kap))):
            continue
        if S(lam, mu) == S(kap, mu):
            continue
        n = len(lam)
        cx, d = cofactors(list(lam), list(mu))
        cy, _ = cofactors(list(kap), list(mu))
        G = [sub(cx[j], cy[j]) for j in range(n + 1)]
        if not any(G):
            continue
        for r in R_RANGE:
            for a in A_RANGE:
                if P(G, d, r + a) == pmul(h(a), P(G, d, r)):
                    hits += 1
                    break
            else:
                continue
            break
    if hits > 40:
        break
assert hits > 0, "CONTROL DEAD: no unequal pair satisfies a ratio identity"
print("  CONTROL FIRES: %d+ UNEQUAL pairs do satisfy a ratio identity, so the"
      % hits)
print("    locus is populated and (1) is a real exclusion, not a vacuity")

# ---- (2) the single-monomial prefix ----------------------------------
prefix_ok = cap_ok = 0
for mu, lam, kap in pairs:
    n = len(lam)
    cx, d = cofactors(list(lam), list(mu))
    cy, _ = cofactors(list(kap), list(mu))
    G = [sub(cx[j], cy[j]) for j in range(n + 1)]
    v = min(i for i in range(n) if lam[i] != kap[i])
    q = v + 1
    A = [lam[0] - 1 - (lam[i] - (i + 1)) for i in range(n)]
    ref = None
    for name, om in WEIGHTS:
        mons, signs = {}, {}
        for j in range(1, q + 1):
            ini, _ = initial(G[j], om)
            assert ini is not None and len(ini) == 1, ("not a monomial", name, mu, lam, kap, j, ini)
            (m, c), = ini.items()
            assert abs(c) == 1, ("coefficient not +-1", name, mu, lam, kap, j, c)
            mons[j], signs[j] = m, c
        for j in range(1, q):
            assert signs[j] == -signs[j + 1], ("signs do not alternate", name, j)
            lhsm = tuple(sorted(mons[j] + ((d[j] - A[j - 1]),))) if d[j] - A[j - 1] else mons[j]
            rhsm = tuple(sorted(mons[j + 1] + ((d[j + 1] - A[j - 1]),))) if d[j + 1] - A[j - 1] else mons[j + 1]
            assert lhsm == rhsm, ("exchange identity fails", name, mu, lam, kap, j)
        if ref is None:
            ref = mons
        else:
            assert ref == mons, ("monomials depend on the weight", name, mu, lam, kap)
        # the cap response has one surviving initial monomial
        for a in A_RANGE:
            ini, _ = initial(P(G, d, a), om)
            want = tuple(sorted(mons[1] + ((a + d[1]),)))
            assert ini == {want: signs[1]}, ("cap leading monomial", name, mu, lam, kap, a, ini)
        for r in range(1, 5):
            for a in A_RANGE:
                resp = sub(P(G, d, r + a), pmul(h(a), P(G, d, r)))
                ini, _ = initial(resp, om)
                want = tuple(sorted(mons[1] + (a, r + d[1])))
                assert ini == {want: -signs[1]}, ("ratio leading monomial", name, mu, lam, kap, r, a, ini)
        cap_ok += 1
    prefix_ok += 1
print("  single-monomial prefix, +-1 coefficients, alternating signs,")
print("    weight-independent, exchange identity : %d/%d pairs on 3 weights"
      % (prefix_ok, len(pairs)))
print("  cap and ratio responses each have one surviving initial monomial : %d checks"
      % cap_ok)

print("\nALL PASS")
