"""Guards for the printed statements listed below.

Guards, in the order they appear in the paper:

  * ex:actual-equal-chain -- the worked equal pair, every printed number;
  * eq:largest-index -- the largest generator index actually occurring, and
    that it forces lambda_0 = kappa_0 through one row extension, which is what
    cor:two-positive-extensions runs on;
  * the priority paragraph after eq:cofactor-initial -- that a dominance-minimal
    monomial already minimizes every admissible convex weight, so minimality
    "for an arbitrary convex weight" is the WEAKER statement (Karamata);
  * eq:radix-weight -- the first increment is B, not B - B^0;
  * cor:unique-ratio -- at most one ratio identity in the whole (r,a) plane;
  * cor:two-positive-extensions -- two distinct positive extensions determine
    the parent;
  * subsec:floor-margin -- the in-class witness with alpha_0 = m_+ and its
    exact k^2 dilation family;
  * prop:caterpillar -- that the feasibility hypothesis A_t <= d_t is needed:
    strictly increasing A and d alone let every maximal minor vanish.

Exact integer arithmetic throughout.
"""

import itertools
import sys
from collections import defaultdict

from check_equal_pair_rigidity_unconditional import (
    INF, S, cofactors, connected, jt_det, shapes, sub, wt, P,
)
from check_cofactor_factorization_and_reconstruction import det, h, pmul, pscal

SQ = lambda k: k * k
CU = lambda k: k ** 3
RX = lambda k: 0 if k == 0 else 7 ** k


def defect(lam, mu, kap):
    n = len(lam)
    cx, d = cofactors(list(lam), list(mu))
    cy, _ = cofactors(list(kap), list(mu))
    return [sub(cx[j], cy[j]) for j in range(n + 1)], d


def alpha(G, d, om):
    return [wt(G[j], om) + om(d[j]) for j in range(len(G))]


def mons(f):
    return sorted(f.items())


# ---- ex:actual-equal-chain -------------------------------------------
lam, kap, mu = (4, 4, 4, 2), (4, 4, 3, 3), (3, 2, 1, 0)
assert S(lam, mu) == S(kap, mu)
G, d = defect(lam, mu, kap)
assert d == [0, 1, 3, 5, 7], d
A = [lam[0] - 1 - (lam[i] - (i + 1)) for i in range(4)]
Ak = [kap[0] - 1 - (kap[i] - (i + 1)) for i in range(4)]
assert A == [0, 1, 2, 5] and Ak == [0, 1, 3, 4], (A, Ak)
assert not G[0] and not G[4]
assert mons(G[1]) == [((2, 5), 1), ((3, 4), -1)]
assert mons(G[2]) == [((1, 4), 1), ((5,), -1)]
assert mons(G[3]) == [((1, 2), -1), ((3,), 1)]
al = alpha(G, d, SQ)
assert al == [INF, 26, 26, 30, INF], al
# the two common-row relations printed in the example
rel1 = {}
for c, g in ((1, G[1]), (3, G[2]), (5, G[3])):
    rel1 = sub(rel1, pscal(-1, pmul(h(c), g)))
rel2 = {}
for c, g in ((0, G[1]), (2, G[2]), (4, G[3])):
    rel2 = sub(rel2, pscal(-1, pmul(h(c), g)))
assert not rel1 and not rel2
v = 2
for i in range(v):
    F = {j: wt(G[j], SQ) + SQ(d[j] - A[i]) for j in range(5) if G[j]}
    lo = min(F.values())
    assert sorted(j for j in F if F[j] == lo) == [i + 1, i + 2]
assert mons(sub(S(lam[1:], mu[1:]), S(kap[1:], mu[1:]))) == [((2, 5), -1), ((3, 4), 1)]
print("ex:actual-equal-chain  every printed number exact, both relations vanish")

# ---- eq:largest-index and the extension identity ---------------------
def extend(lam, mu, a):
    return (lam[0] + a - 1,) + tuple(lam), (lam[0] - 1,) + tuple(mu)


def H(lam, mu):
    return lam[0] - mu[len(lam) - 1] + len(lam) - 1


checked = 0
for lm, m in shapes(10, 4):
    f = jt_det(list(lm), list(m))
    top = max(max(mm) for mm in f)
    assert top == H(lm, m), (lm, m, top, H(lm, m))
    for a in (1, 2, 3):
        lx, mx = extend(lm, m, a)
        assert connected(list(lx), list(mx))
        assert H(lx, mx) == lm[0] + a - 1 - m[len(lm) - 1] + len(lm)
        checked += 1
print("eq:largest-index       largest OCCURRING index = H on every diagram; the")
print("                       extension formula holds on %d instances" % checked)

# ---- Karamata: dominance-minimal already minimizes every convex weight
def dom_le(a, b):
    a, b = sorted(a, reverse=True), sorted(b, reverse=True)
    n = max(len(a), len(b))
    a, b = a + [0] * (n - len(a)), b + [0] * (n - len(b))
    return sum(a) == sum(b) and all(sum(a[:k]) <= sum(b[:k]) for k in range(1, n + 1))


beaten = tested = 0
for lm, m in shapes(10, 4):
    ms = list(jt_det(list(lm), list(m)))
    cand = [x for x in ms if all(dom_le(x, o) for o in ms)]
    assert len(cand) == 1, (lm, m)
    tested += 1
    for om in (SQ, CU, RX):
        w = lambda x: sum(om(k) for k in x)
        if any(w(o) < w(cand[0]) for o in ms):
            beaten += 1
assert beaten == 0
print("Karamata               dominance-minimal monomial minimizes square, cubic")
print("                       and radix weight on all %d diagrams, 0 exceptions" % tested)

# ---- eq:radix-weight -------------------------------------------------
for B in (2, 3, 4, 7):
    om = lambda k, B=B: 0 if k == 0 else B ** k
    inc = [om(k) - om(k - 1) for k in range(1, 6)]
    assert inc[0] == B and inc[0] != B - B ** 0
    assert all(inc[k] == B ** (k + 1) - B ** k for k in range(1, 5))
    strict = all(inc[k] < inc[k + 1] for k in range(4))
    assert strict == (B >= 3), (B, inc)
print("eq:radix-weight        first increment is B (not B-1); strict convexity")
print("                       holds exactly for B >= 3, with B = 2 the control")

# ---- cor:unique-ratio ------------------------------------------------
plane = [(r, a) for r in range(0, 5) for a in range(1, 5)]
multi = 0
one = 0
tested = 0
for mu, lams in ((m, [l for l, mm in shapes(12, 4) if mm == m])
                 for m in {mm for _, mm in shapes(12, 4)}):
    for lam, kap in itertools.combinations(lams, 2):
        if len(lam) != len(kap) or lam[0] != kap[0]:
            continue
        n = len(lam)
        if sorted(lam[i] - mu[i] for i in range(n)) != sorted(kap[i] - mu[i] for i in range(n)):
            continue
        G, d = defect(lam, mu, kap)
        if not any(G):
            continue
        tested += 1
        ids = [(r, a) for (r, a) in plane if P(G, d, r + a) == pmul(h(a), P(G, d, r))]
        if len(ids) > 1:
            multi += 1
        if len(ids) == 1:
            one += 1
assert multi == 0 and one > 0
print("cor:unique-ratio       %d nonzero defects: %d carry exactly one identity," % (tested, one))
print("                       0 carry two -- and the control is that %d do carry one" % one)

# ---- cor:two-positive-extensions -------------------------------------
seen, coll = {}, 0
for lm, m in shapes(11, 4):
    lx, mx = extend(lm, m, 1)
    ly, my = extend(lm, m, 2)
    key = (m, len(lm), tuple(sorted(S(lx, mx).items())), tuple(sorted(S(ly, my).items())))
    if key in seen and seen[key] != lm:
        coll += 1
    seen[key] = lm
assert coll == 0
print("cor:two-positive-extensions:  (a,b) = (1,2): 0 collisions over %d diagrams" % len(seen))

# ---- subsec:floor-margin --------------------------------------------
for k in range(1, 6):
    mk = (3 * k - 2, 2 * k - 1, 0)
    Ak_, Bk = (6 * k - 2, 5 * k - 1, 2 * k), (6 * k - 2, 4 * k - 1, 3 * k)
    assert connected(list(Ak_), list(mk)) and connected(list(Bk), list(mk))
    assert sorted(Ak_[i] - mk[i] for i in range(3)) == sorted(Bk[i] - mk[i] for i in range(3))
    G, d = defect(Ak_, mk, Bk)
    assert d == [0, 3 * k, 4 * k, 6 * k], (k, d)
    al = alpha(G, d, SQ)
    assert al == [k * k * x for x in (24, 26, 24, 38)], (k, al)
    mp = min(al[1:])
    assert al[0] == mp
    supp = [d[j] for j in range(1, 4) if G[j]]
    T0 = [d[j] for j in range(1, 4) if al[j] == mp]
    assert min(supp) == 3 * k and T0 == [4 * k], (k, supp, T0)
    assert min(supp) not in T0
print("subsec:floor-margin    alpha = k^2 (24,26,24,38) exactly for k = 1..5, with")
print("                       alpha_0 = m_+, leftmost supported shift 3k, T_0^+ = {4k}")

# ---- prop:caterpillar needs its feasibility hypothesis ---------------
A_bad, d_bad = [0, 5, 9], [0, 1, 2, 3, 4]
assert all(A_bad[i] < A_bad[i + 1] for i in range(2))
assert all(d_bad[j] < d_bad[j + 1] for j in range(4))
vanish = 0
for i, j in itertools.combinations(range(5), 2):
    cols = [c for c in range(5) if c not in (i, j)]
    if not det([[h(d_bad[c] - A_bad[r]) for c in cols] for r in range(3)]):
        vanish += 1
assert vanish == 10
A_ok, d_ok = [0, 1, 2], [0, 1, 2, 3, 4]
assert all(A_ok[t] <= d_ok[t] for t in range(3))
alive = 0
for i, j in itertools.combinations(range(5), 2):
    cols = [c for c in range(5) if c not in (i, j)]
    if det([[h(d_ok[c] - A_ok[r]) for c in cols] for r in range(3)]):
        alive += 1
assert alive == 10
print("prop:caterpillar       strictly increasing A and d alone: all 10 maximal")
print("                       minors vanish; under A_t <= d_t all 10 are nonzero")

print("\nALL PASS")
