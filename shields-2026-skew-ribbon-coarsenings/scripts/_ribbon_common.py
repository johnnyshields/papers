r"""Shared exact-arithmetic machinery for the ribbon-coarsening checks.

Everything here is integer or `fractions` arithmetic: the objects are finite
combinatorial sets, and a float anywhere would only be a way to be wrong.  Each
object is built from its definition in the paper and not from a formula the paper
later proves about it, so the identities the section scripts assert are pinned to
the defining objects.

  * a composition is a tuple of positive integers; its cut set is the set of
    proper partial sums (`eq:K`, `sec:algebra`);
  * `coarsenings` enumerates every merge of adjacent parts by choosing which cuts
    to keep, and `inventory` records the sorted results with multiplicity, which
    is `eq:introG` read off directly;
  * an element of \Z[h_1,h_2,...] is a `Counter` from a weakly decreasing tuple to
    an integer coefficient.
"""
import itertools
from collections import Counter
from functools import lru_cache
from math import factorial, gcd


# ----------------------------------------------------------------------
# compositions and cuts
# ----------------------------------------------------------------------

def compositions(n):
    """Every composition of n, as tuples, in a fixed order."""
    for mask in range(1 << (n - 1)):
        parts, run = [], 1
        for i in range(n - 1):
            if mask >> i & 1:
                parts.append(run)
                run = 1
            else:
                run += 1
        parts.append(run)
        yield tuple(parts)


def cuts(a):
    """The cut set S(a): proper partial sums."""
    out, s = [], 0
    for x in a[:-1]:
        s += x
        out.append(s)
    return frozenset(out)


def from_cuts(S, n):
    """The composition of n whose cut set is S (a subset of 1..n-1)."""
    pts = [0] + sorted(S) + [n]
    return tuple(pts[i + 1] - pts[i] for i in range(len(pts) - 1))


def indicator(a):
    """Cut indicator on Z/n as a list b[0..n-1] with b[0] = 0."""
    n = sum(a)
    S = cuts(a)
    return [1 if x in S else 0 for x in range(n)]


def reverse(a):
    return tuple(reversed(a))


def concat(a, b):
    return tuple(a) + tuple(b)


def odot(a, b):
    """Near-concatenation: concatenation with the two meeting parts merged."""
    return tuple(a[:-1]) + (a[-1] + b[0],) + tuple(b[1:])


def near_power(e, j):
    """epsilon^{odot j}."""
    out = tuple(e)
    for _ in range(j - 1):
        out = odot(out, e)
    return out


def circ(alpha, e):
    """alpha o epsilon = epsilon^{odot alpha_1} . ... . epsilon^{odot alpha_l}."""
    out = ()
    for x in alpha:
        out = out + near_power(e, x)
    return out


# ----------------------------------------------------------------------
# inventories (eq:introG)
# ----------------------------------------------------------------------

def coarsenings(a):
    """Yield the sorted-decreasing partition of every coarsening of a, once per
    choice of retained cuts (so with multiplicity)."""
    k = len(a)
    pre = [0]
    for x in a:
        pre.append(pre[-1] + x)
    for mask in range(1 << (k - 1)):
        parts, last = [], 0
        for i in range(1, k):
            if mask >> (i - 1) & 1:
                parts.append(pre[i] - last)
                last = pre[i]
        parts.append(pre[k] - last)
        yield tuple(sorted(parts, reverse=True))


def inventory(a):
    """G_a as a Counter partition -> multiplicity."""
    return Counter(coarsenings(a))


def inventory_key(a):
    return tuple(sorted(inventory(a).items()))


def inv_upto(a, r):
    """The part of G_a of ordinary degree at most r (at most r blocks)."""
    k = len(a)
    pre = [0]
    for x in a:
        pre.append(pre[-1] + x)
    out = Counter()
    for c in range(0, min(r - 1, k - 1) + 1):
        for cs in itertools.combinations(range(1, k), c):
            idx = (0,) + cs + (k,)
            parts = tuple(sorted((pre[j] - pre[i] for i, j in zip(idx, idx[1:])),
                                 reverse=True))
            out[parts] += 1
    return out


def inv_below(a, s):
    """Degrees strictly below s."""
    return inv_upto(a, s - 1)


@lru_cache(maxsize=None)
def all_keys(n):
    """Dict composition -> canonical inventory key, for every composition of n."""
    return {a: inventory_key(a) for a in compositions(n)}


def equivalent(a, b):
    return inventory_key(a) == inventory_key(b)


# ----------------------------------------------------------------------
# multiplicities: the subset DP of eq:subset-dp and the labeled count K_b of eq:K
# ----------------------------------------------------------------------

def multiplicity(cutset, lam):
    """m_beta(lambda) by the subset DP, from the cut set of beta.

    States are the vectors a with 0 <= a_i <= nu_i; this is eq:subset-dp.
    """
    lam = tuple(sorted(lam, reverse=True))
    n = sum(lam)
    vals = sorted(set(lam), reverse=True)
    nu = tuple(lam.count(t) for t in vals)
    memo = {}

    def D(st):
        if not any(st):
            return 1
        if st in memo:
            return memo[st]
        s = sum(x * t for x, t in zip(st, vals))
        eta = 1 if st == nu else (1 if s in cutset else 0)
        if eta == 0:
            memo[st] = 0
            return 0
        tot = 0
        for i, x in enumerate(st):
            if x:
                tot += D(st[:i] + (x - 1,) + st[i + 1:])
        memo[st] = tot
        return tot

    # the cut test is on the partial sum of the SELECTED parts, so the full state
    # (partial sum n) is exempt exactly as in the paper
    assert n >= 1
    return D(nu)


def K_labeled(cutset, labels):
    """K_b(a) of eq:K by the chain DP over the Boolean lattice of labels."""
    r = len(labels)
    full = (1 << r) - 1
    tot_sum = [0] * (1 << r)
    for m in range(1, 1 << r):
        low = m & -m
        tot_sum[m] = tot_sum[m ^ low] + labels[low.bit_length() - 1]
    f = [0] * (1 << r)
    f[0] = 1
    for m in range(1, 1 << r):
        s = 0
        mm = m
        while mm:
            low = mm & -mm
            s += f[m ^ low]
            mm ^= low
        if m == full:
            f[m] = s
        else:
            f[m] = s if tot_sum[m] in cutset else 0
    return f[full]


def K_brute(cutset, labels):
    """K_b(a) straight from eq:K, over permutations."""
    r = len(labels)
    tot = 0
    for p in itertools.permutations(range(r)):
        s, ok = 0, 1
        for j in range(r - 1):
            s += labels[p[j]]
            if s not in cutset:
                ok = 0
                break
        tot += ok
    return tot


def kappa(lam):
    out = 1
    for t in set(lam):
        out *= factorial(lam.count(t))
    return out


# ----------------------------------------------------------------------
# the ring Z[h_1, h_2, ...]
# ----------------------------------------------------------------------

def pmul(F, G):
    out = Counter()
    for m1, c1 in F.items():
        for m2, c2 in G.items():
            out[tuple(sorted(m1 + m2, reverse=True))] += c1 * c2
    return Counter({m: c for m, c in out.items() if c})


def padd(F, G, sign=1):
    out = Counter(F)
    for m, c in G.items():
        out[m] += sign * c
    return Counter({m: c for m, c in out.items() if c})


def psub(F, G):
    return padd(F, G, -1)


def pscale(F, k):
    return Counter({m: k * c for m, c in F.items() if k * c})


def one():
    return Counter({(): 1})


def h(j):
    return one() if j == 0 else Counter({(j,): 1})


def G_poly(a):
    """G_a, with G_empty = 1."""
    if len(a) == 0:
        return one()
    return Counter(inventory(a))


def pderiv(F, j):
    """d/dh_j."""
    out = Counter()
    for m, c in F.items():
        nu = m.count(j)
        if nu:
            lst = list(m)
            lst.remove(j)
            out[tuple(lst)] += c * nu
    return Counter({m: c for m, c in out.items() if c})


def psubst(F, images):
    """The homomorphism h_j -> images(j) applied to F."""
    out = Counter()
    cache = {}
    for m, c in F.items():
        term = one()
        for j in m:
            if j not in cache:
                cache[j] = images(j)
            term = pmul(term, cache[j])
        out = padd(out, pscale(term, c))
    return out


def Psi(e):
    """The substitution homomorphism of eq:introPsi, as a function on polynomials."""
    memo = {}

    def img(j):
        if j not in memo:
            memo[j] = G_poly(near_power(e, j))
        return memo[j]

    return lambda F: psubst(F, img)


def pdegree_part(F, r):
    return Counter({m: c for m, c in F.items() if len(m) == r})


def pmin_degree(F):
    return min((len(m) for m in F), default=None)


def pcontent(F):
    g = 0
    for c in F.values():
        g = gcd(g, c)
    return g


def ptrunc(F, r):
    return Counter({m: c for m, c in F.items() if len(m) <= r})


# ----------------------------------------------------------------------
# literal factors (lem:literal-factor) and factor-reversal orbits
# ----------------------------------------------------------------------

def literal_decomposition(a, p):
    """(delta, epsilon) with a = delta o epsilon and |epsilon| = p, or None.

    The criterion is that of lem:literal-factor: the cuts off the p-grid repeat
    with period p.  The returned pair is then rebuilt and compared with `a`.
    """
    n = sum(a)
    if p < 1 or n % p:
        return None
    S = cuts(a)
    inner = {x for x in S if x < p and x % p}
    for x in S:
        if x % p and (x % p) not in inner:
            return None
    for x in inner:
        for j in range(n // p):
            if (j * p + x) not in S:
                return None
    eps = from_cuts(inner, p)
    delta = from_cuts({x // p for x in S if x % p == 0}, n // p)
    assert circ(delta, eps) == tuple(a), (a, p)
    return delta, eps


def factor_lists(a):
    """Every ordered factor list (delta_1, ..., delta_s) with a = delta_1 o ... o delta_s."""
    out = [(tuple(a),)]
    n = sum(a)
    for p in range(1, n):
        if n % p == 0:
            dec = literal_decomposition(a, p)
            if dec is not None and p > 1:
                delta, eps = dec
                for lst in factor_lists(delta):
                    out.append(lst + (eps,))
    return out


def compose_all(lst):
    out = lst[0]
    for f in lst[1:]:
        out = circ(out, f)
    return out


@lru_cache(maxsize=None)
def factor_reversal_orbit(a):
    """The set of compositions delta_1^{+-} o ... o delta_s^{+-} over all factorizations of a."""
    orbit = set()
    for lst in factor_lists(a):
        for signs in itertools.product((0, 1), repeat=len(lst)):
            choice = [f[::-1] if sg else f for f, sg in zip(lst, signs)]
            orbit.add(compose_all(choice))
    return frozenset(orbit)


# ----------------------------------------------------------------------
# arithmetic helpers
# ----------------------------------------------------------------------

def Omega(n):
    c, d = 0, 2
    while n > 1:
        while n % d == 0:
            n //= d
            c += 1
        d += 1
        if d * d > n and n > 1:
            c += 1
            break
    return c


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def nu2(n):
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c


# ----------------------------------------------------------------------
# a second route to inventories: dynamic programming over (closed blocks, open block)
# ----------------------------------------------------------------------

def _insert_sorted(closed, x):
    lst = list(closed)
    lst.append(x)
    lst.sort(reverse=True)
    return tuple(lst)


def inventory_dp(a, maxblocks=None):
    """G_a, or its part of ordinary degree <= maxblocks, by a DP whose state is the
    multiset of closed blocks together with the open block's running sum.  Independent
    of `coarsenings` (which enumerates retained-cut subsets), and fast enough for
    weight 16.  Returns a Counter partition -> multiplicity."""
    states = {((), a[0]): 1}
    for x in a[1:]:
        nxt = {}
        for (closed, openb), cnt in states.items():
            k = (closed, openb + x)
            nxt[k] = nxt.get(k, 0) + cnt
            if maxblocks is None or len(closed) + 2 <= maxblocks:
                k = (_insert_sorted(closed, openb), x)
                nxt[k] = nxt.get(k, 0) + cnt
        states = nxt
    out = Counter()
    for (closed, openb), cnt in states.items():
        if maxblocks is None or len(closed) + 1 <= maxblocks:
            out[_insert_sorted(closed, openb)] += cnt
    return out


def inventory_key_dp(a):
    return tuple(sorted(inventory_dp(a).items()))


def first_diff_degree(F, G):
    """Least ordinary degree (number of blocks) at which two polynomials differ, or None."""
    degs = sorted({len(m) for m in set(F) | set(G) if F.get(m, 0) != G.get(m, 0)})
    return degs[0] if degs else None
