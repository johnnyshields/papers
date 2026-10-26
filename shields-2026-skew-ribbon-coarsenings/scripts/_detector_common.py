r"""Normalized cut-function pairs, drawn from their parametrization.

`sec:detector` and `sec:realization` argue about a pair of cut indicators `b, c` on
`Z/n` in the normalized setting of `prop:normalization`: `c` agrees with the
reflection of `b` off the `d`-grid (so `u = w` there, `v = 0`), `c(x) = b(-x)` on
the `d`-grid (so `u = 0`, `v = b - b(-.)`), and the masks `B_p` of `eq:mask` satisfy
the divisibility chain of `eq:chain`.

A sampler that draws pairs of compositions and reports a margin reports a fact
about the sampler.  The admissible set here has a free parametrization, so the pair
is built from it and then the defining equations are re-checked on the built object
(`audit_setup`), which is what makes the extreme configurations reachable by
construction.

The free data, layer by layer (layers are the sets `p_j Z \ p_{j+1} Z`):
  * `w`, an odd ternary `e`-periodic function vanishing on `eZ`, not identically 0;
  * off the `e`-grid, `b` is `p_1`-periodic with `b(x) - b(-x) = w(x)`;
  * in layer `j <= L-2`, `b` is even and `p_{j+2}`-periodic;
  * in layers `L-1`, `L` (up to the `d`-grid), `b` is even and otherwise free;
  * on the `d`-grid `b` is free, and `c` is its reflection.
"""
import random
from math import gcd

from _ribbon_common import K_labeled, cuts


class Setup:
    pass


def make_setup(n, e, chain, d, rng, free=False):
    """chain = [p_0 = e, p_1, ..., p_L = P].  free=True drops the chain periodicity
    (only the oddness `b(x) - b(-x) = w(x)` is kept off the d-grid)."""
    assert d % chain[-1] == 0 and n % d == 0 and chain[0] == e and d % e == 0
    L = len(chain) - 1
    p1 = chain[1] if L >= 1 else d
    # the odd ternary e-periodic w, zero on multiples of e
    while True:
        wres = [0] * e
        for r in range(1, e // 2 + (e % 2)):
            if 2 * r != e:
                v = rng.choice((-1, 0, 1))
                wres[r], wres[e - r] = v, -v
        if any(wres):
            break
    w = [wres[x % e] for x in range(n)]
    b = [0] * n
    # off the e-grid: p_1-periodic
    f0 = {}
    for rho in range(1, p1):
        if rho % e == 0 or rho in f0:
            continue
        rho2 = (-rho) % p1
        wv = wres[rho % e]
        if wv == 1:
            f0[rho], f0[rho2] = 1, 0
        elif wv == -1:
            f0[rho], f0[rho2] = 0, 1
        else:
            val = rng.randint(0, 1)
            f0[rho] = f0[rho2] = val
    layer_g = {}
    free_g = {}
    for x in range(1, n):
        if x % d == 0:
            continue
        if x % e:
            b[x] = 0 if free else f0[x % p1]
            continue
        # x is a multiple of e: layer j with p_j | x, p_{j+1} does not divide x
        j = 0
        while j < L and x % chain[j + 1] == 0:
            j += 1
        if not free and j <= L - 2:
            m = chain[j + 2]
            rho = x % m
            key = (j, min(rho, (-rho) % m))
            if key not in layer_g:
                layer_g[key] = rng.randint(0, 1)
            b[x] = layer_g[key]
        else:
            key = min(x, n - x)
            if key not in free_g:
                free_g[key] = rng.randint(0, 1)
            b[x] = free_g[key]
    if free:
        # a free off-grid b: decide each opposite pair independently
        done = set()
        for x in range(1, n):
            if x % d == 0 or x in done:
                continue
            y = (-x) % n
            wv = w[x]
            if wv == 1:
                b[x], b[y] = 1, 0
            elif wv == -1:
                b[x], b[y] = 0, 1
            else:
                val = rng.randint(0, 1)
                b[x] = b[y] = val
            done.add(x)
            done.add(y)
    # the d-grid: b free, c its reflection
    dg = [x for x in range(d, n, d)]
    for x in dg:
        y = (-x) % n
        if y < x:
            continue
        if x == y:
            b[x] = rng.randint(0, 1)
        else:
            b[x], b[y] = rng.randint(0, 1), rng.randint(0, 1)
    c = list(b)
    for x in dg:
        c[x] = b[(-x) % n]
    S = Setup()
    S.n, S.e, S.chain, S.d, S.L = n, e, list(chain), d, L
    S.w, S.b, S.c = w, b, c
    S.Sb = frozenset(x for x in range(1, n) if b[x])
    S.Sc = frozenset(x for x in range(1, n) if c[x])
    S.u = [b[x] - c[(-x) % n] for x in range(n)]
    S.v = [b[x] - c[x] for x in range(n)]
    S.tau = [b[x] + b[(-x) % n] for x in range(n)]
    return S


def audit_setup(S):
    """Re-derive the defining properties of the normalized setting from the built object."""
    n, e, d, L, chain = S.n, S.e, S.d, S.L, S.chain
    b, c, u, v, w = S.b, S.c, S.u, S.v, S.w
    assert all(x in (0, 1) for x in b) and all(x in (0, 1) for x in c) and b[0] == 0 == c[0]
    assert all(u[x] == -u[(-x) % n] and v[x] == -v[(-x) % n] for x in range(n))      # odd
    assert all(u[x] * v[x] == 0 for x in range(n))                                   # disjoint
    assert all(abs(u[x]) <= 1 and abs(v[x]) <= 1 for x in range(n))
    assert all(v[x] == 0 for x in range(n) if x % d)                                 # v lives on the d-grid
    assert all(u[x] == w[x] for x in range(n) if x % d)                              # u = w off the grid
    assert all(w[(x + e) % n] == w[x] for x in range(n)) and any(w)
    assert all(w[x] == 0 for x in range(0, n, e)) and all(w[x] == -w[(-x) % n] for x in range(n))
    assert all(S.tau[x] == c[x] + c[(-x) % n] for x in range(n))                     # two-block data
    for p in range(e, d + 1):
        if d % p or p % e:
            continue
        B = mask(S, p)
        assert all(B[x] - B[(-x) % n] == w[x] for x in range(n))                     # eq:mask-odd
    if not getattr(S, 'free', False) and L >= 1:
        for i in range(L):
            B = mask(S, chain[i])
            assert all(B[(x + chain[i + 1]) % n] == B[x] for x in range(n)), (i, chain)   # eq:chain


def mask(S, p):
    return [0 if x % p == 0 else S.b[x] for x in range(S.n)]


def least_period(f, n):
    for p in range(1, n + 1):
        if n % p == 0 and all(f[(x + p) % n] == f[x] for x in range(n)):
            return p


def K_pair(S, labels):
    return K_labeled(S.Sb, labels) - K_labeled(S.Sc, labels)


def theta_i(S, i, y_i, y_ip1):
    B = mask(S, S.chain[i + 1])
    n = S.n
    return B[(y_i + y_ip1) % n] - B[y_i % n]


def f_y(S, y, x):
    B = mask(S, S.e)
    n = S.n
    return B[(x + y) % n] - B[x % n]


def H(S, y, r, s, z):
    w = S.w
    f = lambda x: f_y(S, y, x)
    return (f(r) * (w[s % S.n] + w[z % S.n]) + f(s) * (w[r % S.n] + w[z % S.n])
            + f(z) * (w[r % S.n] + w[s % S.n]))


def supp_v_reps(S):
    return [x for x in range(1, S.n) if S.v[x]]


# configurations used across the detector and realization sweeps: (n, e, chain, d)
CONFIGS = [
    (30, 5, [5, 10], 10),
    (36, 3, [3, 6], 6),
    (48, 4, [4, 12], 12),
    (60, 5, [5, 10], 20),
    (72, 4, [4, 12, 24], 24),
    (60, 5, [5, 10, 20], 20),
    (96, 4, [4, 8, 24], 24),
    (120, 5, [5, 10, 30], 30),
    (144, 3, [3, 6, 12, 24], 24),
]


def sample_list(S, rng, tries=4000):
    """A positive labeled list of the form of eq:detector-list with total n, layers per
    eq:layers, or None."""
    n, e, L, chain = S.n, S.e, S.L, S.chain
    reps = supp_v_reps(S)
    if not reps:
        return None
    for _ in range(tries):
        a = rng.choice(reps)
        ys = []
        for i in range(L):
            cand = [x for x in range(1, n) if x % chain[i] == 0 and x % chain[i + 1]]
            ys.append(rng.choice(cand))
        r = rng.randint(1, n - 1)
        s = rng.randint(1, n - 1)
        z = n - a - sum(ys) - r - s
        if z < 1 or r % e == 0 or s % e == 0 or z % e == 0:
            continue
        return a, ys, r, s, z
    return None


def make_setup_v(n, e, chain, d, rng, free=False):
    """make_setup, resampled until v is not identically zero (the normalization of
    prop:normalization excludes the case where the originals coincide or reverse)."""
    assert n // d >= 3 and n % d == 0, "prop:normalization requires n/d >= 3 (basic-periods)"
    for _ in range(2000):
        S = make_setup(n, e, chain, d, rng, free=free)
        if supp_v_reps(S):
            S.free = free
            audit_setup(S)
            return S
    raise AssertionError(f"no normalized pair with nonzero v found for {(n, e, chain, d)}")


# ----------------------------------------------------------------------
# probes of lem:selection, and the normalized setting of a real pair
# ----------------------------------------------------------------------

def search_probes(S, t, chain):
    """Probes of lem:selection by exhaustive search under the bounds of eq:probe-bounds.
    `chain` is the list of least periods p_0..p_L; returns ([y_0..y_{L-1}], (r, s, z))
    or None."""
    n, e, L = S.n, S.e, len(chain) - 1
    ys = [None] * L
    ys[L - 1] = t
    probe = S.__class__()
    probe.__dict__.update(S.__dict__)
    probe.chain = list(chain)

    def rec(i):
        if i < 0:
            return bottom()
        for y in range(1, chain[i + 2] if i + 2 <= L else n):
            if y % chain[i] or (y % chain[i + 1] == 0):
                continue
            if theta_i(probe, i, y, ys[i + 1]) == 0:
                continue
            ys[i] = y
            got = rec(i - 1)
            if got:
                return got
        return None

    def bottom():
        y0 = ys[0]
        p1 = chain[1]
        for r in range(1, p1):
            if r % e == 0:
                continue
            for s in range(1, p1):
                if s % e == 0:
                    continue
                for z in range(1, p1):
                    if z % e == 0:
                        continue
                    if (sum(ys) + r + s + z) % p1:
                        continue
                    if H(S, y0, r, s, z) != 0:
                        return list(ys), (r, s, z)
        return None

    return rec(L - 2)


def least_period_chain(S):
    """[p_0 = e, p_1, ..., p_L] as least periods of the successive masks, or None if
    the built chain is not a chain of least periods."""
    ch = [S.e]
    for i in range(S.L):
        ch.append(least_period(mask(S, ch[-1]), S.n))
    return ch if ch == S.chain else None


def setup_from_pair(A, B):
    """The normalized setting of prop:normalization for two compositions of one weight
    with equal three-block data, or None when they coincide or are reversals.  The
    second composition is replaced by its reversal when that is what brings
    g_u properly inside d."""
    from math import gcd
    from _ribbon_common import indicator, reverse
    n = sum(A)
    b = indicator(A)
    for gam in (B, reverse(B)):
        c = indicator(gam)
        u = [b[x] - c[(-x) % n] for x in range(n)]
        v = [b[x] - c[x] for x in range(n)]
        if not any(u) or not any(v):
            continue
        gu, d = n, n
        for x in range(1, n):
            if u[x]:
                gu = gcd(gu, x)
            if v[x]:
                d = gcd(d, x)
        if not (gu < d and d % gu == 0):
            continue
        S = Setup()
        S.n, S.d = n, d
        S.w = [u[x] if x % d else 0 for x in range(n)]
        S.e = least_period(S.w, n)
        S.b, S.c, S.u, S.v = b, c, u, v
        S.Sb = frozenset(x for x in range(1, n) if b[x])
        S.Sc = frozenset(x for x in range(1, n) if c[x])
        S.tau = [b[x] + b[(-x) % n] for x in range(n)]
        S.gamma = gam
        chain = [S.e]
        while True:
            p = least_period(mask(S, chain[-1]), n)
            if p == chain[-1]:
                break
            chain.append(p)
        S.chain, S.L = chain, len(chain) - 1
        return S
    return None
