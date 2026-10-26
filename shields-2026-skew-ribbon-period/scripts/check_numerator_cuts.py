r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Singleton cuts of the chain numerators (`lem:conormal-caps`, `app:aligned`).

Claim.  Let P be a profile (xi, zeta) with label height one at q-1 and at xi_0 - q, and let
G_1 < ... < G_e be blocks of its proper matrix (blocks between separated cuts) each of top label
d_G = xi_{s+1} - zeta_e >= q and each with label height one at q-1 and d_G - q.  Then the first,
middle and last numerators of the chain (rows/columns of `first_numerator_profile`,
`mid_numerator_profile`, `last_numerator_profile`) are profiles of label height one at q-1 and at
their top label minus q.

The script enumerates random small profiles, every subset of qualifying blocks, and asserts the
claim; it also asserts that the instances exercised are not vacuous.
"""
import itertools
import random
import sys

random.seed(7)


def height(xs, zs, k):
    return sum(1 for z in zs if z <= k) - sum(1 for x in xs if x <= k)


def is_profile(xs, zs):
    m = len(xs)
    if len(zs) != m or zs[-1] != 0 or xs[-1] <= 0:
        return False
    if any(xs[i] <= xs[i + 1] for i in range(m - 1)):
        return False
    if any(zs[i] <= zs[i + 1] for i in range(m - 1)):
        return False
    if any(zs[i] > xs[i + 1] for i in range(m - 1)):
        return False
    return all(height(xs, zs, k) > 0 for k in range(0, xs[0]))


def rand_profile(n):
    top = random.randint(3, 16)
    if top - 1 < n:
        return None
    xs = [top] + sorted(random.sample(range(1, top), n), reverse=True)
    zs = sorted(random.sample(range(1, top), n), reverse=True) + [0]
    return (xs, zs) if is_profile(xs, zs) else None


def separated(xs, zs, n, k):
    I = xs[1:]
    C = zs[:n]
    return all(I[i] < C[j] for i in range(k, n) for j in range(k))


def blocks(xs, zs, n):
    cuts = [k for k in range(n + 1) if separated(xs, zs, n, k)]
    return [(cuts[i], cuts[i + 1] - 1) for i in range(len(cuts) - 1)]


def sub_profile(xs, zs, rows, cols):
    c = zs[cols[-1]]
    return [xs[a] - c for a in rows], [zs[b] - c for b in cols]


def cuts_ok(xs, zs, q):
    return height(xs, zs, q - 1) == 1 and height(xs, zs, xs[0] - q) == 1


checked = {"first": 0, "mid": 0, "last": 0, "zNe_ge_q": 0}
for trial in range(400000):
    n = random.randint(2, 7)
    P = rand_profile(n)
    if P is None:
        continue
    xs, zs = P
    q = random.randint(2, 4)
    if xs[0] < 2 * q or not cuts_ok(xs, zs, q):
        continue
    good = []
    for (s, e) in blocks(xs, zs, n):
        bx = [xs[a] for a in range(s + 1, e + 2)]
        bz = [zs[b] for b in range(s, e + 1)]
        c = bz[-1]
        bx = [x - c for x in bx]
        bz = [z - c for z in bz]
        if is_profile(bx, bz) and bx[0] >= q and cuts_ok(bx, bz, q):
            good.append((s, e))
            # the last column of a qualifying block is at least q (needed so that the removed
            # column is uncounted at the bottom cut of the last numerator)
            assert zs[e] >= q or e == n, ("zN e < q", xs, zs, q, s, e)
            checked["zNe_ge_q"] += 1
    for r in range(1, len(good) + 1):
        for L in itertools.combinations(good, r):
            # first numerator
            s1, e1 = L[0]
            rows = [a for a in range(0, e1 + 2) if a != s1 + 1]
            cols = list(range(0, e1 + 1))
            nx, nz = sub_profile(xs, zs, rows, cols)
            assert is_profile(nx, nz)
            assert cuts_ok(nx, nz, q), ("first", xs, zs, q, L)
            checked["first"] += 1
            for (s, e), (s2, e2) in zip(L, L[1:]):
                rows = [a for a in range(s + 1, e2 + 2) if a != s2 + 1]
                cols = [b for b in range(s, e2 + 1) if b != e]
                nx, nz = sub_profile(xs, zs, rows, cols)
                assert is_profile(nx, nz)
                assert cuts_ok(nx, nz, q), ("mid", xs, zs, q, L)
                checked["mid"] += 1
            s, e = L[-1]
            rows = list(range(s + 1, n + 1))
            cols = [b for b in range(s, n + 1) if b != e]
            nx, nz = sub_profile(xs, zs, rows, cols)
            assert is_profile(nx, nz)
            assert cuts_ok(nx, nz, q), ("last", xs, zs, q, L)
            checked["last"] += 1
print(checked)
assert all(v >= 20 for v in checked.values()), "vacuous"
print("PASS")
