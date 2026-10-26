"""Exact checks for balanced four-row wall orientation.

The arithmetic classifier uses the stated coefficient criteria, not equality
sampling.  The selected coefficient is checked by constrained determinant
expansion, independently of its bordered-minor derivation.  No geometric
factorization search or composition engine is used.
"""
from collections import Counter
from functools import lru_cache
from itertools import product, permutations


def betas(rows, gaps):
    n = len(rows)
    assert len(gaps) == n - 1
    assert all(0 < g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps))
    x, y = [0] * n, [0] * n
    x[-1] = rows[-1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return tuple(x), tuple(y)


def data(a, b, c, e, f, p):
    rows = (a + p, a + b + e, b + c + f, c + p)
    gaps = (a, b, c)
    x, y = betas(rows, gaps)
    S = x[0]
    A, B = {t + p for t in x[2:]}, set(y[:-2])
    J = A & B
    return S, p, A - J, B - J, J, rows, gaps


def reflect(S, p, P, Q, J):
    return {S + p - q for q in Q}, {S + p - a for a in P}, {S + p - j for j in J}


def sites(S, p, P, Q, d):
    return {(a, b) for a in {0, p} | P for b in {0, p} | Q if (a - b) % S == d}


def private(S, p, P, Q):
    return any(sites(S, p, P, Q, a) == {(a, 0)} for a in P)


def contact(S, p, P, Q, J):
    assert P == {S + p - b for b in Q}
    W = {(a - b) % S for a in {0, p} | P for b in {0, p} | Q}
    def pairs(Z):
        return Counter(tuple(sorted((t, S - t))) for t in Z)
    lhs, rhs = pairs(J), pairs({S + p - t for t in J})
    return any(lhs[z] != rhs[z] and all(0 < t < S and t not in W for t in z)
               for z in lhs.keys() | rhs.keys())


def q1_core(S, p, P, Q):
    """Private or single-internal-site return criterion for one residual pair."""
    assert len(P) == len(Q) == 1
    Ps, Qs, _ = reflect(S, p, P, Q, set())
    if private(S, p, P, Q) or private(S, p, Ps, Qs):
        return True
    for A, B in ((P, Q), (Ps, Qs)):
        a, b = next(iter(A)), next(iter(B))
        d = a - b
        if not (0 < d < S and sites(S, p, A, B, d) == {(a, b)}):
            continue
        lhs = Counter([tuple(sorted((a, S - b)))])
        rhs = Counter([tuple(sorted((a - p, S + p - b)))])
        W = {0, p, S - p}
        if any(lhs[z] != rhs[z] and all(0 < t < S and t not in W for t in z)
               for z in lhs.keys() | rhs.keys()):
            return True
    return False


def classify(a, b, c, e, f, p):
    S, p, P, Q, J, rows, gaps = data(a, b, c, e, f, p)
    assert S == a + b + c + e + f + 2 * p
    assert J == ({c + 2 * p} if f == p or b + e + f == p else set()) | (
        {b + c + f + 2 * p} if e == p else set())
    if a == c and e == f:
        return 'symmetric'
    if e == f == p:
        return 'constant-excess'
    if len(P) == 2:
        assert not J
        if a != c:
            assert min(P) + max(Q) != S + p
            return 'direct'
        d = a + p
        R = {(u, v) for u in P for v in Q if u - v == d}
        assert sites(S, p, P, Q, d) == {(p + d, p), (0, S - d)} | R
        if b != a:
            assert not R
            A = P - {p + d}
            B = Q - {S - d}
            aa, bb = next(iter(A)), next(iter(B))
            assert aa > bb
            assert aa != S + p - bb
            return 'wrapped'
        assert R == {(2 * a + f + 2 * p, a + f + p)}
        assert e != f and e != p and f != p and a + e + f != p
        return 'wrapped-return'
    assert len(P) == 1
    Ps, Qs, _ = reflect(S, p, P, Q, J)
    if P != Ps:
        assert q1_core(S, p, P, Q), (a, b, c, e, f, p, P, Q, J)
        return 'one-pair-core'
    assert Q == Qs
    assert contact(S, p, P, Q, J), (a, b, c, e, f, p, P, Q, J)
    return 'one-pair-contact'


def core(S, p, P, Q, M, K):
    U = {M * S + p, M * S} | {k * S for k in K} | {j * S + a for j in range(M) for a in P}
    V = {0, p} | {k * S + p for k in K} | {j * S + b for j in range(M) for b in Q}
    assert len(U) == len(V)
    return tuple(sorted(U, reverse=True)), tuple(sorted(V, reverse=True))


def target(X, Y, monomial):
    """Signed determinant coefficient by masks and remaining exponents."""
    labels = tuple(sorted(set(monomial)))
    slots = {x: i for i, x in enumerate(labels)}
    start = tuple(monomial.count(x) for x in labels)
    n = len(X)
    @lru_cache(None)
    def rec(mask, left):
        i = mask.bit_count()
        if i == n:
            return int(not any(left))
        ans = 0
        for j, y in enumerate(Y):
            if mask & (1 << j):
                continue
            d = X[i] - y
            if d < 0 or (d > 0 and d not in slots):
                continue
            rem = list(left)
            if d:
                k = slots[d]
                if rem[k] == 0:
                    continue
                rem[k] -= 1
            ans += (-1) ** ((mask >> (j + 1)).bit_count()) * rec(mask | (1 << j), tuple(rem))
        return ans
    return rec(0, start)


def perm_poly(X, Y):
    out = Counter()
    for perm in permutations(range(len(X))):
        ds = [X[i] - Y[j] for i, j in enumerate(perm)]
        if min(ds, default=0) < 0:
            continue
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(len(X)) for j in range(i + 1, len(X)))
        out[tuple(sorted(d for d in ds if d))] += sign
    return {m: c for m, c in out.items() if c}


def join_power(rows, gaps, m):
    r, g = tuple(rows), tuple(gaps)
    for _ in range(1, m):
        r = r[:-1] + (r[-1] + rows[0],) + rows[1:]
        g += gaps
    return r, g


def composite(rows, gaps, alpha):
    R, G = (), ()
    for m in alpha:
        r, g = join_power(rows, gaps, m)
        if R:
            G += (0,)
        R += r
        G += g
    # betas permits zero gaps here through a separate direct recursion.
    x, y = [0] * len(R), [0] * len(R)
    x[-1] = R[-1]
    for i in range(len(R) - 2, -1, -1):
        y[i] = x[i + 1] - G[i]
        x[i] = y[i] + R[i]
    return tuple(x), tuple(y)


def coefficient_certificate(a, e, f, p, M, T, k):
    """Certificate for the constant-gap two-pair branch; no polynomial input."""
    S, _, P, Q, J, _, _ = data(a, a, a, e, f, p)
    assert not J and e != f and e != p and f != p and a + e + f != p
    assert k in T and M - k not in T
    K = set(range(1, M)) - T
    d = a + p
    N = M + 2 * (len(K) + 1)
    L = {M * S + p} | {t * S + p + d for t in T}
    V = {0} | {t * S - d for t in T}
    # Unique bottom arm of label k*S+p+d.
    assert {(u, v) for u in L for v in V if u - v == k * S + p + d} == {(k * S + p + d, 0)}
    LL = sorted(L - {k * S + p + d})
    VV = sorted(V - {0})
    diag = [u - v for u, v in zip(LL, VV)]
    assert all(t > 0 for t in diag)
    u = 2 * a + f + 2 * p
    z = k * S + p - f
    W = {p % S, (p + d) % S, (p + 2 * d) % S}
    assert u % S not in W | {0, d} and z % S not in W | {0, d}
    assert all(t != d for t in diag)
    assert u != d and z != d
    monomial = tuple(sorted([d] * (N - 1) + [u, z] + diag))
    A, B = core(S, p, P, Q, M, K)
    Ps, Qs, _ = reflect(S, p, P, Q, J)
    AA, BB = core(S, p, Ps, Qs, M, K)
    return (A, B), (AA, BB), monomial


def main():
    counts = Counter(classify(*pars) for pars in product(range(1, 6), repeat=6))
    assert sum(counts.values()) == 5 ** 6
    assert all(counts[k] > 0 for k in ('symmetric', 'constant-excess', 'direct', 'wrapped',
                                    'wrapped-return', 'one-pair-core', 'one-pair-contact'))
    print('ARITHMETIC BOX a,b,c,e,f,p in 1..5:', dict(sorted(counts.items())))
    checks = 0
    samples = ((1, 2, 3, 1), (2, 1, 3, 2), (2, 1, 2, 7), (1, 1, 3, 2),
               (3, 5, 2, 4), (1, 1, 2, 5), (2, 3, 5, 1), (1, 2, 4, 1))
    for a, e, f, p in samples:
        assert classify(a, a, a, e, f, p) == 'wrapped-return'
        for M in range(3, 7):
            for mask in range(1, 1 << (M - 1)):
                T = {i + 1 for i in range(M - 1) if mask & (1 << i)}
                if T == {M - t for t in T}:
                    continue
                k = min(T - {M - t for t in T})
                first, second, mon = coefficient_certificate(a, e, f, p, M, T, k)
                v, w = target(*first, mon), target(*second, mon)
                multiplicity = 2 if f == a + e + p and k > 1 else 1
                assert abs(v) == multiplicity and w == 0, (a, e, f, p, M, T, k, v, w)
                checks += 1
    print('WRAPPED-RETURN exact core separators:', checks)
    first, second, mon = coefficient_certificate(1, 2, 3, 1, 3, {2}, 2)
    full_first, full_second = perm_poly(*first), perm_poly(*second)
    assert full_first.get(mon, 0) == target(*first, mon)
    assert full_second.get(mon, 0) == target(*second, mon) == 0
    assert abs(full_first.get(mon, 0)) == 1
    print('INDEPENDENT full permutation expansions verify the selected nine-row core coefficient.')
    resonant, reflected, mon = coefficient_certificate(1, 2, 4, 1, 3, {2}, 2)
    assert abs(target(*resonant, mon)) == 2 and target(*reflected, mon) == 0
    assert abs(target(*resonant, mon)) != 1
    print('CONTROL: coefficient-one mutation rejected at the multiplicity-two resonance.')
    # Independent full signed permutations: a nonsymmetric parent pair and
    # a symmetric control.  The control rejects dropping nonsymmetry.
    for pars, equal in (((1, 1, 1, 2, 3, 1), False), ((1, 1, 1, 2, 2, 1), True)):
        S, p, P, Q, J, rows, gaps = data(*pars)
        X, Y = composite(rows, gaps, (1, 2))
        XX, YY = composite(rows, gaps, (2, 1))
        # Full parents have eleven rows; use an exact target for their
        # positive separation and use the literal rotation identity for equality.
        if not equal:
            _, _, mon = coefficient_certificate(1, 2, 3, 1, 3, {2}, 2)
            v = target(tuple(x + p for x in X), Y, mon)
            w = target(tuple(x + p for x in XX), YY, mon)
            assert v != w and sorted((abs(v), abs(w))) == [0, 1]
            print('FULL PARENT separating monomial:', mon, 'coefficients:', (v, w))
        else:
            N = max(X) + p
            rotated_x = tuple(sorted((N - y for y in Y), reverse=True))
            rotated_y = tuple(sorted((N - (x + p) for x in X), reverse=True))
            assert rotated_x == tuple(x + p for x in XX) and rotated_y == YY
            # Different nine-row core boards give a full permutation control.
            U, V = core(S, p, P, Q, 3, {1})
            UU, VV = core(S, p, P, Q, 3, {2})
            assert (U, V) != (UU, VV)
            assert perm_poly(U, V) == perm_poly(UU, VV)
            print('CONTROL: symmetric inner and unequal reversed outer words give literal rotated parents.')
    # Determinant checker mutation control on its own coefficient assertion.
    small = ((5, 3), (1, 0))
    pp = perm_poly(*small)
    assert pp[(3, 4)] == 1 and pp[(2, 5)] == -1
    for m, v in pp.items():
        assert target(*small, m) == v
    assert target(*small, (3, 4)) != -pp[(3, 4)]
    print('CONTROL: negating the advertised determinant coefficient is rejected.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
