#!/usr/bin/env python3
"""Scalar dual-period identities and nonvanishing, for arbitrary integer data.

Paper sections `sec:dual` (Cyclic inventories and original coefficients),
`sec:one-active` and `sec:strengthening`; targets `lem:dual-identities`,
`thm:dual-period`, `thm:dual-general`, `cor:automatic-open`, `lem:positive-support`,
`lem:two-support`, `cor:one-positive-short`, and the parity step of
`thm:pure-primitive-first`.

Data are integers b > d >= 1 and r >= 1 with no coprimality, the positive remainder
convention b = k d + s with 1 <= s <= d, and an arbitrary cyclic word P of length
n = r d over at most three response classes.  Response values are exact rationals;
active classes carry S_alpha = S_* - alpha F with distinct integer labels, inactive
classes arbitrary nonzero values.  Window sums are enumerated by start.

Asserted: the counts sum to d; d | b gives at most one active class; the three dual
identities for every word and value assignment; the gcd reparametrization divides every
N_j by g; with two or more active classes N_n and Phi_B never vanish together at any
sampled point; the automatic identity Phi_B = 0 at r = 1, b = 1 mod d; the AM-GM
inequality of lem:positive-support with its equality case; the strict positivity of
Phi_B with exactly one positive active exponent (distinct response values), with the two displayed lower-bound chains evaluated in
mpmath.  Controls that must fire: one active class can have N_n = Phi_B = 0, and
two active classes sharing a label can as well.
"""
from collections import Counter
from fractions import Fraction as Fr
from itertools import product
from math import gcd
import random
import mpmath as mp

mp.mp.dps = 60
CLASSES = 3


def window_inverse(word, j, S):
    size = len(word)
    total = Fr(0)
    for i in range(size):
        prod = Fr(1)
        for a in range(j):
            prod *= S[word[(i+a) % size]]
        total += 1/prod
    return total


def window_forward(word, j, S):
    size = len(word)
    total = Fr(0)
    for i in range(size):
        prod = Fr(1)
        for a in range(j):
            prod *= S[word[(i+a) % size]]
        total += prod
    return total


def data(b, d, r, P):
    k, s = divmod(b, d)
    if s == 0:
        k, s = k-1, d
    n, B, m = r*d, r*b, r*s
    assert 1 <= s <= d and len(P) == n and b == k*d+s
    R = P[:m-1]
    word = P*k+R
    assert len(word) == B-1
    c, t = Counter(P), Counter(R)
    e = {x: s*c[x]-d*t[x] for x in range(CLASSES)}
    assert sum(e.values()) == d
    return k, s, n, B, m, R, word, e


def values_for(e, rng, labels=None):
    """Active classes lie on one line S = S_* - alpha F; inactive ones are free."""
    active = [x for x in range(CLASSES) if e[x]]
    anchor, F = Fr(rng.randint(1, 40), rng.randint(1, 9)), Fr(rng.randint(1, 30), rng.randint(1, 9))
    if rng.random() < 0.5:
        F = -F
    alphas = labels or rng.sample(range(-4, 6), len(active))
    S = {}
    for x in range(CLASSES):
        if e[x]:
            S[x] = anchor-alphas[active.index(x)]*F
        else:
            S[x] = Fr(rng.randint(1, 50), rng.randint(1, 9)) * rng.choice((1, -1))
    return S, active


def N(j, b, e, P, word, S):
    return b*window_inverse(P, j, S)-sum(e[x]*window_inverse(word+(x,), j, S) for x in range(CLASSES))


def words(n):
    seen = set()
    for w in product(range(CLASSES), repeat=n):
        order = []
        for x in w:
            if x not in order:
                order.append(x)
        key = tuple(order.index(x) for x in w)
        if key not in seen:
            seen.add(key)
            yield key


def identities_and_nonvanishing(counts):
    rng = random.Random(20260101)
    for b in range(3, 9):
        for d in range(1, b):
            for r in (1, 2):
                n = r*d
                if n > 6:
                    continue
                for P in words(n):
                    k, s, n, B, m, R, word, e = data(b, d, r, P)
                    active = [x for x in range(CLASSES) if e[x]]
                    if b % d == 0:
                        assert s == d and m == n and R == P[:-1]
                        assert len(active) <= 1
                        assert all(e[x] == (d if x == P[-1] else 0) for x in range(CLASSES))
                        counts['d | b: at most one active'] += 1
                    g = gcd(b, d)
                    if g > 1:
                        b2, d2, r2 = b//g, d//g, r*g
                        k2, s2, n2, B2, m2, R2, word2, e2 = data(b2, d2, r2, P)
                        assert (n2, B2, m2, R2, word2) == (n, B, m, R, word)
                        assert {x: e2[x]*g for x in e2} == e
                        S, _ = values_for(e, rng)
                        if all(S[x] != 0 for x in S):
                            for j in (n, m, B):
                                assert N(j, b2, e2, P, word2, S)*g == N(j, b, e, P, word, S)
                        counts['gcd reparametrizations'] += 1
                    if len(active) < 1:
                        continue
                    for trial in range(3):
                        S, _ = values_for(e, rng)
                        if any(v == 0 for v in S.values()):
                            continue
                        prodw = lambda w: eval_prod(w, S)
                        AP, DR, T = prodw(P), prodw(R), prodw(word)
                        C = (k-1)*n+m
                        LS = sum((Fr(e[x])/S[x] for x in range(CLASSES)), Fr(0))
                        HC = window_forward(P, C, S) if C > 0 else Fr(n)
                        assert T == AP**k*DR
                        assert N(n, b, e, P, word, S) == Fr(n*d)/AP-LS*HC/T
                        assert N(m, b, e, P, word, S) == s*window_inverse(P, m, S)-Fr(m)*LS/DR
                        assert N(B, b, e, P, word, S) == Fr(b, s)*AP**(-k)*N(m, b, e, P, word, S)
                        for x in range(CLASSES):
                            assert window_inverse(word+(x,), B, S) == Fr(B)/(T*S[x])
                        counts['dual identity evaluations'] += 1
                    if len(active) >= 2:
                        for trial in range(4):
                            S, _ = values_for(e, rng)
                            if any(v == 0 for v in S.values()):
                                continue
                            first = N(n, b, e, P, word, S)
                            last = N(B, b, e, P, word, S)
                            assert not (first == 0 and last == 0), (b, d, r, P, S)
                            counts['two or more active: not both zero'] += 1
                    # automatic identity locus
                    if r == 1 and b % d == 1 % d and s == 1:
                        S, _ = values_for(e, rng)
                        if all(v != 0 for v in S.values()):
                            assert N(1, b, e, P, word, S) == 0 == N(B, b, e, P, word, S)
                            if len(active) >= 2:
                                assert N(n, b, e, P, word, S) != 0
                            counts['automatic identity'] += 1


def eval_prod(word, S):
    out = Fr(1)
    for x in word:
        out *= S[x]
    return out


def controls(counts):
    rng = random.Random(7)
    one_active = shared = 0
    for b in range(3, 8):
        for d in range(1, b):
            n = d
            for P in words(n):
                k, s, n, B, m, R, word, e = data(b, d, 1, P)
                active = [x for x in range(CLASSES) if e[x]]
                for trial in range(2):
                    S, _ = values_for(e, rng)
                    if any(v == 0 for v in S.values()):
                        continue
                    both = N(n, b, e, P, word, S) == 0 and N(B, b, e, P, word, S) == 0
                    if len(active) == 1 and both:
                        one_active += 1
                    if len(active) >= 2:
                        S2, _ = values_for(e, rng, labels=[0]*len(active))
                        if all(v != 0 for v in S2.values()) and \
                                N(n, b, e, P, word, S2) == 0 and N(B, b, e, P, word, S2) == 0:
                            shared += 1
    assert one_active and shared
    counts['control: one active class, both vanish'] = one_active
    counts['control: shared label, both vanish'] = shared


def positive_values(e, rng):
    return {x: Fr(rng.randint(1, 60), rng.randint(1, 13)) for x in range(CLASSES)}


def inequalities(counts):
    rng = random.Random(99)
    for b in range(3, 9):
        for d in range(1, b):
            for r in (1, 2):
                n = r*d
                if n > 6:
                    continue
                for P in words(n):
                    k, s, n, B, m, R, word, e = data(b, d, r, P)
                    active = [x for x in range(CLASSES) if e[x]]
                    signs = [e[x] > 0 for x in active]
                    for trial in range(3):
                        S = positive_values(e, rng)
                        AP, DR, T = eval_prod(P, S), eval_prod(R, S), eval_prod(word, S)
                        if signs and all(signs):
                            # exact count balance, then AM-GM with its equality case
                            product = T**d
                            for x in active:
                                product *= S[x]**e[x]
                            assert AP**b == product
                            lhs = sum(e[x]*window_inverse(word+(x,), n, S) for x in active)
                            assert lhs >= Fr(b*n)/AP
                            products = []
                            for x in active:
                                Q = word+(x,)
                                products += [eval_prod([Q[(i+a) % B] for a in range(n)], S) for i in range(B)]
                            equal = len(set(products)) == 1
                            if len(active) == 1:
                                assert (lhs == Fr(b*n)/AP) == equal
                            if len(active) >= 2:
                                if len({S[x] for x in active}) == len(active):
                                    assert lhs > Fr(b*n)/AP
                            counts['AM-GM evaluations'] += 1
                        if (len(active) >= 2 and sum(signs) == 1 and not all(signs)
                                and len({S[x] for x in active}) == len(active)):
                            phi = N(B, b, e, P, word, S)
                            assert phi > 0
                            counts['signed support: Phi_B > 0'] += 1
                            Z = {x: 1/(T*S[x]) for x in active}
                            wts = {x: Fr(e[x], d) for x in active}
                            windows = [Fr(1)/eval_prod([P[(i+a) % n] for a in range(B)], S) for i in range(n)]
                            Gm = mp.e**(sum(mp.log(mp.mpf(w.numerator)/w.denominator) for w in windows)/n)
                            Gz = mp.mpf(1)
                            for x in active:
                                zx = mp.mpf(Z[x].numerator)/Z[x].denominator
                                Gz *= zx**(mp.mpf(wts[x].numerator)/wts[x].denominator)
                            assert abs(Gm-Gz) < mp.mpf(10)**-40*Gm            # geometric mean = product of Z^w
                            bound = b*n*(Gm-sum(mp.mpf(wts[x].numerator)/wts[x].denominator
                                                *mp.mpf(Z[x].numerator)/Z[x].denominator for x in active))
                            phi_mp = mp.mpf(phi.numerator)/phi.denominator
                            assert phi_mp >= bound-mp.mpf(10)**-40
                            assert bound > 0
                            counts['one positive exponent: chain'] += 1
                            if len(active) == 2:
                                tau = wts[active[0]] if wts[active[0]] > 1 else wts[active[1]]
                                z = (Z[active[0]]/Z[active[1]]) if wts[active[0]] > 1 else (Z[active[1]]/Z[active[0]])
                                other = active[1] if wts[active[0]] > 1 else active[0]
                                zf, tf = mp.mpf(z.numerator)/z.denominator, mp.mpf(tau.numerator)/tau.denominator
                                convex = b*n*(mp.mpf(Z[other].numerator)/Z[other].denominator) \
                                    * (zf**tf-1-tf*(zf-1))
                                assert convex > 0
                                assert phi_mp >= convex-mp.mpf(10)**-40
                                counts['two supports: convexity term'] += 1
                    if r == 1 and s == 1:
                        assert all(v >= 0 for v in e.values())    # m = 1 excludes a negative exponent
                        counts['m = 1 exponents nonnegative'] += 1


def parity(counts):
    for b in range(3, 41):
        for d in range(2, 13):
            if d >= b or gcd(b, d) != 1:
                continue
            k, s = divmod(b, d)
            if s == 0:
                k, s = k-1, d
            for bits in product((0, 1), repeat=d):
                P = tuple(bits)
                R = P[:s-1]
                l = P*k+R
                T = lambda V: sum(V[i] != V[(i+1) % len(V)] for i in range(len(V)))
                for closure in (0, 1):
                    Q = l+(closure,)
                    assert len(Q) == b
                    if len(set(P)) == 2:
                        assert 0 < T(P) <= d and T(P) % 2 == 0 and T(Q) % 2 == 0
                        assert b*T(P) != d*T(Q), (b, d, P, closure)
                        counts['parity: nonconstant words'] += 1
                if P == (1,)*d:
                    Q = l+(0,)
                    assert b*T(P)-d*T(Q) == -2*d
                    counts['parity: constant word'] += 1


def main():
    counts = Counter()
    identities_and_nonvanishing(counts)
    controls(counts)
    inequalities(counts)
    parity(counts)
    for key in ('dual identity evaluations', 'two or more active: not both zero',
                'automatic identity', 'AM-GM evaluations', 'signed support: Phi_B > 0',
                'one positive exponent: chain', 'two supports: convexity term',
                'parity: nonconstant words', 'gcd reparametrizations'):
        assert counts[key], key
    print(dict(counts))
    print('check_dual_scalar: PASS')


if __name__ == '__main__':
    main()
