#!/usr/bin/env python3
"""Exhaustive check of the prime obstruction, Lemma `lem:five-prime`.

    For u > v > tau >= 0, b > p >= 0, c > v + p, and d = c + u - v,
        B  does not divide  H_u T(c) - H_v T(d),
    where
        B    = H_u H_v - H_tau H_L,      L = u + v - tau,
        T(z) = H_b H_z - H_p H_{z+q},    q = b - p.

The hypotheses do NOT imply d > max(c, u, b, v): c > v + p leaves d <= b
attainable, and d = b occurs.  The enumeration therefore covers that locus
explicitly rather than assuming it away, and it verifies both specializations
the proof uses -- H_u = H_tau = 0, which must leave H_v(H_p H_{d+q} - H_b H_d),
and H_v = H_tau = 0, which on the forced branch p = tau, b = u must leave
H_u^2 H_c.

METHOD.  The H_i are independent indeterminates, so B and P are honest
polynomials in Z[H_0, H_1, ...] and non-divisibility is decided exactly by
multivariate division -- no numerical substitution and no sampling.  Monomials
are index multisets, so commutativity holds and equal indices collapse as the
collected-coefficient convention requires.

This corroborates the algebraic proof in the paper; it does not replace it.
The paper's domain is unbounded and this enumeration is finite.
"""
import sys
from collections import defaultdict
from itertools import product

CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 9


def mono(*idx):
    """A monomial as a sorted index tuple; equal indices collapse by position."""
    return tuple(sorted(idx))


def pmul(a, b):
    out = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[mono(*(ma + mb))] += ca * cb
    return {m: c for m, c in out.items() if c}


def padd(a, b, s=1):
    out = defaultdict(int, a)
    for m, c in b.items():
        out[m] += s * c
    return {m: c for m, c in out.items() if c}


def H(i):
    return {mono(i): 1}


def divides(B, P):
    """Exact multivariate division test: does B divide P in Z[H_*]?

    Both are at most quadratic times linear here, so ordinary multivariate
    division with a fixed monomial order terminates and is decisive.
    """
    if not P:
        return True
    order = lambda m: (len(m), m)
    lead = lambda q: max(q, key=order)
    lb = lead(B)
    R = dict(P)
    while R:
        lr = lead(R)
        # try to divide lr by lb as multisets
        rem = list(lr)
        ok = True
        for i in lb:
            if i in rem:
                rem.remove(i)
            else:
                ok = False
                break
        if not ok:
            return False
        if R[lr] % B[lb]:
            return False
        q = {mono(*rem): R[lr] // B[lb]}
        R = padd(R, pmul(q, B), -1)
    return True


def build(u, v, tau, b, p, c):
    d = c + u - v
    q = b - p
    L = u + v - tau
    B = padd(pmul(H(u), H(v)), pmul(H(tau), H(L)), -1)
    T = lambda z: padd(pmul(H(b), H(z)), pmul(H(p), H(z + q)), -1)
    P = padd(pmul(H(u), T(c)), pmul(H(v), T(d)), -1)
    return B, P, d


def main():
    tested = divis = 0
    worst = []
    d_le_b = 0
    for u, v, tau, b, p, c in product(range(CAP + 1), repeat=6):
        if not (u > v > tau >= 0 and b > p >= 0 and c > v + p):
            continue
        B, P, d = build(u, v, tau, b, p, c)
        tested += 1
        if d <= b:
            d_le_b += 1
        if divides(B, P):
            divis += 1
            if len(worst) < 5:
                worst.append((u, v, tau, b, p, c, d))
    print(f"  domain u>v>tau>=0, b>p>=0, c>v+p, indices <= {CAP}")
    print(f"  tuples tested: {tested}   of which d <= b: {d_le_b}")
    print(f"  tuples where B DIVIDES P: {divis}")
    if worst:
        print(f"  COUNTEREXAMPLES: {worst}")
    assert divis == 0, "lem:five-prime FAILS on the tuples above"
    assert tested > 0 and d_le_b > 0, "vacuous: domain or d<=b stratum empty"

    # The two specializations the repaired proof actually uses.
    spec_ok = spec_n = 0
    for u, v, tau, b, p, c in product(range(CAP + 1), repeat=6):
        if not (u > v > tau >= 0 and b > p >= 0 and c > v + p):
            continue
        B, P, d = build(u, v, tau, b, p, c)
        q = b - p
        z = lambda poly, kill: {m: cc for m, cc in poly.items()
                                if not (set(m) & kill)}
        # first: H_u = H_tau = 0 kills B, and must leave H_v(H_p H_{d+q} - H_b H_d)
        k1 = {u, tau}
        assert not z(B, k1), "B did not vanish under H_u=H_tau=0"
        want = z(padd(pmul(H(v), pmul(H(p), H(d + q))),
                      pmul(H(v), pmul(H(b), H(d))), -1), k1)
        assert z(P, k1) == want, (u, v, tau, b, p, c)
        spec_n += 1
        # second: H_v = H_tau = 0 kills B; when p=tau and b=u it leaves H_u^2 H_c
        k2 = {v, tau}
        assert not z(B, k2), "B did not vanish under H_v=H_tau=0"
        if p == tau and b == u:
            assert z(P, k2) == z(pmul(pmul(H(u), H(u)), H(c)), k2)
            spec_ok += 1
    print(f"  first specialization verified on all {spec_n} tuples")
    print(f"  second specialization, on the {spec_ok} tuples with p=tau and b=u")
    assert spec_ok > 0, "the forced branch p=tau, b=u never occurs: control is vacuous"

    # CONTROL: a deliberately false divisibility must be detected.
    Bx = padd(pmul(H(3), H(2)), pmul(H(1), H(4)), -1)
    assert divides(Bx, pmul(Bx, H(7))), "CONTROL FAILED: true divisibility missed"
    assert not divides(Bx, padd(pmul(Bx, H(7)), H(5))), \
        "CONTROL FAILED: false divisibility accepted"
    print("  CONTROLS FIRED: division test accepts a multiple, rejects a non-multiple")
    print("ALL PASS")


if __name__ == "__main__":
    main()
