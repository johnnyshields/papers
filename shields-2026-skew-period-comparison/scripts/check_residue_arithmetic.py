#!/usr/bin/env python3
"""Paper section `sec:older-cells` (Residue exclusions and smaller ribbon probes) and the
arithmetic of `thm:ordinary-probes`; targets `lem:arithmetic-transcendence`,
`lem:row-collapse`, `lem:modular-saturation`, `thm:heterogeneous-reduction`,
`thm:ordinary-probes`.

Exact checks of the elementary arithmetic and the residue-specialization algebra
those proofs consume.  The field-theoretic steps (residue fields, gradings,
primitive triangularity, factorization in the polynomial rings) are not
computational and are not checked here.
"""
from math import gcd
import sympy as sp

N = 40


def prime_divisor_exists(n):
    return abs(n) >= 2


def check_arithmetic_transcendence():
    """lem:arithmetic-transcendence: a rational residue value a/b other than 0 or 1
    forces a prime divisor of one of the nonzero integers a, b, b - a."""
    count = 0
    for a in range(-N, N + 1):
        for b in range(1, N + 1):
            if gcd(a, b) != 1 or a == 0 or a == b:
                continue
            assert b - a != 0 and a != 0
            assert any(prime_divisor_exists(x) for x in (a, b, b - a)), (a, b)
            count += 1
    assert count > 1000
    print('PASS arithmetic-transcendence prime-divisor step', count)


def check_row_collapse():
    """lem:row-collapse: under b_j = f tau^(j-1), M_j = A^(j-1) b_j equals
    f^j v^(j-1) with v = A tau / f; the recurrence M_i M_j - f M_(i+j-1) vanishes; and
    a weight-(b+1) monomial of length d specializes to f^(b+1) v^(b+1-d), with only
    h_(b+1) of length one."""
    f, A, tau = sp.symbols('f A tau')
    v = A * tau / f

    def M(j):
        return A ** (j - 1) * f * tau ** (j - 1)

    for j in range(1, 12):
        assert sp.simplify(M(j) - f ** j * v ** (j - 1)) == 0
    for i in range(2, 9):
        for j in range(2, 9):
            assert sp.simplify(M(i) * M(j) - f * M(i + j - 1)) == 0
    count = 0
    for w in range(1, 13):
        for d in range(1, w + 1):
            lengths = partitions(w, d)
            assert lengths
            for parts in lengths:
                spec = sp.Integer(1)
                for j in parts:
                    spec *= M(j)
                assert sp.simplify(spec - f ** w * v ** (w - d)) == 0, parts
            if d == 1:
                assert lengths == [(w,)]
            count += len(lengths)
    print('PASS row-collapse specialization', count)


def partitions(w, d):
    out = []
    def rec(rem, k, mx, cur):
        if k == 0:
            if rem == 0:
                out.append(tuple(cur))
            return
        for x in range(min(rem, mx), 0, -1):
            rec(rem - x, k - 1, x, cur + [x])
    rec(w, d, w, [])
    return out


def coprime_pairs(bmin=2):
    for a in range(1, N):
        for b in range(bmin, N):
            if gcd(a, b) == 1:
                yield a, b


def check_modular_saturation():
    """lem:modular-saturation and the pivot matching in thm:ordinary-probes: from
    N_E = p + w = m q + u, the pivot equation j p + w = k q + u with p = a d,
    q = b d is a(j-1) = b(k-m), and it has no solution with 2 <= j <= b; the
    leftover weight a - b m is nonzero."""
    count = 0
    for a, b in coprime_pairs():
        for m in range(2, 8):
            assert (a - b * m) % b != 0
            for j in range(2, b + 1):
                assert a * (j - 1) % b != 0
                count += 1
            # j = 1 is the only residue class that matches
            assert a * (b + 1 - 1) % b == 0
    print('PASS modular-saturation pivot congruence', count)


def check_heterogeneous_reduction():
    """thm:heterogeneous-reduction: for w >= q the mark mismatch w - u = m q - p is not
    divisible by q (q does not divide p); the high-row scalar
    (b+1)p + rho - j0 (p + rho), 0 < rho < p, j0 in {0,1,2}, is nonzero; the weight
    a - b m is not divisible by b."""
    count = 0
    for a, b in coprime_pairs():
        d = 1
        p, q = a * d, b * d
        assert p % q != 0
        for m in range(2, 8):
            assert (m * q - p) % q != 0
        for rho in range(1, p):
            for j0 in (0, 1, 2):
                assert (b + 1) * p + rho - j0 * (p + rho) != 0
                count += 1
    print('PASS heterogeneous-reduction scalars', count)


def check_ordinary_probes_arithmetic():
    """thm:ordinary-probes: the matched top indices (1 + b k) p + w = (m + a k) q + u,
    l = b p = a q, the bound n - l (K - 1) < n for K >= 2, and the wide-source
    contradiction b K = 2t against K >= t + 1."""
    count = 0
    for a, b in coprime_pairs():
        for d in (1, 2, 3):
            p, q = a * d, b * d
            ell = b * p
            assert ell == a * q
            for m in range(2, 6):
                for u in range(1, q):
                    w = m * q + u - p
                    for k in range(0, 6):
                        assert (1 + b * k) * p + w == (m + a * k) * q + u
                        count += 1
            for t in range(1, 8):
                for K in range(t + 1, t + 8):
                    assert b * K != 2 * t
                    assert ell * (K - 1) > 0
    print('PASS ordinary-probes index and area arithmetic', count)


if __name__ == '__main__':
    check_arithmetic_transcendence()
    check_row_collapse()
    check_modular_saturation()
    check_heterogeneous_reduction()
    check_ordinary_probes_arithmetic()
