"""Paper section `subsec:locus-family` (the reversal family on the ratio locus).
Target labels: `lem:two-series-reversal`.

The abstract two-series reversal identity, verified on generic coefficients.
It is the step that carries the all-k statement of the family.  It is checked on
generic (algebraically independent) series coefficients rather than on the
h-specialization, so that a coincidence of the specialization cannot make it pass.

Setup.  Two formal series
    A(z) = 1 + a_1 z + a_2 z^2 + ...,      B(z) = b_0 + b_1 z + ...,
and Q = B/A.  For a binary word x = x_1...x_l over {A, B}, let

    M_x = [ B ; A ; S X_{x_1} ; S^2 X_{x_2} ; ... ; S^l X_{x_l} ]

on columns 0..l+1, where S shifts right, X_A = A and X_B = B.  With
J = { i : x_i = B }, the claimed identity is

    det M_x = (-1)^(l+1-|J|) det T_Q[{0} u J, J u {l+1}],   (T_Q)_rc = q_{c-r}.

Reversing x replaces J by l+1-J, which anti-transposes that minor, whence

    det M_x = det M_{x^rev}.

Both the boxed identity and its reversal consequence are checked.  Controls: a
non-reversal permutation must break the equality, or the test is blind.
"""

import itertools
import sympy as sp

LMAX = 5
NC = LMAX + 4                      # series coefficients needed

a = [sp.Integer(1)] + [sp.Symbol("a%d" % i) for i in range(1, NC)]
b = [sp.Symbol("b%d" % i) for i in range(NC)]


def series_A(i):
    return a[i] if 0 <= i < NC else sp.Integer(0)


def series_B(i):
    return b[i] if 0 <= i < NC else sp.Integer(0)


# Q = B / A  as a power series: q_n = b_n - sum_{i=1..n} a_i q_{n-i}
Q = []
for n in range(NC):
    val = series_B(n) - sum(a[i] * Q[n - i] for i in range(1, n + 1))
    Q.append(sp.expand(val))


def q(n):
    return Q[n] if 0 <= n < NC else sp.Integer(0)


def M_of(word):
    """word: tuple over {'A','B'} of length l.  Returns (l+2)x(l+2) matrix."""
    l = len(word)
    rows = []
    rows.append([series_B(c) for c in range(l + 2)])          # B
    rows.append([series_A(c) for c in range(l + 2)])          # A
    for i, ch in enumerate(word, start=1):                    # S^i X_{x_i}
        f = series_B if ch == "B" else series_A
        rows.append([f(c - i) for c in range(l + 2)])
    return sp.Matrix(rows)


def toeplitz_minor(J, l):
    rows = [0] + sorted(J)
    cols = sorted(J) + [l + 1]
    return sp.Matrix(len(rows), len(cols),
                     lambda r, c: q(cols[c] - rows[r]))


print("Abstract two-series reversal identity, generic coefficients\n")
print("  l   words   boxed identity   det M_x = det M_rev")
for l in range(1, LMAX + 1):
    words = list(itertools.product("AB", repeat=l))
    id_ok = rev_ok = 0
    for x in words:
        J = {i for i, ch in enumerate(x, start=1) if ch == "B"}
        lhs = sp.expand(M_of(x).det(method="berkowitz"))
        rhs = sp.expand(sp.Integer(-1) ** (l + 1 - len(J))
                        * toeplitz_minor(J, l).det(method="berkowitz"))
        id_ok += sp.simplify(lhs - rhs) == 0
        rev = tuple(reversed(x))
        rev_ok += sp.expand(lhs - M_of(rev).det(method="berkowitz")) == 0
    print("  %d   %5d   %11d/%d   %14d/%d"
          % (l, len(words), id_ok, len(words), rev_ok, len(words)))
    assert id_ok == len(words), ("boxed identity failed at l=%d" % l)
    assert rev_ok == len(words), ("reversal failed at l=%d" % l)

print("\n  J -> l+1-J under reversal (the anti-transposition), checked:")
for l in range(1, LMAX + 1):
    for x in itertools.product("AB", repeat=l):
        J = {i for i, ch in enumerate(x, start=1) if ch == "B"}
        Jr = {i for i, ch in enumerate(reversed(x), start=1) if ch == "B"}
        assert Jr == {l + 1 - i for i in J}, (x, J, Jr)
print("     holds for every binary word up to l=%d" % LMAX)

print("\nCONTROL -- a non-reversal permutation must break it:")
fired = checked = 0
for l in (4, 5):
    for x in itertools.product("AB", repeat=l):
        for p in set(itertools.permutations(x)):
            if p == x or p == tuple(reversed(x)):
                continue
            checked += 1
            if sp.expand(M_of(x).det(method="berkowitz")
                         - M_of(p).det(method="berkowitz")) != 0:
                fired += 1
            if checked >= 30:
                break
        if checked >= 30:
            break
    if checked >= 30:
        break
print("  %d of %d non-reversal pairs differ -> control fires" % (fired, checked))
assert fired > 0

print("\nALL PASS")
