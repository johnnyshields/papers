"""Full mate-space check of the saturated-column rigidity theorem.

Paper section `sec:component-reductions`, `thm:saturated-column`.

Let F be connected with r >= 6 nonempty rows.  Suppose, after an optional
global rotation, its first column has all r-2 negatives permitted by connectedness
and at most two negative entries lie outside that column:
    x_3 < y_1   and   #{(i,j) : x_i < y_j, j >= 2} <= 2.
Then every connected Schur-equal mate is F or F*.

MECHANISM, independent of the production checkers (subset determinants,
hashing, context windows):
  * Equal skew Schur functions force equal row-length multisets and equal
    adjacent-gap multisets (held polynomial readings).  So EVERY possible
    connected mate of a source is a rearrangement of its rows with a rearrangement
    of its gaps.  All of them are enumerated here, not a sample.
  * Each candidate's Jacobi-Trudi determinant is evaluated at random points
    modulo a large prime.  A point where two values differ PROVES the polynomials
    differ, so exclusion is rigorous; only apparent matches go to an exact
    sympy check.
  * Zero-free sources only; the theorem's common-beta case is the homogenization step,
    checked in check_saturated_column.py.

Assertions:
  (1) every sampled r = 6 and r = 7 source satisfying the theorem's predicate has class
      exactly {F, F*};
  (2) CONTROL that must FIRE: merged A's five-row family at (b,g,q) = (2,3,1)
      satisfies the same predicate with r = 5 and HAS a nonrotation mate, so the
      checker detects mates and r >= 6 is a real boundary.
"""
import random
from itertools import permutations, product

import sympy as sp

P = (1 << 61) - 1
rng = random.Random(20260923)
POINTS = [[rng.randrange(1, P) for _ in range(80)] for _ in range(3)]


def betas(rows, gaps):
    n = len(rows)
    x, y = [0] * n, [0] * n
    x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return x, y


def valid(rows, gaps):
    return all(0 <= gaps[i] < min(rows[i], rows[i + 1]) for i in range(len(gaps)))


def det_mod(rows, gaps, pt):
    x, y = betas(rows, gaps)
    n = len(rows)

    def hv(k):
        return 0 if k < 0 else (1 if k == 0 else pt[k - 1])
    M = [[hv(x[i] - y[j]) % P for j in range(n)] for i in range(n)]
    det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det = det * M[c][c] % P
        inv = pow(M[c][c], P - 2, P)
        for r in range(c + 1, n):
            f = M[r][c] * inv % P
            if f:
                M[r] = [(a - f * b) % P for a, b in zip(M[r], M[c])]
    return det % P


def exact(rows, gaps):
    H = sp.symbols('h1:80')
    x, y = betas(rows, gaps)
    n = len(rows)
    hf = lambda k: sp.Integer(0) if k < 0 else (sp.Integer(1) if k == 0 else H[k - 1])
    return sp.expand(sp.Matrix(n, n, lambda i, j: hf(x[i] - y[j])).det(method='berkowitz'))


def rot(rows, gaps):
    return tuple(reversed(rows)), tuple(reversed(gaps))


def zero_free(rows, gaps):
    x, y = betas(rows, gaps)
    return not (set(x) & set(y))


def a44(rows, gaps):
    """Predicate on the literal orientation, normalized y_r = 0."""
    x, y = betas(rows, gaps)
    n = len(rows)
    if n < 3 or not x[2] < y[0]:
        return False
    return sum(1 for i in range(n) for j in range(1, n) if x[i] < y[j]) <= 2


def mates(rows, gaps):
    """All connected diagrams Schur-equal to (rows, gaps), found by full enumeration."""
    sig = [det_mod(rows, gaps, pt) for pt in POINTS]
    found = set()
    for R in set(permutations(rows)):
        for G in set(permutations(gaps)):
            if not valid(R, G):
                continue
            if all(det_mod(R, G, pt) == s for pt, s in zip(POINTS, sig)):
                found.add((R, G))
    src = exact(rows, gaps)
    confirmed = {c for c in found if exact(*c) == src}
    assert confirmed == found, "a random-point match failed the exact check"
    return confirmed


def cores(m, smax):
    """Connected zero-free m-row cores (C; D), C_1 = S, D_m = 0, with <= 2 negatives."""
    out = []
    for S in range(m, smax + 1):
        for Cr in __import__('itertools').combinations(range(1, S), m - 1):
            C = (S,) + tuple(sorted(Cr, reverse=True))
            for Dr in __import__('itertools').combinations(range(1, S), m - 1):
                D = tuple(sorted(Dr, reverse=True)) + (0,)
                if any(C[i] <= D[i] for i in range(m)):
                    continue
                if any(C[i + 1] <= D[i] for i in range(m - 1)):
                    continue
                if set(C) & set(D):
                    continue
                if sum(1 for c in C for d in D if c < d) <= 2:
                    out.append((C, D))
    return out


def sources(m, smax, params):
    """Saturated-column sources built as singleton contexts C_s(Q; u, v, g), per eq:singleton-context:
    X = (z+s+u, z+s, v+C_1..v+C_m),  Y = (z, v+D_1..v+D_m, 0),  z = v + S + g."""
    out = []
    for C, D in cores(m, smax):
        S = C[0]
        for s, u, v, g in params:
            z = v + S + g
            X = (z + s + u, z + s) + tuple(v + c for c in C)
            Y = (z,) + tuple(v + d for d in D) + (0,)
            rows = tuple(X[i] - Y[i] for i in range(len(X)))
            gaps = tuple(X[i + 1] - Y[i] for i in range(len(X) - 1))
            if not valid(rows, gaps) or not zero_free(rows, gaps):
                continue
            assert betas(rows, gaps) == (list(X), list(Y)), "profile round-trip failed"
            if a44(rows, gaps) or a44(*rot(rows, gaps)):
                out.append((rows, gaps))
    return out


def main():
    tested = 0
    params = [(1, 1, 1, 1), (1, 2, 1, 1), (2, 1, 1, 2), (1, 1, 2, 1)]
    for m, smax, take in ((4, 9, 40), (5, 12, 3)):
        n = m + 2
        pool = sorted(set(sources(m, smax, params)), key=lambda s: (sum(s[0]), s))
        assert pool, f"VACUOUS: no saturated-column sources built at r = {n}"
        step = max(1, len(pool) // take)
        picked = pool[::step][:take]
        print(f"r={n}: {len(pool)} zero-free saturated-column sources built as singleton contexts; testing {len(picked)}, "
              f"{min(sum(p[0]) for p in picked)}-{max(sum(p[0]) for p in picked)} cells")
        for rows, gaps in picked:
            cls = mates(rows, gaps)
            expect = {(rows, gaps), rot(rows, gaps)}
            assert cls == expect, (rows, gaps, "NONROTATION MATE", sorted(cls - expect))
            tested += 1
    print(f"PASS (1): {tested} saturated-column sources at r = 6, 7 -- every class is exactly {{F, F*}},")
    print("          each against EVERY row/gap rearrangement, exclusion certified by a differing value")

    X, Y = (14, 11, 8, 5, 2), (9, 4, 3, 1, 0)
    rows = tuple(X[i] - Y[i] for i in range(5))
    gaps = tuple(X[i + 1] - Y[i] for i in range(4))
    assert betas(rows, gaps) == (list(X), list(Y))
    assert a44(rows, gaps), "control source does not satisfy the predicate"
    extra = mates(rows, gaps) - {(rows, gaps), rot(rows, gaps)}
    assert extra, "CONTROL DID NOT FIRE: the five-row family member shows no nonrotation mate"
    print(f"PASS (2, control fires): five-row source {rows};{gaps} satisfies the predicate at r = 5")
    print(f"          and has nonrotation mate(s) {sorted(extra)} -- so r >= 6 is a real boundary")
    print("ALL PASS")


if __name__ == "__main__":
    main()
