"""Equal connected children through mark factors (ph:CF0, ph:coface-data).

Paper section `app:cofaces` (Cofaces, two-copy identities, and native residues), ph:coface-data (mixed
normalization, "the same prime argument gives the whole child equality and
N_W Pi_G(k) = D_W Pi_Q(a)").

The cleared mixed comparison is s_S s_B s_N = c s_T s_A s_N' in Lambda, with c rational.  The
Lean statement child_equality_marked concludes s_S = s_T, s_B s_N = s_A s_N' and c = 1 when every
component of the extra factors on each side has span below the connected child on the other.

1. The constant is +1: over every skew shape lambda/mu inside a 4 x 4 box with at most 4 cells,
   any two products s_D s_E that are proportional over Q are equal (primitivity of products and
   positive specialization).
2. The span hypothesis is needed: S = (2), T = (1,1), N = (1,1), N' = (2), A = B = empty gives
   s_S s_N = s_T s_N' with s_S != s_T.  There the mark factor N has span 2 = span T, violating
   the hypothesis on N.
"""

import itertools

import sympy as sp

H = sp.symbols("h1:9")


def h(k):
    if k < 0:
        return sp.Integer(0)
    if k == 0:
        return sp.Integer(1)
    return H[k - 1]


def skew_schur(lam, mu):
    n = len(lam)
    mu = list(mu) + [0] * (n - len(mu))
    if n == 0:
        return sp.Integer(1)
    M = sp.Matrix(n, n, lambda i, j: h(lam[i] - mu[j] - i + j))
    return sp.expand(M.det())


def partitions_in_box(rows, cols):
    for p in itertools.product(range(cols + 1), repeat=rows):
        if all(p[i] >= p[i + 1] for i in range(rows - 1)):
            yield tuple(x for x in p)


def shapes(max_cells=4):
    out = {}
    for lam in partitions_in_box(4, 4):
        for mu in partitions_in_box(4, 4):
            if all(m <= l for m, l in zip(mu, lam)):
                cells = sum(lam) - sum(mu)
                if 0 < cells <= max_cells:
                    f = skew_schur(lam, mu)
                    out.setdefault(f, (lam, mu))
    return list(out.items())


def normalize(f):
    p = sp.Poly(f, *H)
    lc = p.LC()
    return sp.expand(f / lc), lc


def check_constant_is_one():
    fs = [f for f, _ in shapes()]
    seen = {}
    pairs = 0
    for a, b in itertools.combinations_with_replacement(range(len(fs)), 2):
        prod = sp.expand(fs[a] * fs[b])
        key, lc = normalize(prod)
        if key in seen:
            other, olc = seen[key]
            assert sp.expand(prod - other) == 0, (a, b)
            pairs += 1
        else:
            seen[key] = (prod, lc)
    return len(fs), pairs


def check_span_hypothesis_needed():
    sS = skew_schur((2,), ())
    sT = skew_schur((1, 1), ())
    sN = skew_schur((1, 1), ())
    sNp = skew_schur((2,), ())
    assert sp.expand(sS * sN - sT * sNp) == 0
    assert sp.expand(sS - sT) != 0


if __name__ == "__main__":
    n, pairs = check_constant_is_one()
    check_span_hypothesis_needed()
    print(f"{n} distinct skew functions; {pairs} proportional coincidences among products, all equal")
    print("span hypothesis needed: s_(2) s_(1,1) = s_(1,1) s_(2) with s_(2) != s_(1,1)")
    print("PASS")
