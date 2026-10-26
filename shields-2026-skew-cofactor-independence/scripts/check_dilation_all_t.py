#!/usr/bin/env python3
"""Paper section `sec:dilation` (Integral dilation).  Targets `thm:dilation`, `cor:nullity-increment`,
`eq:dilation-kernel`, `eq:nullity-increment`, `eq:offgrid-space`, for EVERY dilation factor t.

`check_cofactor_dilation.py` compares the kernel of tC with the formula for t <= 4.  Here the factor t is
removed from the problem, so that one finite computation per core settles every t at once.

The reduction.  Write an off-grid position of tC as z = tq + r with 0 < r < t and 0 <= q < N.  Its unit is
    U_z = sum_{b_j <= q <= a_i - 1} sigma_t(D_ij) h_{t(a_i-q-1) + (t-r)} h_{t(q-b_j) + r},
because a_i > z/t > b_j is b_j <= q <= a_i - 1 whatever r and t are.  Its two off-grid letters lie in the
residue classes t-r and r, so a relation splits by the unordered pair {r, t-r}; within a pair the letters
h_{tx+(t-r)}, h_{ty+r} are renamed X_x, Y_y, and the grid letters h_{tk} are renamed h_k.  Every pair with
r != t/2 then gives the SAME t-free system
    V_q = sum D_ij X_{a_i-q-1} Y_{q-b_j},     V'_q = sum D_ij Y_{a_i-q-1} X_{q-b_j}     (0 <= q < N),
and when t is even the middle class r = t/2 gives
    W_q = sum D_ij W_{a_i-q-1} W_{q-b_j}      (0 <= q < N),
with W a single commuting alphabet.  The grid part is sigma_t of the base relation system.  Hence
    dim K(tC) = dim K(C) + floor((t-1)/2) kappa_1 + [t even] kappa_2,
with kappa_1, kappa_2 the kernel dimensions of the two t-free systems: a finite computation on C alone.

Asserted, for every core in the box:
  (1) the reduction itself, against direct kernels of tC for t = 2..TMAX;
  (2) the explicit kernels: on the pair system the g vectors lambda(V_q) = psi(q mod g),
      lambda(V'_q) = -psi((N-1-q) mod g) are relations, and on the middle system the odd ones
      psi(q) = -psi((N-1-q) mod g) are; these transport to A_off(tC) on every pair, for every t;
  (3) on nonsymmetric dense cores, kappa_1 = g and kappa_2 = (g - f(g, N-1))/2, so the relations in (2) are
      all of them and eq:dilation-kernel holds for every t;
  (4) eq:nullity-increment for every t: the count floor((t-1)/2) g + [t even](g - f(g,N-1))/2 equals
      ((t-1)g - f(tg,tN) + f(g,N))/2 symbolically in t on each parity class, using f(q,M) = 1 for q odd and
      2[M even] for q even (elementary, asserted on a box); and g = 1 gives floor((t-1)/2).
On symmetric cores (where the cofactor hypothesis fails) (1) and (2) still hold and the containment of
eq:dilation-kernel is checked for every t; the equality is not claimed there.

What stays a census: the cores themselves, every normalized dense core of span <= SPAN and order <= ORDER.
"""
import sys
from collections import Counter
from math import gcd

import sympy as sp

from check_cofactor_dilation import (
    add_to, available, cofactors, dense_boards, modulus, multiply, rank, symmetric, unit,
)

SPAN, ORDER = 9, 3
TMAX = 5
X0, Y0, W0 = 10 ** 6, 2 * 10 ** 6, 3 * 10 ** 6


def f(q, M):
    return sum((2 * r - M) % q == 0 for r in range(q))


def pair_system(a, b, cofs):
    N, out = a[0], {}
    for tag, (L, R) in (("V", (X0, Y0)), ("V'", (Y0, X0))):
        for q in range(N):
            poly = Counter()
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    if y <= q <= x - 1:
                        add_to(poly, multiply(cofs[i][j], {tuple(sorted((L + x - q - 1, R + q - y))): 1}))
            out[tag, q] = poly
    return out


def middle_system(a, b, cofs):
    N, out = a[0], {}
    for q in range(N):
        poly = Counter()
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                if y <= q <= x - 1:
                    add_to(poly, multiply(cofs[i][j], {tuple(sorted((W0 + x - q - 1, W0 + q - y))): 1}))
        out[q] = poly
    return out


def relation_rank(system, vectors):
    """Assert each vector is a relation of the system; return the rank of the vectors."""
    for vec in vectors:
        residual = Counter()
        for key, w in vec.items():
            if w:
                add_to(residual, system[key], w)
        assert not residual
    keys = sorted({k for v in vectors for k in v}, key=str)
    return rank([{(str(k),): v[k] for k in keys if v.get(k)} for v in vectors])


def nullity(polys):
    polys = list(polys)
    return len(polys) - rank(polys)


def check_f_closed_form():
    for q in range(1, 80):
        for M in range(0, 2 * q + 2):
            assert f(q, M) == (1 if q % 2 else 2 * (M % 2 == 0)), (q, M)


def check_formula_symbolic():
    s, g = sp.symbols("s g", integer=True, positive=True)
    for g_par in (0, 1):
        for N_par in (0, 1):
            fc = lambda q_par, M_par: 1 if q_par else 2 * (M_par == 0)      # noqa: E731
            # t = 2s + 1 (odd): tg has the parity of g, tN that of N
            lhs = s * g
            rhs = ((2 * s) * g - fc(g_par, N_par) + fc(g_par, N_par)) / 2
            assert sp.simplify(lhs - rhs) == 0
            # t = 2s (even): tg and tN even
            lhs = (s - 1) * g + (g - fc(g_par, (N_par - 1) % 2)) / sp.Integer(2)
            rhs = ((2 * s - 1) * g - 2 + fc(g_par, N_par)) / sp.Integer(2)
            assert sp.simplify(lhs - rhs) == 0, (g_par, N_par)
    # modulus one: floor((t-1)/2) on both parities
    assert sp.simplify(((2 * s) * 1 - 1 + 1) / 2 - s) == 0                       # t = 2s+1
    assert sp.simplify(((2 * s - 1) * 1 - 2 + 1) / sp.Integer(2) - (s - 1)) == 0  # t = 2s


def main():
    check_f_closed_form()
    check_formula_symbolic()
    print("f(q,M) closed form on q < 80; eq:nullity-increment = floor((t-1)/2) g + [t even](g - f(g,N-1))/2 "
          "symbolically on every parity class; modulus one gives floor((t-1)/2)")
    n_cores = n_nonsym = n_direct = 0
    for a, b in dense_boards(SPAN, ORDER):
        N, g = a[0], modulus(a, b)
        cofs = cofactors(a, b)
        base = nullity(unit(a, b, z, cofs) for z in available(a, b))
        P = pair_system(a, b, cofs)
        Wsys = middle_system(a, b, cofs)
        kappa1 = nullity(P.values())
        kappa2 = nullity(Wsys.values())
        # (2) the explicit relations
        pair_vecs = []
        for r0 in range(g):
            vec = {}
            for q in range(N):
                vec["V", q] = vec.get(("V", q), 0) + (1 if q % g == r0 else 0)
                vec["V'", q] = vec.get(("V'", q), 0) - (1 if (N - 1 - q) % g == r0 else 0)
            pair_vecs.append(vec)
        assert relation_rank(P, pair_vecs) == g
        mid_vecs = []
        for r0 in range(g):
            partner = (N - 1 - r0) % g
            if partner == r0:
                continue
            mid_vecs.append({q: (1 if q % g == r0 else 0) - (1 if q % g == partner else 0) for q in range(N)})
        mid_rank = relation_rank(Wsys, mid_vecs) if mid_vecs else 0
        assert mid_rank == (g - f(g, N - 1)) // 2
        assert kappa1 >= g and kappa2 >= mid_rank                                 # containment, every t
        # (1) the reduction against direct kernels of tC
        for t in range(2, TMAX + 1):
            if N * t > 30:
                break
            aa, bb = tuple(t * x for x in a), tuple(t * y for y in b)
            cc = cofactors(aa, bb)
            direct = nullity(unit(aa, bb, z, cc) for z in available(aa, bb))
            predicted = base + ((t - 1) // 2) * kappa1 + (kappa2 if t % 2 == 0 else 0)
            assert direct == predicted, (a, b, t, direct, predicted)
            n_direct += 1
        # (3) on nonsymmetric dense cores the t-free kernels are exactly the arithmetic ones
        if not symmetric(a, b):
            assert kappa1 == g and kappa2 == (g - f(g, N - 1)) // 2, (a, b, kappa1, kappa2, g)
            for t in range(1, 41):
                inc = ((t - 1) // 2) * kappa1 + (kappa2 if t % 2 == 0 else 0)
                assert 2 * inc == (t - 1) * g - f(t * g, t * N) + f(g, N), (a, b, t)
            n_nonsym += 1
        n_cores += 1
    assert n_cores > 20 and n_nonsym > 10 and n_direct > 40
    print("%d dense cores (span <= %d, order <= %d), %d nonsymmetric: the t-free pair and middle systems "
          "reproduce dim K(tC) at %d direct (core, t) cases; their kernels are the transported residue "
          "functions; so eq:dilation-kernel and eq:nullity-increment hold for every t on every nonsymmetric "
          "core in the box" % (n_cores, SPAN, ORDER, n_nonsym, n_direct))
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
