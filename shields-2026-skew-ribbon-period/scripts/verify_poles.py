r"""Paper section `sec:poles` (Endpoint poles and outward boundary defects).

Targets `lem:weak-sign` (subsection on weak Jacobi--Trudi signs).

For every pair of strict lists `X_1 > ... > X_m`, `Y_1 > ... > Y_m` with `X_i >= Y_i`, over
a bounded box, the determinant `det(h_{X_i - Y_j})` is built with `h_0 = nu` (a positive
rational) and symbolic generators.  Asserted: nonvanishing; the lexicographic leading monomial
for `h_M >> ... >> h_1`, evaluated with every positive generator negative, has sign
`(-1)^eta` with `eta = #{(i, j): i >= j, X_i > Y_j}`; and the simultaneous specialization
`h_j = -T^(B^j)` with `B` exceeding twice the largest matrix size plus two realizes all the signs
at once at one concrete `T` (checked at an explicit exact integer `T`, not asymptotically).
Sampled, not exhaustive: lists with entries up to 5 and size at most 3.
"""
from itertools import combinations, permutations

import sympy as sp

MAXLABEL = 5
MAXSIZE = 3
NUS = (sp.Rational(1), sp.Rational(7, 3))
TOP = MAXLABEL + 1                              # largest index, X_1 - Y_m <= MAXLABEL + 1
GENS = sp.symbols(f"h1:{TOP + 1}")              # lex order h_TOP >> ... >> h1
LEX = tuple(reversed(GENS))


def entry(j, nu):
    return nu if j == 0 else (sp.Integer(0) if j < 0 else GENS[j - 1])


def eta(X, Y):
    m = len(X)
    return sum(1 for i in range(m) for j in range(i + 1) if X[i] > Y[j])


def feasible_pairs():
    labels = range(0, MAXLABEL + 1)
    for m in range(1, MAXSIZE + 1):
        for X in combinations(sorted(labels, reverse=True), m):
            for Y in combinations(sorted(range(-1, MAXLABEL + 1), reverse=True), m):
                if all(X[i] >= Y[i] for i in range(m)):
                    yield X, Y


def main():
    pairs = list(feasible_pairs())
    dets = {}
    for X, Y in pairs:
        for nu in NUS:
            M = sp.Matrix(len(X), len(X), lambda i, j: entry(X[i] - Y[j], nu))
            P = sp.Poly(sp.expand(M.det()), *LEX)
            assert not P.is_zero                                            # nonvanishing
            mon = P.monoms(order='lex')[0]
            coef = P.coeff_monomial(mon)
            sign_neg = sp.sign(coef) * (-1) ** sum(mon)                     # all generators negative
            assert sign_neg == (-1) ** eta(X, Y), (X, Y, nu, mon, coef)
            dets[(X, Y, nu)] = (M, P)
    # simultaneous specialization h_j = -T^(B^j), exact integers
    B = 2 * MAXSIZE + 2 + 1
    T = 2 ** 8
    bad = 0
    for nu in NUS:
        den = nu.q
        vals = {j: -(T ** (B ** j)) for j in range(1, TOP + 1)}      # h_j = -T^(B^j)
        for X, Y in pairs:
            m = len(X)
            rows = [[(nu.p if X[i] - Y[j] == 0 else 0) if X[i] - Y[j] <= 0 else vals[X[i] - Y[j]] * den
                     for j in range(m)] for i in range(m)]
            # integer determinant scaled by den^m (a positive factor): Leibniz expansion
            val = 0
            for perm in permutations(range(m)):
                sgn = 1
                for a in range(m):
                    for b in range(a + 1, m):
                        if perm[a] > perm[b]:
                            sgn = -sgn
                term = sgn
                for i in range(m):
                    term *= rows[i][perm[i]]
                val += term
            assert val != 0
            assert (1 if val > 0 else -1) == (-1) ** eta(X, Y), (X, Y, nu)
    print(f"weak pairs {len(pairs)} x {len(NUS)} values of nu, sign and simultaneous specialization PASS")
    print("PASS")


if __name__ == "__main__":
    main()
