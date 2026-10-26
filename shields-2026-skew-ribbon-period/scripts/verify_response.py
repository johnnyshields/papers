r"""Paper section `sec:response` (The complete scalar and its second channel).

Targets `eq:schur-complement`, `eq:gradient-product`, `eq:whole-observers`, the derivations
`delta_s`, `V_s`, `DD_s(lambda)` of that section, the line clocks stated after
`eq:whole-observers`, and the commutator identities before `prop:clocks`.

Objects come from definitions.  For a connected skew diagram `S` of span `N` the proper matrix
`A_S` is the Jacobi--Trudi matrix of the beta lists with the top row (`N`) and last column (`0`)
removed, `b` and `w` are the deleted column and row, and `f_S = h_N - w A_S^{-1} b` is compared
with `s_S / d s_S / d h_N` computed from the full determinant.  With `h_0 = nu` a symbol the
endpoint coframes `R_S, L_S` are built from `A_S^{-1} b` and `w A_S^{-1}`; then
`d f_S / d h_m = [z^{N-m}] R_S L_S`, `delta_q f_S = [z^{N-q}] H R_S L_S`, and
`DD_q(lambda) f_S = [z^{N-q}] H (N - q - lambda - z d/dz)(R_S L_S)` with
`H(z) = nu + sum h_j z^j`, for every `q` and `lambda`, as rational-function identities
(evaluated exactly at a rational point after symbolic differentiation).  The derivations are
implemented from their displayed formulas and their commutators `[DD_p(a), DD_q(b)]`,
`[delta_p, DD_q(b)]` and the coefficient identity are asserted on monomials in
`h_1, ..., h_{p+q+3}`; the line clocks `V_1 h_J = (J-1) h_{J-1}`, `V_1 e_J = -(J-1) e_{J-1}`,
`delta_1 h_J = h_{J-1}`, `delta_1 e_J = e_{J-1}` are checked with `e_J` the Jacobi--Trudi
determinant.  Sampled, not exhaustive: diagrams of span at most 5; commutators for
`1 <= q <= p <= 3`, ten random monomials per pair and clocks in `{-2, 0, 3}`; the coefficient
identity is checked symbolically in `k` for clocks in `[-3, 3]`.
"""
import itertools
import random

import sympy as sp

from check_regroup_mixed import skew_shapes, span, is_connected
from check_contact_currents import beta_lists

NU = sp.Symbol("nu")
RNG = random.Random(5)


def gens(n):
    return sp.symbols(f"h1:{n + 1}")


def make_h(n):
    hs = gens(n)

    def h(j):
        return sp.Integer(0) if j < 0 else (NU if j == 0 else hs[j - 1])
    return hs, h


def delta(P, s, hs, h):
    return sp.expand(sum(h(j - s) * sp.diff(P, hs[j - 1]) for j in range(max(s, 1), len(hs) + 1)))


def Vop(P, s, hs, h):
    return sp.expand(sum((j - s) * h(j - s) * sp.diff(P, hs[j - 1]) for j in range(max(s, 1), len(hs) + 1)))


def DD(P, s, lam, hs, h):
    return sp.expand(Vop(P, s, hs, h) - lam * delta(P, s, hs, h))


def delta_rat(P, s, hs, h):
    return sum(h(j - s) * sp.diff(P, hs[j - 1]) for j in range(max(s, 1), len(hs) + 1))


def DD_rat(P, s, lam, hs, h):
    return sum(((j - s) - lam) * h(j - s) * sp.diff(P, hs[j - 1]) for j in range(max(s, 1), len(hs) + 1))


def check_schur_complement_coframes(max_span):
    n = 0
    for S in skew_shapes(max_span + 3, 3, 4):
        if len(S) < 2 or span(S) > max_span:
            continue
        X, Y = beta_lists(S)
        N = X[0]
        hs, h = make_h(N)
        I = list(X[1:])
        C = list(Y[:-1])
        A = sp.Matrix(len(I), len(C), lambda i, j: h(I[i] - C[j]))
        b = sp.Matrix([h(i) for i in I])
        w = sp.Matrix([[h(N - j) for j in C]])
        full = sp.Matrix(len(X), len(Y), lambda i, j: h(X[i] - Y[j]))
        s = sp.expand(full.det())
        if I:
            Ainv = A.inv()
            f = h(N) - (w * Ainv * b)[0, 0]
            Ab = Ainv * b
            wA = w * Ainv
        else:
            f, Ab, wA = h(N), sp.zeros(0, 1), sp.zeros(1, 0)
        pt = {hh: sp.Rational(RNG.randint(1, 30), RNG.randint(1, 9)) for hh in hs}
        pt[NU] = sp.Rational(RNG.randint(2, 30), RNG.randint(1, 9))
        assert (f - s / sp.diff(s, hs[N - 1])).subs(pt) == 0                   # eq:schur-complement
        z = sp.Symbol("z")
        R = 1 - sum((Ab[k] * z ** C[k] for k in range(len(C))), sp.Integer(0))
        L = 1 - sum((wA[0, k] * z ** (N - I[k]) for k in range(len(I))), sp.Integer(0))
        RL = sp.expand(R * L)
        for m in range(1, N + 1):
            lhs = sp.diff(f, hs[m - 1]).subs(pt)
            rhs = sp.Poly(RL, z).coeff_monomial(z ** (N - m)).subs(pt) if N - m >= 0 else 0
            assert lhs - rhs == 0, (sorted(S), m)               # eq:gradient-product
        Hz = NU + sum(hs[j - 1] * z ** j for j in range(1, N + 1))
        for q in range(1, N):
            mm = N - q
            O_H = sp.Poly(sp.expand(Hz * RL), z).coeff_monomial(z ** mm)
            assert (delta_rat(f, q, hs, h) - O_H).subs(pt) == 0     # O_H = delta_q f
            for lam in (-2, 0, 3):
                Th = sp.expand(mm * RL - z * sp.diff(RL, z))                  # (m - Theta_z)(R L)
                O_l = sp.Poly(sp.expand(Hz * (Th - lam * RL)), z).coeff_monomial(z ** mm)
                assert (DD_rat(f, q, lam, hs, h) - O_l).subs(pt) == 0   # eq:whole-observers
        n += 1
    return n


def check_commutators():
    count = 0
    for p in range(1, 4):
        for q in range(1, p + 1):
            top = p + q + 3
            hs, h = make_h(top)
            pool = [sp.Mul(*[hs[j - 1] ** e for j, e in zip(js, es)]) for js in
                    itertools.combinations(range(1, top + 1), 2) for es in ((1, 1), (2, 1))]
            monos = RNG.sample(pool, 10)
            monos += [hs[top - 1], hs[p + q - 1] * hs[1], sp.Integer(1)]
            for P in monos:
                for al, be in itertools.product((-2, 0, 3), repeat=2):
                    lhs = DD(DD(P, q, be, hs, h), p, al, hs, h) - DD(DD(P, p, al, hs, h), q, be, hs, h)
                    rhs = (p - q) * Vop(P, p + q, hs, h) + (q * be - p * al) * delta(P, p + q, hs, h)
                    assert sp.expand(lhs - rhs) == 0, (p, q, al, be, P)
                    c1 = delta(DD(P, q, be, hs, h), p, hs, h) - DD(delta(P, p, hs, h), q, be, hs, h)
                    assert sp.expand(c1 - p * delta(P, p + q, hs, h)) == 0
                    count += 1
            k = sp.Symbol("k")
            for al, be in itertools.product(range(-3, 4), repeat=2):
                assert sp.expand((k + p - be) * (k - al) - (k + q - al) * (k - be)
                                 - ((p - q) * k + q * be - p * al)) == 0
    return count


def check_line_clocks():
    n = 0
    for J in range(2, 7):
        hs, _ = make_h(J)

        def h(j, hs=hs):
            return sp.Integer(0) if j < 0 else (sp.Integer(1) if j == 0 else hs[j - 1])   # physical h_0 = 1
        e = sp.Matrix(J, J, lambda i, j: h(1 - i + j)).det()
        hJ = hs[J - 1]
        eJm = sp.Matrix(J - 1, J - 1, lambda i, j: h(1 - i + j)).det()
        assert sp.expand(Vop(hJ, 1, hs, h) - (J - 1) * hs[J - 2]) == 0
        assert sp.expand(delta(hJ, 1, hs, h) - hs[J - 2]) == 0
        assert sp.expand(Vop(sp.expand(e), 1, hs, h) + (J - 1) * eJm) == 0
        assert sp.expand(delta(sp.expand(e), 1, hs, h) - eJm) == 0
        n += 1
    return n


def main():
    nd = check_schur_complement_coframes(5)
    nc = check_commutators()
    nk = check_line_clocks()
    print(f"diagrams {nd}, commutator cases {nc}, line clocks J=2..{nk + 1}")
    assert nd > 0 and nc > 0 and nk > 0
    print("PASS")


if __name__ == "__main__":
    main()
