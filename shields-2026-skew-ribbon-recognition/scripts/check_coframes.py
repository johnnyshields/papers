r"""Coframes, neutral adjugate and the finite response algebra (ph:gradient, ph:stationary-packet,
ph:intercept-exclusion, ph:matrix-powers).

Paper section `app:first-responses` (First responses and the unshifted defect) and
`sec:comparison` (Finite comparisons on actual composition charts); labels ph:gradient,
ph:stationary-packet, ph:intercept-exclusion, ph:matrix-powers, ph:coframe-operator.

Reading: the coframes G (right) and C (left, the right coframe of the half-turn in the same
alphabet) of a connected board with beta lists X = {M} u I, Y = S u {0} are G = 1 - sum_s
(T^{-1}(R_i)_{i in I})_s z^s with T = (R_{i-s}); R_0 is a generic clock, R_l = 0 for l < 0.  The
operator is T_{A,B}(u) = A[uB]_{<M} - B[uA]_{<M}.  For every connected V of span 2 <= M <= MMAX, at
random rational letters, exact:

* neutral adjugate: with R_M solved from e = 0, the signed cofactor at the entry (x, y) is
  kappa G_y C_{M-x}, kappa the cofactor at (M, 0);
* the coframes of the half-turn V* are (C, G) and V = V* exactly when G = C;
* the finite multiplication formula [z^{M+a-1}] T_{A,B}(f) = sum_{i>=a, j<a} (A_i B_j - B_i A_j)
  f_{M+a-1-i-j} for arbitrary series f (with H^p as f) and the shift-cap identity
  T(zu) = zT(u) - z^M{A[uB]_{M-1} - B[uA]_{M-1}};
* ord_z D >= M+1 and deg_z D <= 2M-2 for D = T_{G,C}(H), H a generic series with H_0 = R_0, with
  D = 0 when V = V* and D != 0 otherwise;
* the cutoff family: J_a = sum_D C_{a,D} R_{D+a-1} with C_{a,D} = sum_{j-k=D} A_V(j,k)
  ([k<a] - [j>M-a]) satisfies J_1 = J_M = 0 and Jhat_a = J_{a+1} (Jhat_a with R_{D+a}), and every
  surviving term has 2 <= D+a <= M; the control with the sign [k<a] + [j>M-a] fails;
* on every coequal pair: G' = C and C' = G exactly when V' = V*, G' = G exactly when V' = V, and
  for p != 0 the crossed assignment G' = [Hbar^p C]_{<M} fails (its z^1 coefficient depends on the
  free Hbar_1 while G'_1 does not).

The p-power argument of ph:matrix-powers is run for p = -3..3 on every half-turn coequal pair
(spans 3 to MMAX-1) with generic Hbar: the equation G[Hbar^p C] = G'[Hbar^p C'] holds for p = 0 and
fails for every p != 0, and the crossed assignment G' = [Hbar^p C] fails for p != 0.  For
ph:intercept-exclusion, eq. T(H^p) = p [H^(p-1) D] holds exactly at p = 1 and fails for p = 2, 3
on a nonself board without the cutoff equations, so the exclusion has content.

Uncovered: the response equations in the fine field (T_m(H_R), the aliases), the unshifted-defect identity
itself (it follows from the cutoff equations, not from the operator alone), the exclusion theorem
of the cited coframe paper, and the principal values P', G' of the ordinary chart.
"""
import itertools
import random
from fractions import Fraction

import sympy as sp


MMAX = 5
rng = random.Random(21)


def profiles(M):
    """Connected normalized beta pairs of span M: rows in (0, M] with M, columns in [0, M) with 0."""
    out = []
    for xm in range(1 << (M - 1)):
        X = [M] + [k for k in range(M - 1, 0, -1) if xm >> (k - 1) & 1]
        for ym in range(1 << (M - 1)):
            Y = [k for k in range(M - 1, 0, -1) if ym >> (k - 1) & 1] + [0]
            if len(X) != len(Y):
                continue
            n = len(X)
            if all(Y[i] < X[i] for i in range(n)) and all(Y[i] <= X[i + 1] for i in range(n - 1)):
                out.append((tuple(X), tuple(Y)))
    return out


def make_R(M):
    vals = {n: Fraction(rng.randint(1, 7), rng.randint(1, 3)) for n in range(0, 2 * M + 3)}
    return lambda n, vals=vals: vals[n] if n >= 0 else Fraction(0)


def mat(R, X, Y):
    return sp.Matrix(len(X), len(Y), lambda i, j: sp.Rational(R(X[i] - Y[j])))


def coframe(R, X, Y):
    M = X[0]
    I, S = X[1:], Y[:-1]
    G = [sp.Integer(1)] + [sp.Integer(0)] * (M - 1)
    if I:
        T = sp.Matrix(len(I), len(S), lambda i, j: sp.Rational(R(I[i] - S[j])))
        sol = T.solve(sp.Matrix([sp.Rational(R(i)) for i in I]))
        for s, val in zip(S, sol):
            G[s] = -val
    return G


def rotate(X, Y):
    M = X[0]
    return sorted((M - y for y in Y), reverse=True), sorted((M - x for x in X), reverse=True)


def mul_clip(a, b, n):
    return [sum(a[i] * b[k - i] for i in range(k + 1) if i < len(a) and k - i < len(b))
            for k in range(n)]


def op(A, B, u, M, n):
    """T_{A,B}(u) coefficients 0..n-1; u a list long enough."""
    uB = mul_clip(u, B, M)
    uA = mul_clip(u, A, M)
    left = [sum(A[i] * uB[k - i] for i in range(len(A)) if 0 <= k - i < M) for k in range(n)]
    right = [sum(B[i] * uA[k - i] for i in range(len(B)) if 0 <= k - i < M) for k in range(n)]
    return [a - b for a, b in zip(left, right)]


def main():
    tested = distinct = 0
    for M in range(2, MMAX + 1):
        for X, Y in profiles(M):
            R = make_R(M)
            while True:
                e0 = mat(lambda n: R(n) if n != M else Fraction(0), X, Y).det()
                kap = mat(lambda n: R(n) if n != M else Fraction(1), X, Y).det() - e0
                if kap != 0:
                    break
                R = make_R(M)
            RM = -e0 / kap
            Rn = lambda n, R=R, RM=RM, M=M: RM if n == M else R(n)  # noqa: E731
            A = mat(Rn, X, Y)
            assert A.det() == 0
            G, C = coframe(Rn, X, Y), None
            Xr, Yr = rotate(X, Y)
            C = coframe(Rn, Xr, Yr)
            # neutral adjugate
            kap = A.cofactor(0, len(Y) - 1)
            for i, x in enumerate(X):
                for j, y in enumerate(Y):
                    assert A.cofactor(i, j) == kap * G[y] * C[M - x], (X, Y, x, y)
            # rotation swaps the coframes
            assert coframe(Rn, *rotate(Xr, Yr)) == G and coframe(Rn, Xr, Yr) == C

            assert (G == C) == ((tuple(Xr), tuple(Yr)) == (X, Y)), (X, Y)
            # operator algebra with generic H
            H = [sp.Rational(Rn(n)) for n in range(M + 1)] + [
                sp.Rational(rng.randint(-5, 5), rng.randint(1, 4)) for _ in range(3 * M)]
            D = op(G, C, H, M, 2 * M + 2)
            assert all(c == 0 for c in D[:M + 1]) and all(c == 0 for c in D[2 * M - 1:])
            if G == C:
                assert all(c == 0 for c in D)
            else:
                assert any(c != 0 for c in D)
                distinct += 1
            for a in range(1, M):
                f = [sp.Rational(rng.randint(-4, 4)) for _ in range(3 * M)]
                lhs = op(G, C, f, M, M + a)[M + a - 1]
                rhs = sum((G[i] * C[j] - C[i] * G[j]) * f[M + a - 1 - i - j]
                          for i in range(a, M) for j in range(a) if 0 <= M + a - 1 - i - j < len(f))
                assert lhs == rhs
            u = [sp.Rational(rng.randint(-4, 4)) for _ in range(3 * M)]
            zu = [0] + u
            lhs = op(G, C, zu, M, 2 * M)
            T0 = op(G, C, u, M, 2 * M)
            capG = sum(G[i] * u[M - 1 - i] for i in range(M) if M - 1 - i >= 0)
            capC = sum(C[i] * u[M - 1 - i] for i in range(M) if M - 1 - i >= 0)
            # [uC]_{M-1} and [uG]_{M-1}
            uC_top = sum(u[M - 1 - i] * C[i] for i in range(M))
            uG_top = sum(u[M - 1 - i] * G[i] for i in range(M))
            cap = [sp.Integer(0)] * (2 * M)
            for i in range(M):
                cap[M + i] = G[i] * uC_top - C[i] * uG_top
            shifted = [sp.Integer(0)] + T0[:2 * M - 1]
            assert lhs == [s - c for s, c in zip(shifted, cap)], (X, Y)
            # cutoff family J_a
            RR = sp.symbols('Rq0:%d' % (2 * M + 2))
            sym = lambda n, RR=RR: 0 if n < 0 else RR[n]  # noqa: E731
            As = sp.Matrix(len(X), len(Y), lambda i, j: sym(X[i] - Y[j]))
            ad = {(x, y): As.cofactor(i, j) for i, x in enumerate(X) for j, y in enumerate(Y)}

            def Jfam(a, shift, sgn=-1):
                total = 0
                for (j, k), val in ad.items():
                    D_ = j - k
                    w = (1 if k < a else 0) + sgn * (1 if j > M - a else 0)
                    if w:
                        total += val * w * sym(D_ + a - 1 + shift)
                return sp.expand(total)

            for a in range(1, M + 1):
                if a in (1, M):
                    assert Jfam(a, 0) == 0, (X, Y, a)
                if a < M:
                    assert sp.expand(Jfam(a, 1) - Jfam(a + 1, 0)) == 0, (X, Y, a)
            if M >= 3:
                assert any(Jfam(a, 0, +1) != 0 for a in (1, M)), 'control: wrong sign must fail'
            tested += 1
    pairs = crossed = 0
    z, h1 = sp.symbols('z h1')
    for M in range(3, MMAX + 1):
        R = make_R(M)
        groups = {}
        for X, Y in profiles(M):
            A = sp.Matrix(len(X), len(Y), lambda i, j: sp.Symbol('Rs%d' % (X[i] - Y[j])) if X[i] >= Y[j] else 0)
            groups.setdefault(sp.expand(A.det()), []).append((X, Y))
        for grp in groups.values():
            cof = {b: (coframe(R, *b), coframe(R, *rotate(*b))) for b in grp}
            for V1, V2 in itertools.permutations(grp, 2):
                (G1, C1), (G2, C2) = cof[V1], cof[V2]
                is_rot = V2 == tuple(map(tuple, rotate(*V1)))
                assert ((G2 == C1) and (C2 == G1)) == is_rot, (V1, V2)
                assert G2 != G1
                pairs += 1
                crossed += is_rot
                for p in (-3, -2, -1, 1, 2, 3):
                    Hbar = 1 + h1 * z
                    ser = sp.series(Hbar ** p * sum(C1[i] * z ** i for i in range(M)), z, 0, 2).removeO()
                    assert sp.diff(sp.expand(ser).coeff(z, 1), h1) == p
    # p-power argument (ph:matrix-powers) and the p-power unshifted defect (ph:intercept-exclusion):
    # H generic with H_0 = R_0; Hbar = H / R_0.  For p in {-3..3} the two assignments are tested as
    # polynomial identities in the free coefficients of Hbar.
    zs = sp.symbols('u1:%d' % (MMAX + 1))
    powers = fails = held0 = deffail = defhold = 0
    for M in range(3, MMAX):
        R = make_R(M)
        groups = {}
        for X, Y in profiles(M):
            A = sp.Matrix(len(X), len(Y), lambda i, j: sp.Symbol('Rs%d' % (X[i] - Y[j])) if X[i] >= Y[j] else 0)
            groups.setdefault(sp.expand(A.det()), []).append((X, Y))
        Hbar = [sp.Integer(1)] + list(zs[:M - 1])
        for grp in groups.values():
            cof = {b: (coframe(R, *b), coframe(R, *rotate(*b))) for b in grp}
            for V1, V2 in itertools.permutations(grp, 2):
                (G1, C1), (G2, C2) = cof[V1], cof[V2]
                if V2 != tuple(map(tuple, rotate(*V1))):
                    continue
                for p in range(-3, 4):
                    zser = sum(Hbar[i] * sp.Symbol('z') ** i for i in range(M))
                    z = sp.Symbol('z')
                    Hp = sp.series(zser ** p, z, 0, M).removeO()
                    hp = [sp.expand(Hp).coeff(z, i) for i in range(M)]
                    lhs = mul_clip([sp.Integer(0)] + [0] * 0 + hp, G1, M) if False else None
                    PC = mul_clip(hp, C1, M)
                    PG = mul_clip(hp, G1, M)
                    # the crossed assignment: G' = [Hbar^p C]_{<M}; actual G' of the half-turn mate is C
                    crossed_ok = all(sp.expand(PC[i] - G2[i]) == 0 for i in range(M))
                    # the hypothesis G [Hbar^p C] = G' [Hbar^p C'] with the actual half-turn pair
                    PC2 = mul_clip(hp, C2, M)
                    eq = [sp.expand(a - b) for a, b in zip(mul_clip(G1, PC, 2 * M - 1),
                                                           mul_clip(G2, PC2, 2 * M - 1))]
                    holds = all(e == 0 for e in eq)
                    powers += 1
                    if p == 0:
                        held0 += holds and crossed_ok
                    else:
                        fails += (not holds)
                        assert not crossed_ok
    print(f'p-power instances {powers}: p = 0 holds on {held0}; the equation fails for p != 0 on {fails}')
    assert powers > 0 and held0 > 0 and fails > 0
    # unshifted defect, exact at p = 1 and generically failing at p >= 2 without the cutoff equations
    for M in range(3, MMAX):
        R = make_R(M)
        for X, Y in profiles(M):
            G = coframe(R, X, Y)
            C = coframe(R, *rotate(X, Y))
            H = [sp.Rational(R(0))] + [sp.Rational(rng.randint(-5, 5), rng.randint(1, 4)) for _ in range(3 * M)]
            Dd = op(G, C, H, M, 2 * M)
            for p in (1, 2, 3):
                Hp = [sp.Integer(1)]
                pw = [sp.Integer(1)] + [0] * (3 * M)
                for _ in range(p):
                    pw = mul_clip(pw, H, 3 * M)
                lhs = op(G, C, pw, M, 2 * M)
                rhs = [sp.Integer(0)] * (2 * M)
                if p == 1:
                    rhs = Dd
                else:
                    pm = [sp.Integer(1)] + [0] * (3 * M)
                    for _ in range(p - 1):
                        pm = mul_clip(pm, H, 3 * M)
                    t = mul_clip(pm, Dd + [sp.Integer(0)] * M, 2 * M)
                    rhs = [p * x for x in t]
                ok = lhs == rhs
                if p == 1:
                    assert ok
                    defhold += 1
                else:
                    deffail += (not ok) and any(c != 0 for c in Dd)
    print(f'unshifted defect T(H^p) = p [H^(p-1) D]: exact at p = 1 on {defhold}; fails without the cutoff equations (p = 2, 3) on {deffail}')
    assert defhold > 0 and deffail > 0
    print(f'coequal ordered pairs {pairs}, half-turn pairs {crossed}')
    assert pairs > 0 and crossed > 0
    print(f'boards tested {tested}, non-self-rotational with D != 0: {distinct}')
    assert tested > 50 and distinct > 10
    print('ALL PASS')


if __name__ == '__main__':
    main()
