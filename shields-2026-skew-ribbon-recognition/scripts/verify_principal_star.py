r"""Paper section `app:endpoints` (Endpoint scalars and ordinary reflection), rt:principal-star.

E = V o_mu J and U = V' o_mu J are compositions through the same positive ordinary (a) mark of
period r, width v, with V, V' connected of one span M >= 3, equal skew Schur function (the common
coarse function), equal source function s_E = s_U, 0 <= w < v < r and Q = M r + v - w.  The lemma:
if the global contractions G_Q(E) = (adj(A_E) K_Q adj(A_E))_{0,S} and G_Q(U) agree, then V' = V or
V' = V* (half-turn).

Candidates are enumerated, not chosen: every J up to CELLS cells with a positive case (a) mark with
v < r, every connected V of span M >= 3 up to COARSE cells, every V' with schur(V') = schur(V).  The
polynomial equalities s_E = s_U and G_Q(E) = G_Q(U) are tested at SAMPLES random integer points of the
letters h_i (a disagreement refutes equality exactly; agreement at all points is taken as equality,
so a false agreement could only make the final assertion fail, never pass).  Non-vacuity: the number
of pairs with V' != V, V* that pass the hypotheses is reported (the lemma says the contraction
separates them, so the count of equal contractions among them must be zero), together with the
number of V' = V* pairs whose contractions agree.
"""
import random

import sympy as sp

from _gluing_common import compose, normalize, rotate, schur, span
from check_two_copy_flags import betas, diagrams, marks, phases

CELLS = 3
COARSE = 7
SAMPLES = 2


def contraction(E, Q, hv):
    X, Y = betas(E)
    S = X[0]
    A = sp.Matrix(len(X), len(Y), lambda i, j: hv(X[i] - Y[j]))
    K = sp.Matrix(len(X), len(Y), lambda i, j: hv(Q + X[i] - Y[j]))
    adj = A.adjugate()
    return (adj * K * adj)[Y.index(0), X.index(S)], A.det()


def main():
    rng = random.Random(11)
    coarse = [V for V in diagrams(COARSE) if span(V) >= 3]
    by_function = {}
    for V in coarse:
        by_function.setdefault((span(V), schur(V)), []).append(V)
    pairs = same = other = star_equal = star_total = 0
    for J in diagrams(CELLS):
        for mu in marks(J):
            if mu.case != 'a' or not mu.lower or mu.width >= mu.period:
                continue
            r, v = mu.period, mu.width
            for group in by_function.values():
                if len(group) < 2:
                    continue
                M = span(group[0])
                for V in group:
                    for V2 in group:
                        if V == V2:
                            continue
                        E, U = compose(V, mu), compose(V2, mu)
                        for w in range(0, v):
                            Q = M * r + v - w
                            points = []
                            for _ in range(SAMPLES):
                                size = 2 * (M * r + v) + Q + 4
                                hs = [None] + [sp.Integer(rng.randint(1, 6)) for _ in range(size)]
                                points.append(lambda i, hs=hs: 0 if i < 0 else 1 if i == 0 else hs[i])
                            equal_s = equal_g = True
                            for hv in points:
                                gE, dE = contraction(E, Q, hv)
                                gU, dU = contraction(U, Q, hv)
                                equal_s &= dE == dU
                                equal_g &= gE == gU
                            if not equal_s:
                                continue
                            pairs += 1
                            is_star = V2 == normalize(rotate(V))
                            if is_star:
                                star_total += 1
                                star_equal += equal_g
                            if equal_g:
                                assert is_star, (sorted(J), sorted(V), sorted(V2), w)
                            else:
                                other += 1
    assert pairs > 0 and star_total > 0
    print(f'rt:principal-star: {pairs} (J, mark, V, V\', w) with equal source function and coarse '
          f'function; contractions agree only for V\' = V*: {star_equal} of {star_total} V* pairs agree, '
          f'{other} disagreeing pairs')
    print('ALL PASS')


if __name__ == '__main__':
    main()
