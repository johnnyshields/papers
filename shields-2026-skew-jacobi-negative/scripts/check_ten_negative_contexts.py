"""Symbolic exceptional-core response and row-multiset checks.

Checks the proof's identities, row-multiset possibilities, and exceptional
interfaces rather than enumerating an unrestricted mate space.
"""
from collections import Counter
from itertools import combinations, permutations
import sympy as sp
from check_ten_negative_algebra import (add, coefficient, context, det, determinant,
    endpoint, firing_control, five_cores, mul, profile, rotate, times, top)


def V(name):
    return {(name,): 1}


def prod(*names):
    return {tuple(sorted(names)): 1}


def response_matrix(i, kind, direction):
    rows = []
    for row, r in enumerate(range(4, -1, -1)):
        entries = ([('a', r-3), ('b', r-1), ('a', r-1), ('b', r), ('a', r)] if (i, kind) == (1, 'F') else
                   [('b', r-2), ('a', r-2), ('a', r-1), ('b', r), ('a', r)] if (i, kind) == (1, 'H') else
                   [('b', r-3), ('b', r-1), ('a', r-1), ('b', r), ('a', r)] if kind == 'F' else
                   [('b', r-2), ('a', r-2), ('b', r-1), ('b', r), ('a', r)])
        rows.append(tuple(None if j < 0 else f'{letter}{j}'+('t' if (direction == 'up' and row == 0) or (direction == 'down' and col == 4) else '')
                          for col, (letter, j) in enumerate(entries)))
    return tuple(rows)


def D_polynomials():
    D1 = add((1, prod('a0', 'a0', 'b2')), (-1, prod('a0', 'a1', 'b1')),
             (-1, prod('a0', 'a2', 'b0')), (1, prod('a1', 'a1', 'b0')))
    D2 = add((1, prod('a0', 'b0', 'b2')), (-1, prod('a0', 'b1', 'b1')),
             (1, prod('a1', 'b0', 'b1')), (-1, prod('a2', 'b0', 'b0')))
    W = add((1, prod('a0', 'b1')), (-1, prod('a1', 'b0')))
    assert not add((1, mul(V('b0'), D1)), (-1, mul(V('a0'), D2)), (-1, mul(W, W)))
    return D1, D2, W


def check_responses(wrong_sign=False):
    D1, D2, W = D_polynomials()
    for i, Di, Ki in ((1, D1, prod('a0', 'a0')), (2, D2, prod('a0', 'b0'))):
        P = {(kind, direction): determinant(response_matrix(i, kind, direction))
             for kind in ('F', 'H') for direction in ('up', 'down')}
        U = add((1, P['F', 'up']), (-1, P['H', 'up']))
        VV = add((1, P['F', 'down']), (-1, P['H', 'down']))
        C = add((1, U), (1, VV))
        sign = 1 if wrong_sign else -1
        assert coefficient(U, 'a3t') == add((sign, mul(V('b0'), Di)))
        assert coefficient(VV, 'a3t') == mul(V('b0'), Di)
        assert coefficient(C, 'b3t') == mul(V('a0'), Di)
        for D in (U, VV):
            names = {j for m in D for j in m}
            assert not names & {'a4t', 'b4t', 'a4', 'b4'}
        assert not any('a3t' in m for m in C)
        for left, right in (('H', 'F'), ('F', 'H')):
            mixed = add((1, P[left, 'up']), (-1, P[right, 'down']))
            assert coefficient(mixed, 'b4t') == add((-1, mul(Ki, W)))
            assert not any('a4t' in m or 'a4' in m for m in mixed)
    print('PASS: both generic endpoint-coefficient tables and b0*D1-a0*D2=W^2')


def check_row_table():
    p, q, G, A, v, s, u = sp.symbols('p q G A v s u')
    for i in (1, 2):
        F, H = five_cores(i, p, q, G)
        names = {'F': F, 'H': H, 'Fs': rotate(*F), 'Hs': rotate(*H)}
        expected = {
            ('F', 'H'): [(A-G,)],
            ('Fs', 'Hs'): [(v-G,)],
            ('F', 'Hs'): [(A-G, v-G), (A-(3*G-q), v-(2*G if i == 1 else 2*G-q))],
            ('H', 'Fs'): [(A-G, v-G), (A-(2*G if i == 1 else 2*G-q), v-(3*G-q))],
        }
        rows = {name: Counter(sp.expand(x) for x in profile(*context(*Q, s, u, v, A-s))[0])
                for name, Q in names.items()}
        for pair, allowed in expected.items():
            left, right = rows[pair[0]], rows[pair[1]]
            common = left & right
            a, b = list((left-common).elements()), list((right-common).elements())
            assert len(a) == len(b) in (2, 3)
            feasible = 0
            for perm in permutations(b):
                equations = [sp.expand(x-y) for x, y in zip(a, perm)]
                M, rhs = sp.linear_eq_to_matrix(equations, (A, v))
                constraints = [sp.expand((z.T*rhs)[0]) for z in M.T.nullspace()]
                constraints = [c for c in constraints if c != 0]
                # Do not lose a permissible special ratio such as G=2q by treating
                # the parameters as generic. Consistency conditions are linear.
                ratios = [None]
                if constraints:
                    R = sp.Symbol('R')
                    eqs = [c.subs({G: R, q: 1}) for c in constraints]
                    solutions = sp.solve(eqs, (R,), dict=True)
                    ratios = [sol[R] for sol in solutions if R in sol and sol[R].is_Rational and sol[R] > 1]
                for ratio in ratios:
                    sub = {} if ratio is None else {G: ratio*q}
                    solutions = sp.linsolve((M, rhs.subs(sub)), (A, v))
                    for aa, vv in solutions:
                        assert any(all(sp.expand(c.subs(sub).subs({A: aa, v: vv}, simultaneous=True)) == 0
                                       for c in alternative) for alternative in allowed), (i, pair, equations, ratio, aa, vv)
                        feasible += 1
            assert feasible
            # Verify sufficiency of each listed row-multiset locus as well.
            for conditions in allowed:
                substitution = sp.solve(conditions, (A, v), dict=True)[0]
                la = Counter(sp.expand(x.subs(substitution)) for x in left.elements())
                lb = Counter(sp.expand(x.subs(substitution)) for x in right.elements())
                assert la == lb
    print('PASS: all four row-multiset pairings, including parameter-ratio degeneracies')


def endpoint_delta(Q, R, t, up):
    return add((1, det(*endpoint(*Q, t, up))), (-1, det(*endpoint(*R, t, up))))


def check_interface():
    for i, p, q, G in ((1, 4, 1, 7), (2, 3, 2, 6), (2, 2, 1, 4)):
        F, H = five_cores(i, p, q, G)
        cores = [F, H, rotate(*F), rotate(*H)]
        S = F[0][0]
        for s, A, u in ((1, 3, 1), (2, 5, 2)):
            for v in (u+1, A+u, A+u+2):
                assert u < v and s < A
                polynomials = [det(*context(*Q, s, u, v, A-s)) for Q in cores]
                for j, k in combinations(range(4), 2):
                    Delta = add((1, polynomials[j]), (-1, polynomials[k]))
                    Q, R = cores[j], cores[k]
                    if v < A+u:
                        assert top(Delta) == S+A+u
                    elif v > A+u:
                        expected = add((1, times(endpoint_delta(Q, R, A, True), s+u)),
                                       (-1, times(endpoint_delta(Q, R, A+u, True), s)))
                        assert expected and top(Delta) == S+v
                        assert coefficient(Delta, S+v) == expected
                    else:
                        expected = add((1, times(endpoint_delta(Q, R, A, True), s+u)),
                                       (-1, times(endpoint_delta(Q, R, v, True), s)),
                                       (-1, times(endpoint_delta(Q, R, v, False), s)))
                        assert not coefficient(Delta, S+v, 2)
                        assert coefficient(Delta, S+v) == expected
        # The surviving locus; this compares only the four recovered cores.
        params = (p-q, q, G, G-p)
        assert det(*context(*cores[2], *params)) == det(*context(*cores[3], *params))
    print('PASS: forced-interface coefficients for all six core pairs and the surviving starred-pair locus')


def check_secondary_tie():
    a0, a1, a2, b0, b1, b2 = sp.symbols('a0 a1 a2 b0 b1 b2')
    D2 = a0*b0*b2-a0*b1**2+a1*b0*b1-a2*b0**2
    W = a0*b1-a1*b0
    assert sp.expand(a1*D2-a2*b0*W).coeff(a2) == -a0*b0*b1
    # Admissible secondary tie p+q<G: s=p+G < A=2G-q.
    i, p, q, G = 2, 2, 1, 5
    F, H = five_cores(i, p, q, G)
    s, A, v, u = p+G, 2*G-q, 3*G-q, G
    assert 0 < s < A and v == A+u
    assert det(*context(*H, s, u, v, A-s)) != det(*context(*rotate(*F), s, u, v, A-s))
    print('PASS: secondary mixed-orientation tie has coefficient -a0*b0*b1, not zero')


def wrong_locus():
    F, H = five_cores(1, 4, 1, 7)
    # False claim obtained by dropping u=q while retaining the forced interface.
    s, u, v, g = 3, 2, 8, 3
    assert det(*context(*rotate(*F), s, u, v, g)) == det(*context(*rotate(*H), s, u, v, g))


if __name__ == '__main__':
    check_responses()
    check_row_table()
    check_interface()
    check_secondary_tie()
    firing_control('wrong sign in the up-response table', lambda: check_responses(True))
    firing_control('dropped u=q from the exceptional locus', wrong_locus)
    print('ALL PASS')
