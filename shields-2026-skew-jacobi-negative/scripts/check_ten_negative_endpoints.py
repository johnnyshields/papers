"""Symbolic endpoint identities and the one-negative placement replacements."""
from itertools import product
import sympy as sp
from check_ten_negative_algebra import (add, border, coefficient, connected, context,
    det, determinant, difference, endpoint, evaluate, firing_control, h, lists,
    mul, negative_partition, profile, rotate, times, top)


def formal(expr):
    return str(sp.expand(expr))


def var(expr):
    return {(formal(expr),): 1}


def check_four_alternants(include_open=True):
    b, q, c, d, u, w, sig, t = sp.symbols('b q c d u w sigma t')
    x, y, z = b+c+u, c+d-sig, b+d+w
    XX, YY = lists((b+q, x, y, z, b+q), (b, c, d, b))
    mask = {(2, 0), (3, 0), (4, 0), (4, 1), (4, 2)}
    def shifted(up):
        X, Y = endpoint(XX, YY, t, up)
        return determinant(tuple(tuple(None if (i, j) in mask else formal(a-v)
            for j, v in enumerate(Y)) for i, a in enumerate(X)))
    actual = add((1, shifted(True)), (-1, shifted(False)))
    X, Y = x+y-c, y+z-d
    def F(r, s):
        matrix = tuple(tuple(formal(a+offset) for offset in (0, q, q+t)) for a in (b, r, s))
        return add((-1, determinant(matrix)))
    terms = [(1, mul(var(y), F(x, z))), (-1, mul(var(c), F(X, z))),
             (-1, mul(var(d), F(x, Y)))]
    if include_open:
        terms.append((1, mul(var(sig), F(X, Y))))
    expected = mul(var(b), add(*terms))
    assert actual == expected
    print('PASS: generic four-alternant identity as an exact polynomial in formal affine labels')


def check_five_leaders():
    cases = 0
    for b, q, c, d, u, w in product((1, 2), (1, 3), (2, 3), (2, 4), (1, 2), (1, 3)):
        sig = 1
        x, y, z = b+c+u, c+d-sig, b+d+w
        C, D = lists((b+q, x, y, z, b+q), (b, c, d, b))
        assert connected(C, D) and not set(C) & set(D)
        assert sum(negative_partition(C, D)) == 5
        X, Y = x+y-c, y+z-d
        k = max(X, Y)+q
        K = lambda j: add((1, times(h(j), b+q)), (-1, times(h(j+q), b)))
        if (C, D) == rotate(C, D):
            assert not difference(C, D, 1)
            continue
        if X > Y:
            predicted = times(add((1, times(K(z), c)), (-1, times(K(Y), sig))), b)
        elif Y > X:
            predicted = times(add((-1, times(K(x), d)), (1, times(K(X), sig))), b)
        else:
            predicted = times(add((1, times(K(z), c)), (-1, times(K(x), d))), b)
        assert predicted and top(predicted) <= k < C[0]
        for t in (1, 2, 5):
            P = difference(C, D, t)
            assert top(P) == k+t and coefficient(P, k+t) == predicted
        cases += 1
    print('PASS:', cases, 'canceled-boundary five-negative leaders, including X=Y and unequal X,Y')


def check_two_variable_formula():
    a, b, c, d, e, r, t = sp.symbols('a b c d e r t')
    C, D = (a, b, c), (c+r, d, e)
    def specialized(up):
        X, Y = endpoint(C, D, t, up)
        return sp.Matrix([[0 if (i, j) == (2, 0) else X[i]-Y[j]+1
                           for j in range(3)] for i in range(3)]).det()
    assert sp.expand(specialized(True)-specialized(False)-(r-1)*t*((d-e)-(a-b))) == 0
    x, y, z = sp.symbols('x y z')
    for power in (0, 1):
        result = sum(a**power/sp.prod(a-b for b in (x, y, z) if b != a) for a in (x, y, z))
        assert sp.factor(result) == 0
    print('PASS: symbolic rank-two correction and rank-three values at indices -2,-1')


def one_negative_cores():
    cores = []
    for r in (1, 2, 3, 5):
        S = 10+r
        cores += [((S, S-1, 6+r, 5), (5+r, 3, 1, 0)),
                  ((S, S-2, 6+r, 5), (5+r, 3, 1, 0)),
                  ((S+2, S-1, 6+r, 5), (5+r, 3, 1, 0)),
                  ((S, S-1, 7+r, 5), (5+r, 3, 1, 0))]
    cores += [((12+r, 11+r, 8+r, 6), (6+r, 4, 2, 0)) for r in (1, 2, 3)]
    return cores


def check_one_negative_lower(drop_lower=False):
    for C, D in one_negative_cores():
        assert connected(C, D) and not set(C) & set(D)
        assert negative_partition(C, D) == (1,)
        k = max(C[1], C[0]-D[-2])
        f = det(C, D)
        B = det(C[1:], D[:-1])
        assert connected(C[1:], D[:-1]) and negative_partition(C[1:], D[:-1]) == (1,)
        assert all(r < k for r in profile(C, D)[0])
        symmetric = (C, D) == rotate(C, D)
        c0 = None
        for t in (1, 2, 5):
            P = difference(C, D, t)
            if symmetric:
                assert not P
                continue
            c = coefficient(P, k+t)
            assert c and top(P) == k+t
            if c0 is None:
                c0 = c
            assert c == c0
            if drop_lower:
                P = times(c, k+t)
            assert add((1, P), (-1, times(c, k+t)))
            first, last = profile(C, D)[0][0], profile(C, D)[0][-1]
            r = D[0]-C[-1]
            if first == last:
                if r >= 3:
                    assert evaluate(P, lambda j: j+1) == 0
                    assert evaluate(c, lambda j: j+1) != 0
                else:
                    hv = lambda j: sum(2**a*3**b for a in range(j+1) for b in range(j+1-a))
                    assert evaluate(P, hv) == 0
                    assert evaluate(c, hv) != 0
        for ell in (1, k-1, k, k+1, C[0]):
            for u in {1, C[0]-k, max(1, C[0]-ell)}:
                x, v = ell+1, ell+1+u
                Dx, Dv = difference(C, D, x), difference(C, D, v)
                A = add((1, times(det(*endpoint(C, D, x)), ell+u)),
                        (-1, times(f, ell+v)), (-1, times(Dv, ell)))
                B = add((1, times(Dx, ell+u)), (-1, times(Dv, ell)))
                assert A
                assert add((1, B), (-1, times(f, ell+v)))
                assert add((1, B), (1, times(f, ell+v)))
    print('PASS: one-negative lower remainders and both cross-resonance inequalities, including symmetric controls')


def placement(C, D, ell, m, g1, g2, u, v, middle):
    S, L, R = C[0], ell+g1, m+g2
    N = S+L+R+u+v
    if middle:
        X = (N, N-u)+tuple(v+R+c for c in C)+(v+m,)
        Y = (N-u-ell,)+tuple(v+R+d for d in D)+(v, 0)
    else:
        X = (N, N-u, S+R+v)+tuple(v+c for c in C)
        Y = (N-u-ell, S+R+v-m)+tuple(v+d for d in D)+(0,)
    return X, Y


def check_placement_identities():
    for C, D in one_negative_cores()[::4]:
        S, k = C[0], max(C[1], C[0]-D[-2])
        f = det(C, D)
        Phi = lambda a, b: det(*border(C, D, a, b))
        parameters = [(1, 2, 1, 1, 1, 2), (2, 1, 2, 1, 3, 1),
                      (1, 1, 1, 2, 2, 2), (1, 1, 2, 1, k+1, k+2)]
        for ell, m, g1, g2, u, v in parameters:
            L, R = ell+g1, m+g2
            AL = add((1, times(h(m+L), ell+u)), (-1, times(h(m+L+u), ell)))
            E = add((1, mul(AL, Phi(R, v))), (-1, times(Phi(L+R, v), m, ell+u)),
                    (1, times(Phi(L+R+u, v), ell, m)))
            M = add((1, times(Phi(L, R), ell+u, m+v)),
                    (-1, times(Phi(L+u, R), ell, m+v)),
                    (-1, times(Phi(L, R+v), ell+u, m)),
                    (1, times(Phi(L+u, R+v), ell, m)))
            for middle, expected in ((False, E), (True, M)):
                X, Y = placement(C, D, ell, m, g1, g2, u, v, middle)
                assert connected(X, Y) and not set(X) & set(Y)
                assert sum(negative_partition(X, Y)) == 10
                P = det(X, Y)
                assert P == expected
                q, N = min(u, v), X[0]
                fu = det(*endpoint(C, D, q, False))
                if middle:
                    marker = times(f, m, ell+q) if u < v else times(f, ell, m+q) if v < u else add((1, times(f, m, ell+q)), (1, times(f, ell, m+q)))
                else:
                    marker = times(f, m, ell+q) if u < v else times(fu, ell, m) if v < u else add((1, times(f, m, ell+q)), (1, times(fu, ell, m)))
                assert coefficient(P, N-q) == add((-1, marker))
                RC, RD = rotate(C, D)
                if middle and g1 > g2 and ell == m and L+u == R+v:
                    assert P != det(*placement(RC, RD, ell, m, g1, g2, u, v, middle))
            x = L
            U = ((S+x+u, S+x)+C[1:], (S+x-ell,)+D[:-1]+(0,))
            assert connected(*U) and negative_partition(*U) == (2, 1, 1)
            assert negative_partition(*rotate(*U)) == (3, 1)
            assert det(*U) == add((1, times(det(*endpoint(C, D, x)), ell+u)),
                                  (-1, times(det(*endpoint(C, D, x+u)), ell)))
    print('PASS: one-negative end/middle polynomial identities, first-marker table, hook intermediates, and final orientation tie')


if __name__ == '__main__':
    check_four_alternants()
    check_five_leaders()
    check_two_variable_formula()
    check_one_negative_lower()
    check_placement_identities()
    firing_control('deleted opened-cell alternant', lambda: check_four_alternants(False))
    firing_control('deleted one-negative endpoint lower remainder', lambda: check_one_negative_lower(True))
    print('ALL PASS')
