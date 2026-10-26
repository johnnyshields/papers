"""Quartet upper-inclusion data, formal border separators, and assembly checks."""
from collections import Counter
from itertools import product
import sympy as sp
from check_ten_negative_algebra import (add, border, coefficient, connected, det,
    determinant, firing_control, five_cores, gamma, lists, minimum,
    negative_partition, normalize, profile, rotate, signed_permutations)


def family(kind, a, b, d, mate=False):
    if kind == 'A':
        r = ((a+d, b+d, a+b+d, 2*b+d, a+2*b+d, 3*b+d, 2*b+d) if mate else
             (a+d, b+d, a+b+d, 2*b+d, 2*b+d, a+2*b+d, 3*b+d))
        z = ((d, a+d, b+d, a+b+d, 2*b+d, b+d) if mate else
             (d, a+d, b+d, b+d, a+b+d, 2*b+d))
    else:
        r = ((a+d, b+d, a+b+d, 2*b+d, a+2*b+d, 3*b+d, a+2*b+d) if mate else
             (a+d, b+d, a+b+d, 2*b+d, a+2*b+d, a+2*b+d, 3*b+d))
        z = ((d, a+d, b+d, a+b+d, 2*b+d, a+b+d) if mate else
             (d, a+d, b+d, a+b+d, a+b+d, 2*b+d))
    return lists(r, z)


def formals(kind, mate=False, bordered=False):
    if kind == 'A':
        rows = [('V', 6), ('U', 6), ('V', 5), ('U', 5)] + ([('V', 4), ('U', 4), ('U', 2)] if mate else [('U', 4), ('V', 3), ('U', 3)])
    else:
        rows = [('V', 6), ('U', 6), ('V', 5), ('U', 5), ('V', 4)] + ([('U', 4), ('V', 2)] if mate else [('V', 3), ('U', 3)])
    cols = range(6, -1, -1)
    if bordered:
        rows = [('V', 8)]+[(letter, index+1) for letter, index in rows]
        cols = range(7, -1, -1)
    return tuple(tuple(None if r-j < 0 else f'{letter}{r-j}' for j in cols) for letter, r in rows)


def check_formal_borders(reverse_sign=False):
    for kind in ('A', 'B'):
        F, H = formals(kind), formals(kind, True)
        assert determinant(F) == determinant(H)
        BF, BH = formals(kind, bordered=True), formals(kind, True, True)
        word = (('U1',)*4+('V0', 'V3', 'V5', 'V7') if kind == 'A' else
                ('U1',)*3+('V0', 'V1', 'V3', 'V5', 'V7'))
        word = tuple(sorted(word))
        delta = add((1, determinant(BF)), (-1, determinant(BH)))
        assert delta[word] == (1 if reverse_sign else -1)
        contributors = []
        for matrix in (BF, BH):
            words = []
            for p, sign in signed_permutations(8):
                entries = [matrix[i][p[i]] for i in range(8)]
                if None not in entries and tuple(sorted(entries)) == word:
                    words.append((tuple(j+1 for j in p), sign))
            contributors.append(words)
        extra = ((7, 1, 2, 5, 3, 8, 4, 6), 1)
        shared = ((1, 8, 2, 7, 3, 6, 4, 5), 1)
        assert contributors == ([[], [extra]] if kind == 'A' else [[shared], [shared, extra]])
        print('PASS:', kind, 'formal equality, tied-border coefficient -1, contributors', contributors)
    # Check the localization prefactor and the stated minor index sets independently.
    U, V = [2, 3, 5, 7, 11, 13, 17], [19, 23, 29, 31, 37, 41, 43]
    c = []
    for n in range(7):
        c.append((sp.Rational(V[n])-sum(U[j]*c[n-j] for j in range(1, n+1)))/U[0])
    source = sp.Matrix([[0 if x is None else (U if x[0] == 'U' else V)[int(x[1:])]
                        for x in row] for row in formals('A')]).det()
    for rr, cc in (((3, 5, 6), (0, 1, 2)), ((4, 5, 6), (0, 1, 3))):
        small = sp.Matrix([[0 if r < j else c[r-j] for j in cc] for r in rr]).det()
        assert source == U[0]**7*small
    print('PASS: family A localization has the stated positive h_d^7 prefactor and minor sets')


def check_upper_inclusion_rows():
    a, b, d = sp.symbols('a b d')
    from check_ten_negative_algebra import context
    S = a+4*b+d
    A, B, C, D, E, L = a+d, b+d, a+b+d, 2*b+d, a+2*b+d, 3*b+d
    expected = {
        'A': [(A, 3*b-a+d, E, D, D, C, C), (A, 2*b-a+d, L, E, D, C, C)],
        'B': [(A, 3*b-a+d, E, E, D, C, C), (A, D, L, E, D, C, C)],
    }
    for kind, i in (('A', 2), ('B', 1)):
        canonical = five_cores(i, a+d, a, b)[::-1]
        for mate, core, row_word in zip((False, True), canonical, expected[kind]):
            X, Y = family(kind, a, b, d, mate)
            Q = normalize(X[2:], Y[1:-1])
            assert all(sp.expand(x-y) == 0 for aa, bb in zip(rotate(*Q), core) for x, y in zip(aa, bb)), (kind, mate, rotate(*Q), core)
            assert sp.expand(Q[0][0]-S) == 0
            rows = profile(*context(*rotate(*Q), d, a, b, b-a-d))[0]
            assert all(sp.expand(x-y) == 0 for x, y in zip(rows, row_word))
            # Substitute b=a+d+e. Positivity of all residual row-minus-B
            # differences is manifest from positive coefficients in a,d,e.
            e = sp.Symbol('e')
            for row in rows[1:]:
                expr = sp.Poly(sp.expand((row-B).subs(b, a+d+e)), a, d, e)
                assert all(coef >= 0 for coef in expr.coeffs()) and expr != 0
                assert expr.eval({a: 1, d: 0, e: 1}) > 0
    t = sp.Symbol('t')
    # Both tied-border row-multiset equations force t=b.
    for left, right in (((3*b+d, 3*b+d+t), (4*b+d, 2*b+d+t)),
                        ((a+3*b+d, 3*b+d+t), (4*b+d, a+2*b+d+t))):
        eq = sp.expand(sp.prod(left)-sp.prod(right))
        sol = sp.solve(eq, t)
        assert sol == [b]
    print('PASS: both upper-inclusion reflected-row tables and both tied-border margin equations')


def cells_profile(cells):
    rows = []
    intervals = []
    for r in range(min(r for r, c in cells), max(r for r, c in cells)+1):
        cols = sorted(c for rr, c in cells if rr == r)
        assert cols == list(range(cols[0], cols[-1]+1))
        rows.append(len(cols))
        intervals.append((cols[0], cols[-1]))
    gaps = tuple(min(b, d)-max(a, c) for (a, b), (c, d) in zip(intervals, intervals[1:]))
    return tuple(rows), gaps


def check_chart_and_assembly():
    for a, b, d in ((1, 2, 0), (1, 3, 1), (2, 5, 2), (3, 7, 1)):
        E = {(0, j) for j in range(b-1, b-1+a+d)} | {(1, j) for j in range(b+d)}
        def copy(eta, tau):
            return {(r+eta-tau, c+eta+tau*(b-1)) for r, c in E}
        union = set().union(*(copy(0, j) for j in range(6)), *(copy(1, j) for j in range(1, 5)))
        assert cells_profile(union | copy(2, 3)) == profile(*family('A', a, b, d, True))
        assert cells_profile(union | copy(2, 2)) == profile(*family('A', a, b, d))
        for kind in ('A', 'B'):
            F, H = family(kind, a, b, d), family(kind, a, b, d, True)
            orbit = [F, H, rotate(*F), rotate(*H)]
            assert len(set(orbit)) == 4
            words = [profile(*Q)[1] for Q in orbit]
            assert len(set(words)) == 4
            assert all(Counter(w) == Counter(words[0]) for w in words)
            for Q in orbit:
                assert connected(*Q)
                rho = negative_partition(*Q)
                assert sum(rho) == 10 and minimum(rho) == 7
                assert bool(set(Q[0]) & set(Q[1])) == (d == 0)
            for mate, Q in ((False, F), (True, H)):
                assert gamma(*Q) == family(kind, 2*a, 2*b, 2*d+1, mate)
                assert gamma(*border(*Q, 2, 3)) == border(*gamma(*Q), 4, 6)
            area = sum(profile(*F)[0])
            assert area == (3 if kind == 'A' else 4)*a+11*b+7*d
    # The image's first three odd gaps force precisely this parameter parity.
    compatible = [(a, b, d) for a, b, d in product(range(2), repeat=3)
                  if all(z % 2 for z in (d, a+d, b+d))]
    assert compatible == [(0, 0, 1)]
    print('PASS: A cell-union profiles, four distinct gap words, image parameters, border covariance, and parity back-transfer')


if __name__ == '__main__':
    check_formal_borders()
    check_upper_inclusion_rows()
    check_chart_and_assembly()
    firing_control('reversed tied-border separator sign', lambda: check_formal_borders(True))
    print('ALL PASS')
