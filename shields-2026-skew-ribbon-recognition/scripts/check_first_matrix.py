r"""The first response matrix of an ordinary finer (ph:first-response, ph:gradient, ph:finite-block,
ph:ordinary-zero).

Paper section `sec:comparison` (Finite comparisons on actual composition charts), labels
ph:ordinary-flags, ph:ordinary-source-chart, ph:finite-block, ph:first-response, ph:ordinary-zero.

For a legal case (a) mark of J, use its own returned chart H=P'/G', G'_t=1, P'_s=R_0.
At the physical unit, P'_0=G'_0; G'_0 is a neutral variable when t>0, not a second normalization.
The outside coordinates are the available P'_i and G'_j with v<i,j<N_J.
Build the complete response inverse and compute its actual Jacobian by exact first-order
arithmetic over Fractions, including the inverse variation.  Unit differences are only an
affinity diagnostic and are never substituted for derivatives.

The sweep covers legal ordinary finers through J_CELLS cells and every 0<w<r with w!=v,
at generic rational coordinates.  It compares the mark determinant with its signed contact
cofactor times R_0.  A separate symbolic calculation checks the Jacobian on a nontrivial
vertical-domino mark, including its unfixed G'_0.  Native closure retains s in the target
set X_W union B_-.

These mate-free samples do not supply the full finite comparison.  Affinity, skew-symmetry,
zero Jacobians at a sample, and native closure are diagnostics, not assertions of ph:finite-block
or ph:ordinary-zero.  In particular, a zero sampled Jacobian is not a whole-function identity.
The Schur-equal mate, mixed finer, empty finer, and full zero-response implication remain uncovered.
"""
import random
import sys
from fractions import Fraction as Fr

import sympy as sp

from _gluing_common import intersection_mark, legal
from check_two_copy_flags import betas, diagrams, phases

J_CELLS = int(sys.argv[1]) if len(sys.argv) > 1 else 8
rng = random.Random(4)


class _Tangent:
    """An exact value and one directional derivative."""

    def __init__(self, value, derivative=0):
        self.value = Fr(value)
        self.derivative = Fr(derivative)

    def __add__(self, other):
        other = other if isinstance(other, _Tangent) else _Tangent(other)
        return _Tangent(self.value + other.value, self.derivative + other.derivative)

    __radd__ = __add__

    def __neg__(self):
        return _Tangent(-self.value, -self.derivative)

    def __sub__(self, other):
        return self + -other

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, _Tangent) else _Tangent(other)
        return _Tangent(self.value * other.value,
                        self.derivative * other.value + self.value * other.derivative)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = other if isinstance(other, _Tangent) else _Tangent(other)
        return _Tangent(self.value / other.value,
                        (self.derivative * other.value - self.value * other.derivative)
                        / other.value ** 2)

    def __rtruediv__(self, other):
        return _Tangent(other) / self


def _value(x):
    return x.value if isinstance(x, _Tangent) else x


def _moments(J, mk, base, count):
    X, Y = betas(J)
    s, t = phases(mk)
    G = {j: (Fr(1) if j == t else base['G', j]) for j in Y}
    P = {i: base['P', i] for i in range(1, X[0]) if i not in X}
    P[s] = base['R0']
    moments = [Fr(1)]
    for k in range(1, count):
        moments.append((P.get(k, 0) - sum(G.get(j, 0) * moments[k - j]
                                         for j in range(1, k + 1))) / G[0])
    return moments


def _jacobian(J, mk, w, base):
    values = responses(J, mk, w, base)
    if values is None:
        return None
    labels = list(values)
    columns = []
    for label in labels:
        moving = {key: _Tangent(value, key == label) for key, value in base.items()}
        result = responses(J, mk, w, moving)
        if result is None:
            return None
        assert all(_value(result[key]) == values[key] for key in labels)
        columns.append([result[key].derivative if isinstance(result[key], _Tangent) else Fr(0)
                        for key in labels])
    return values, [[column[i] for column in columns] for i in range(len(labels))]


def _check_normalization_and_jacobian():
    J = frozenset({(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1)})
    mk = intersection_mark(J, (-1, 3))
    X, Y = betas(J)
    base = {('P', i): Fr(1) for i in range(1, X[0]) if i not in X}
    base.update({('G', j): Fr(1) for j in Y})
    base['G', 0], base['R0'] = Fr(-2, 3), Fr(-1, 3)
    assert _moments(J, mk, base, 3) == [1, 2, 3]
    assert closure(J, mk, 3)
    values, A = _jacobian(J, mk, 1, base)
    p3, p4, g4 = variables = sp.symbols('p3 p4 g4')
    raw = [sp.Integer(1)]
    P, G = {1: sp.Rational(-1, 3), 3: p3, 4: p4}, {0: sp.Rational(-2, 3), 1: 1, 4: g4}
    for n in range(1, 7):
        raw.append(sp.expand((P.get(n, 0) - sum(G.get(j, 0) * raw[n-j] for j in range(1, n+1))) / G[0]))
    reference = sp.Matrix([raw[5]/raw[2] - raw[1]*raw[6]/raw[2]**2,
                           0, raw[2] - raw[1]*raw[3]/raw[2]])
    point = dict.fromkeys(variables, 1)
    assert list(values) == [('P', 3), ('P', 4), ('G', 4)]
    assert sp.Matrix(list(values.values())) == reference.subs(point)
    assert sp.Matrix(A) == reference.jacobian(variables).subs(point)


def _check_inverse_variation():
    J = frozenset({(-2, 1), (-2, 2), (-2, 3), (-1, 1),
                   (-1, 2), (0, 0), (0, 1), (0, 2)})
    mk = intersection_mark(J, (-2, 3))
    assert (mk.period, mk.width, phases(mk)) == (5, 1, (1, 0))
    X, Y = betas(J)
    base = {('P', i): Fr(2, 3) for i in range(1, X[0]) if i not in X}
    base.update({('G', j): Fr(3, 2) for j in Y})
    base['R0'] = Fr(5, 4)
    key = ('P', 2)
    for coefficient in (Fr(2, 3), Fr(3, 2)):
        base[key] = coefficient
        moving = {k: _Tangent(value, k == key) for k, value in base.items()}
        epsilon = sp.Symbol('epsilon')
        symbolic = dict(base)
        symbolic[key] = sp.Rational(coefficient.numerator, coefficient.denominator) + epsilon
        actual = responses(J, mk, 2, moving)
        reference = responses(J, mk, 2, symbolic)
        assert actual is not None and reference is not None
        derivatives = {}
        for label in actual:
            derivative = actual[label].derivative if isinstance(actual[label], _Tangent) else Fr(0)
            assert sp.diff(reference[label], epsilon).subs(epsilon, 0) == derivative
            derivatives[label] = derivative
        # The fixed inverse varies even when an elimination multiplier has value zero.
        moments = _moments(J, mk, moving, 5)
        fixed = [[moments[b-c] if b >= c else Fr(0) for c in (2, 3)] for b in (3, 4)]
        inverse = solve(fixed, [[Fr(1), Fr(0)], [Fr(0), Fr(1)]])
        assert inverse is not None and any(x.derivative for row in inverse for x in row)
        if coefficient == Fr(3, 2):
            assert _value(fixed[1][0]) == 0 and fixed[1][0].derivative == 1
            assert sp.Matrix([[_value(x) for x in row] for row in fixed]).det() == sp.Rational(25, 16)
            assert derivatives['P', 2] == 0 and derivatives['G', 3] == 1


def solve(A, Bm):
    n = len(A)
    M = [list(A[i]) + list(Bm[i]) for i in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if _value(M[r][c]) != 0), None)
        if p is None:
            return None
        M[c], M[p] = M[p], M[c]
        inv = 1 / M[c][c]
        M[c] = [x * inv for x in M[c]]
        for r in range(n):
            if r != c:
                f = M[r][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return [row[n:] for row in M]


def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def responses(J, mk, w, base):
    r, v = mk.period, mk.width
    s, t = phases(mk)
    X, Y = betas(J)
    N = X[0]
    XW = sorted(x - r for x in X if x >= r)
    Bm = sorted(x for x in X if v < x < r)
    YW = sorted(y for y in Y if y <= v)
    Cm = sorted(y for y in Y if v < y < r)
    rows = set(X)
    Pc = [i for i in range(1, N) if i not in rows]
    Gc = [j for j in Y if j < N]
    delta = v - w
    K = 2 * r + N + 4
    h = _moments(J, mk, base, K)

    def Hm(m, n):
        return h[n * r + m] if 0 <= n * r + m < K else Fr(0)
    B0 = sorted((set(XW) - {s}) | set(Bm))
    C0 = sorted((set(YW) - {t}) | set(Cm))
    if len(B0) != len(C0):
        return None
    m = len(B0)
    L0 = L1 = []
    if m:
        D0 = [[Hm(b - c, 0) for c in C0] for b in B0]
        D1 = [[Hm(b - c, 1) for c in C0] for b in B0]
        D0i = solve(D0, [[Fr(int(i == j)) for j in range(m)] for i in range(m)])
        if D0i is None:
            return None
        L0 = mm([[Hm(s - c, 0) for c in C0]], D0i)[0]
        t1 = mm([L0], D1)[0]
        L1 = mm([[Hm(s - c, 1) - x for c, x in zip(C0, t1)]], D0i)[0]

    def Lam(mm_):
        k = 0
        while mm_ >= r:
            mm_ -= r
            k += 1
        if mm_ < 0:
            return None
        if mm_ == s:
            b = [Fr(-1), Fr(0)]
        elif mm_ in B0:
            b = [L0[B0.index(mm_)], L1[B0.index(mm_)]]
        else:
            b = [Fr(0), Fr(0)]
        return [b[n - k] if n - k >= 0 else Fr(0) for n in range(2)]

    def Theta(d):
        a = [Hm(s - d, 0), Hm(s - d, 1)]
        if m:
            h0 = [Hm(b - d, 0) for b in B0]
            h1 = [Hm(b - d, 1) for b in B0]
            a = [a[0] - sum(x * y for x, y in zip(L0, h0)),
                 a[1] - sum(x * y + z * u for x, y, z, u in zip(L0, h1, L1, h0))]
        return a
    out = {}
    for i in [i for i in Pc if v < i < N]:
        lam = Lam(i - delta)
        if lam is None:
            return None
        out['P', i] = lam[1]
    for j in [j for j in Gc if v < j < N]:
        out['G', j] = Theta(j - delta)[1]
    return out


def closure(J, mk, w):
    r, v = mk.period, mk.width
    s, t = phases(mk)
    X, Y = betas(J)
    B = set(betas(mk.lower)[0]) | {x for x in X if v < x < r}
    C = {y for y in Y if 0 <= y < r}
    d = v - w
    return (all((b + d) % r in B for b in B - {s}) and all((c - d) % r in C for c in C - {t}))




def main():
    _check_normalization_and_jacobian()
    _check_inverse_variation()
    stats = {}
    skew = {}
    nonlinear = skipped = closed = normalizations = 0
    zero = nonzero = zero_closed = nonzero_closed = 0
    for J in diagrams(J_CELLS):
        X, Y = betas(J)
        for cell in J:
            try:
                mk = intersection_mark(J, cell)
            except AssertionError:
                continue
            if mk.case != 'a' or not legal(mk) or mk.width == 0:
                continue
            r, v = mk.period, mk.width
            s, t = phases(mk)
            XW, YW = betas(mk.lower)
            Pc = [i for i in range(1, X[0]) if i not in X]
            for w in range(1, r):
                if w == v:
                    continue
                base = {('P', i): Fr(rng.randint(1, 9), rng.randint(1, 5)) for i in Pc}
                base.update({('G', j): Fr(rng.randint(1, 9), rng.randint(1, 5)) for j in Y})
                base['R0'] = Fr(rng.randint(1, 9), rng.randint(1, 5))
                result = _jacobian(J, mk, w, base)
                if result is None:
                    skipped += 1
                    continue
                F, A = result
                moments = _moments(J, mk, base, v + 1)
                h = lambda n: 0 if n < 0 else moments[n]
                mark = sp.Matrix([[h(x-y) for y in YW] for x in XW])
                Gamma = (-1) ** (XW.index(s) + YW.index(t)) * mark.minor_submatrix(XW.index(s), YW.index(t)).det()
                assert mark.det() == Gamma * base['R0']
                normalizations += 1
                labels = list(F)
                for j, label in enumerate(labels):
                    shifted = dict(base)
                    shifted[label] += 1
                    moved = responses(J, mk, w, shifted)
                    if moved is not None:
                        nonlinear += any(moved[key] - F[key] != A[i][j] for i, key in enumerate(labels))
                n = len(labels)
                is_skew = all(A[i][j] == -A[j][i] for i in range(n) for j in range(n))
                skew[is_skew] = skew.get(is_skew, 0) + 1
                pp = all(A[i][j] == 0 for i in range(n) for j in range(n)
                         if labels[i][0] == labels[j][0] == 'P')
                gg = all(A[i][j] == 0 for i in range(n) for j in range(n)
                         if labels[i][0] == labels[j][0] == 'G')
                is_zero = all(value == 0 for row in A for value in row)
                key = (pp, gg, is_zero)
                stats[key] = stats.get(key, 0) + 1
                native = closure(J, mk, w)
                closed += native
                if is_zero:
                    zero += 1
                    zero_closed += native
                else:
                    nonzero += 1
                    nonzero_closed += native
    assert normalizations > 0
    print(f'normalized mark/cofactor identities checked: {normalizations}; skipped singular samples: {skipped}')
    print(f'sampled Jacobian (PP zero, GG zero, all zero): {stats}; skew-symmetry: {skew}')
    print(f'non-affine unit-shift diagnostics: {nonlinear}; native-closed samples: {closed}')
    print(f'zero sampled Jacobian: {zero}, native-closed: {zero_closed}; '
          f'nonzero sampled Jacobian: {nonzero}, native-closed: {nonzero_closed}')
    print('symbolic Jacobian and unfixed-zero-column normalization agree; no full-comparison implication asserted')
    print('ALL PASS')


if __name__ == '__main__':
    main()
