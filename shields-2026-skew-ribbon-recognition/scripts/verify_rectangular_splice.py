r"""Paper section `app:physical` (Whole currents and the first complete grade), ph:rectangular-splice.

For every connected diagram A with at most CELLS cells and every legal horizontal row mark of A
(case (a) with the lower copy in one row, the genuine empty mark included), the two-copy row
composition F = Row_2 o A is built by the gluing composition, and its Jacobi--Trudi determinant is
computed directly from its own flags.  Over exact integer letters h_1, h_2, ... (h_0 = 1,
h_i = 0 for i < 0) this is compared with

* the splice sum  s_F = sum_{x in X, y in Y} l_x R_y h_{Q + x - y},  where l_x and R_y are the
  signed cofactors of JT(A) at (row x, column 0) and (row S, column y);
* for every r >= 1 with X closed under subtracting r at positive results and no multiple of r in
  X, the substitution h_i -> h_i + z h_{i-r}: it fixes every R_y, sends l_x to
  sum_{j >= 0} (-z)^j l_{x + jr}, and the coefficient formula for [z^L] s_F, every L >= 1.

Polynomials in z are compared exactly by evaluating at more integer points than the degree and
interpolating with `fractions`; no floating point.  Sampled letters (SEEDS random assignments),
exhaustive in the diagrams and marks.
"""
import random
from fractions import Fraction

from _gluing_common import compose
from check_two_copy_flags import betas, diagrams, marks

CELLS = 8
SEEDS = 2
ZPOINTS = 24


def det(mat):
    n = len(mat)
    a = [[Fraction(x) for x in row] for row in mat]
    d = Fraction(1)
    for k in range(n):
        p = next((i for i in range(k, n) if a[i][k] != 0), None)
        if p is None:
            return Fraction(0)
        if p != k:
            a[k], a[p] = a[p], a[k]
            d = -d
        d *= a[k][k]
        for i in range(k + 1, n):
            f = a[i][k] / a[k][k]
            if f:
                for j in range(k, n):
                    a[i][j] -= f * a[k][j]
    return d


def jt(X, Y, h):
    return [[h(x - y) for y in Y] for x in X]


def cofactor(X, Y, h, row_label, col_label):
    i, j = X.index(row_label), Y.index(col_label)
    sub = [[h(x - y) for jj, y in enumerate(Y) if jj != j] for ii, x in enumerate(X) if ii != i]
    return (-1) ** (i + j) * det(sub)


def interpolate(points):
    """Coefficients of the polynomial through (z, value) pairs, by Newton's divided differences."""
    zs = [p[0] for p in points]
    coef = [Fraction(p[1]) for p in points]
    n = len(zs)
    for k in range(1, n):
        for i in range(n - 1, k - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (zs[i] - zs[i - k])
    poly = [Fraction(0)]
    for i in range(n - 1, -1, -1):
        new = [Fraction(0)] * (len(poly) + 1)
        for k, c in enumerate(poly):
            new[k + 1] += c
            new[k] -= zs[i] * c
        new[0] += coef[i]
        poly = new
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def is_row_mark(mk):
    return mk.case == 'a' and len({i for i, _ in mk.lower}) <= 1


def main():
    rng = random.Random(20260101)
    row2 = frozenset({(0, 0), (0, 1)})
    cases = substitutions = 0
    for A in diagrams(CELLS):
        for mk in marks(A):
            if not is_row_mark(mk):
                continue
            X, Y = betas(A)
            S, w = X[0], mk.width
            Q = S - w
            assert Q == mk.period
            F = compose(row2, mk)
            XF, YF = betas(F)
            for seed in range(SEEDS):
                letters = {i: rng.randint(1, 9) for i in range(1, 40)}

                def h(i, letters=letters):
                    return 0 if i < 0 else 1 if i == 0 else letters[i]
                ell = {x: cofactor(X, Y, h, x, 0) for x in X}
                R = {y: cofactor(X, Y, h, S, y) for y in Y}
                sF = det(jt(XF, YF, h))
                splice = sum(ell[x] * R[y] * h(Q + x - y) for x in X for y in Y)
                assert sF == splice, (sorted(A), sorted(mk.lower))
                cases += 1
                for r in range(1, S + 1):
                    if any(x % r == 0 for x in X):
                        continue
                    if any(x - r > 0 and (x - r) not in X for x in X):
                        continue

                    def hz(i, z, r=r, h=h):
                        return h(i) + z * h(i - r)
                    # substituted cofactors, as polynomials in z
                    pts = list(range(1, ZPOINTS + 1))
                    for y in Y:
                        poly = interpolate([(z, cofactor(X, Y, lambda i, z=z: hz(i, z), S, y))
                                            for z in pts])
                        assert poly == [R[y]], ('R_y not fixed', sorted(A), r, y)
                    for x in X:
                        poly = interpolate([(z, cofactor(X, Y, lambda i, z=z: hz(i, z), x, 0))
                                            for z in pts])
                        want = [Fraction(0)] * (len(poly) + len(X) + 2)
                        j = 0
                        while x + j * r <= S:
                            if x + j * r in X:
                                want[j] += (-1) ** j * ell[x + j * r]
                            j += 1
                        while len(want) > 1 and want[-1] == 0:
                            want.pop()
                        assert poly == want, ('l_x', sorted(A), r, x)
                    big = interpolate([(z, det(jt(XF, YF, lambda i, z=z: hz(i, z))))
                                       for z in range(1, len(XF) + 3)])
                    for L in range(1, 5):
                        total = Fraction(0)
                        for b in range(1, r + 1):
                            lab = b + (L - 1) * r
                            if lab in ell:
                                total += ell[lab] * sum(R[y] * h(S + b - r - w - y) for y in Y)
                        want = (-1) ** (L - 1) * total
                        got = big[L] if L < len(big) else Fraction(0)
                        assert got == want, ('coefficient', sorted(A), sorted(mk.lower), r, L)
                    substitutions += 1
    assert cases > 0 and substitutions > 0
    print(f'ph:rectangular-splice: {cases} (mark, letters) cases of the splice sum, '
          f'{substitutions} admissible r with substitution identities and coefficients L = 1..4')
    print('ALL PASS')


if __name__ == '__main__':
    main()
