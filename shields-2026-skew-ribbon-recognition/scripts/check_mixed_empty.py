r"""An empty upper over a mixed inner (rt:mixed-empty).

Paper section `app:mixed-empty` (An empty upper over a mixed inner), rt:mixed-empty,
rt:empty-junction, rt:mixed-empty-flags, rt:mixed-empty-splice, rt:mixed-empty-pencil.

The lemma's hypothesis (two Schur-equal charts through a full mixed mark, one of them under an
empty domino) is a comparison the main theorem excludes, so it has no positive instance.  The
finite machinery its proof runs on is built backwards instead: every connected J up to J_CELLS
cells, every legal case (d) mark mu of J with 0 < v < r, and every connected outer V up to V_CELLS
cells of span M >= 2 give the actual composition E = V o_mu J.  On each such E, at random integer
letters h_j (h_0 = 1, h_j = 0 for j < 0), exact:

* N = M r + v is the top row of E;
* the empty row-domino parent has the beta lists
  (X_E + N) u (X_E \ {N}) and ((Y_E \ {0}) + N) u Y_E, and the column parent has one more row;
* the two-junction identity s_E^2 = s_{Row_2 o_empty E} + s_{Col_2 o_empty E}, which is asserted
  on every diagram E up to E_CELLS cells as well;
* with l_x the signed cofactor at row x, column zero, R_y the signed cofactor at row N, column y,
  alpha = l_N = R_0: the splice P_E = sum_{x,y} l_x R_y h_{x+N-y};
* X_E is closed under subtraction of r while positive and has no zero residue;
* the pencil formula, for L = 1..M+1: [zeta^L] P_E(h + zeta h_{.-r}) = (-1)^{L-1} sum_{b=1}^{r}
  l_{b+(L-1)r} Q_b with Q_b = Phi(N+b-r), Phi(a) = sum_y R_y h_{a-y}, l_a = 0 off X_E; the
  control with the sign (-1)^L instead fails on every E where the left side is nonzero.

Uncovered: the occupied-residue coding of the flags (B, t_0, s_0), the window cofactors kappa_x,
the fixed-block elimination and the final recovery of V from the observable O.
"""
import random
from fractions import Fraction

from _gluing_common import compose, empty_mark, intersection_mark, legal, span
from check_two_copy_flags import betas, diagrams

J_CELLS = 5
V_CELLS = 3
E_CELLS = 8
rng = random.Random(11)


def det(rows):
    a = [[Fraction(x) for x in row] for row in rows]
    n, sign, result = len(a), 1, Fraction(1)
    for c in range(n):
        piv = next((i for i in range(c, n) if a[i][c] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != c:
            a[c], a[piv] = a[piv], a[c]
            sign = -sign
        result *= a[c][c]
        for i in range(c + 1, n):
            f = a[i][c] / a[c][c]
            if f:
                a[i] = [x - f * y for x, y in zip(a[i], a[c])]
    return sign * result


def JT(h, X, Y):
    return [[h(x - y) for y in Y] for x in X]


def minor(rows, i, j):
    return det([[v for jj, v in enumerate(row) if jj != j] for ii, row in enumerate(rows) if ii != i])


def letters():
    vals = {n: Fraction(rng.randint(1, 6)) for n in range(1, 80)}
    vals[0] = Fraction(1)
    return lambda n, vals=vals: vals[n] if n >= 0 else Fraction(0)


def flags_of_empty_row(X, Y, N):
    return sorted([x + N for x in X] + [x for x in X if x != N], reverse=True), \
        sorted([y + N for y in Y if y != 0] + list(Y), reverse=True)


def junction(E, h):
    X, Y = betas(E)
    row = betas(compose(frozenset({(0, 0), (0, 1)}), empty_mark(E)))
    col = betas(compose(frozenset({(0, 0), (1, 0)}), empty_mark(E)))
    sE = det(JT(h, X, Y))
    sR = det(JT(h, *row))
    sC = det(JT(h, *col))
    assert sE ** 2 == sR + sC, sorted(E)
    assert len(col[0]) == len(row[0]) + 1
    return row


def pencil_check(E, mk, M):
    r, v = mk.period, mk.width
    X, Y = betas(E)
    N = X[0]
    assert N == M * r + v
    assert all((x - r in X) for x in X if x > r) and all(x % r for x in X)
    h = letters()
    row = betas(compose(frozenset({(0, 0), (0, 1)}), empty_mark(E)))
    assert row == flags_of_empty_row(X, Y, N), (sorted(E), r, v)
    A = JT(h, X, Y)
    n = len(X)
    j0 = Y.index(0)
    ell = {x: (-1) ** (i + j0) * minor(A, i, j0) for i, x in enumerate(X)}
    R = {y: (-1) ** j * minor(A, 0, j) for j, y in enumerate(Y)}
    alpha = ell[N]
    assert alpha == R[0]
    PE = det(JT(h, *row))
    assert PE == sum(ell[x] * R[y] * h(x + N - y) for x in X for y in Y)

    def PE_at(z):
        hz = lambda m: h(m) + z * h(m - r)  # noqa: E731
        return det(JT(hz, *row))

    deg = 2 * len(row[0])
    pts = list(range(deg + 1))
    vals = [PE_at(Fraction(z)) for z in pts]
    coeffs = interpolate(pts, vals)
    Phi = lambda a: sum(R[y] * h(a - y) for y in Y)  # noqa: E731
    nonzero = 0
    for L in range(1, M + 2):
        rhs = sum(ell.get(b + (L - 1) * r, 0) * Phi(N + b - r) for b in range(1, r + 1))
        lhs = coeffs[L] if L < len(coeffs) else 0
        assert lhs == (-1) ** (L - 1) * rhs, (sorted(E), r, v, L)
        if lhs:
            nonzero += 1
            assert lhs != (-1) ** L * rhs
    return nonzero


def interpolate(xs, ys):
    """Coefficients of the polynomial through (xs, ys), exact."""
    n = len(xs)
    coeffs = [Fraction(0)] * n
    for i in range(n):
        poly, denom = [Fraction(1)], Fraction(1)
        for j in range(n):
            if j != i:
                poly = [a - xs[j] * b for a, b in zip([0] + poly, poly + [0])]
                denom *= xs[i] - xs[j]
        for k in range(n):
            coeffs[k] += ys[i] * poly[k] / denom
    return coeffs


def main():
    seen = 0
    for E in diagrams(E_CELLS):
        junction(E, letters())
        seen += 1
    print(f'junction identity on {seen} diagrams')
    built = live = 0
    outers = [V for V in diagrams(V_CELLS) if span(V) >= 2]
    for J in diagrams(J_CELLS):
        for cell in J:
            try:
                mk = intersection_mark(J, cell)
            except AssertionError:
                continue
            if mk.case != 'd' or not legal(mk) or not 0 < mk.width < mk.period:
                continue
            for V in outers:
                try:
                    E = compose(V, mk)
                except AssertionError:
                    continue
                M = span(V)
                live += pencil_check(E, mk, M) > 0
                built += 1
    print(f'mixed compositions V o_mu J: {built}, pencils with a nonzero coefficient: {live}')
    assert built > 20 and live > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
