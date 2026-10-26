r"""Paper section `app:cell-cut` (Integral cuts with a cell-only proper interior).

Sign of the top coefficient of the weighted current on a cell-only board.

`app:cell-cut`, "Application to the original aligned comparison": with `Q_C = (-1)^(s-1) det`
the signed board numerator of a connected cell-only profile `C` of span `L + R`, and
`kappa(C) = h_1^c`, the ray `Q_0` has `d Q_0 / d h_R = h_1^c`, so `V_L Q_C = m Q_0` forces
`m = [h_R h_1^c] V_L Q_C` and `delta_L Q_C = alpha Q_0` forces `alpha = [h_R h_1^c] delta_L Q_C`.
This script tabulates that coefficient over small cell-only profiles, reports its sign, and
asserts it is never negative (`board_m_nonneg` in the Lean tree); it vanishes on a few boards.
"""
import itertools
import sympy as sp

H = sp.symbols("h1:40")


def h(j):
    if j < 0:
        return sp.Integer(0)
    if j == 0:
        return sp.Integer(1)
    return H[j - 1]


def profiles(max_rows, max_len):
    # rows r_0..r_n (top to bottom), overlaps-minus-one g_0..g_{n-1} in {0,1}
    for n1 in range(1, max_rows + 1):
        for r in itertools.product(range(1, max_len + 1), repeat=n1):
            for g in itertools.product((0, 1), repeat=n1 - 1):
                if any(g[j] >= r[j] or g[j] >= r[j + 1] for j in range(n1 - 1)):
                    continue
                # interior row inequalities: g_a + g_b < r_b for consecutive a, b
                if any(g[a] + g[a + 1] >= r[a + 1] for a in range(n1 - 2)):
                    continue
                yield r, g


def betas(r, g):
    n1 = len(r)
    zeta = [0] * n1
    for i in range(n1 - 2, -1, -1):
        zeta[i] = zeta[i + 1] + r[i + 1] - g[i]
    xi = [zeta[i] + r[i] for i in range(n1)]
    return xi, zeta


def V(L, f, top):
    return sp.expand(sum((j - L) * h(j - L) * sp.diff(f, h(j)) for j in range(L + 1, top + 1)))


def D(L, f, top):
    return sp.expand(sum(h(j - L) * sp.diff(f, h(j)) for j in range(L, top + 1)))


def main():
    signs = {}
    count = 0
    for r, g in profiles(4, 4):
        xi, zeta = betas(r, g)
        s = len(r)
        S = xi[0]
        c = sum(g)
        Q = sp.expand((-1) ** (s - 1) * sp.Matrix(s, s, lambda i, j: h(xi[i] - zeta[j])).det())
        for L in range(2, S - 1):
            R = S - L
            if R < 2:
                continue
            m = sp.Poly(V(L, Q, S), *H[:S]).coeff_monomial(h(R) * h(1) ** c) if R != 1 else None
            al = sp.Poly(D(L, Q, S), *H[:S]).coeff_monomial(h(R) * h(1) ** c)
            signs.setdefault(sp.sign(m), 0)
            signs[sp.sign(m)] += 1
            count += 1
            if m <= 0:
                print("nonpositive m", r, g, L, m, al)
            assert m >= 0, (r, g, L, m)
    print("boards x L:", count, "sign tally of m:", signs)
    assert count > 0 and signs.get(1, 0) > 0


if __name__ == "__main__":
    main()
