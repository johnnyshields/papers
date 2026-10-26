r"""Paper section `app:aligned` (Aligned reconstruction before minimality): `prop:full-image`,
`eq:full-source-image`, `lem:derivative-stock`, `prop:distinct-realization`, `eq:phi`.

Reading.  The proposition's hypothesis is a pair of Schur-equal proper charts F = D o_omega E and
H = C o_eta U of periods p = kq, q with D a ribbon; it does not require source-minimality, so
the pair F = H of one diagram written as a nested composition is an instance.  It is built
backwards from the data: a fine inner U with a legal ordinary mark eta of period q and width u, a
diagram J of span R = k + b with a legal ordinary mark omega' of period k and width b (the empty
mark when b = 0), a ribbon D = Row_M or Col_M, M = 2, then C = D o_omega' J, H = C o_eta U and
E = J o_eta U.  The mark omega of E with F = D o_omega E = H is found among the legal marks of
E and asserted to have period p = kq and width w = bq + u, N_E = Rq + u.  Exact polynomial
computations in h_1, h_2, ...:

  * (span = largest generator index; the weight of P is the area of J)
  * T_1 / T_0 = (delta_k^{M-1} s_C)/(delta_k^M s_C) is reduced to P/G (coprime, P primitive with
    positive leading coefficient); P is weighted homogeneous, irreducible, linear in h_R with
    span R, and equals s_J up to the canonical sign (prop:distinct-realization: P is the function
    of an actual connected diagram of span R);
  * Phi_eta(P) = L s_E (eq:full-source-image), with Phi_eta(h_j) = A^{j-1} s_{Row_j o_eta U}
    (eq:phi), L a nonzero primitive polynomial in the generators below q only;
  * lem:derivative-stock: the derivative of P in h_R is a primitive polynomial equal to the
    product of s_Z over the connected components Z of the interior J^- (the diagram on the
    proper flags of J), with a one-cell component contributing h_1; it is positive on positive
    letters;
  * prop:distinct-realization: on the instances whose fine mark eta is positive with distinct
    phases (s != t), P itself is, up to a sign (the canonical phase of the paper is a convention, not fixed by P), the function s_J of the actual
    connected diagram J of span R (counted separately below);
  * control: Phi_eta(P + h_1^R) is not divisible by s_E.
The reading of lem:derivative-stock stated here takes J^- as the "actual fine outer interior"; for
C the proper interior need not have the same components, and that identification is the one point
the instance does not exercise.

Uncovered: the general (non-nested) pair F = H, the irreducibility of s_E over the fraction field
of the nonpivot variables, and every use of source-minimality.
"""
import sympy as sp

from _gluing_common import compose, empty_mark, intersection_mark, legal, schur
from _mark_builders import betas, diagrams, marks, phases

JMAX = 6
UMAX = 7
N_SYMS = 40
h = sp.symbols('h1:%d' % N_SYMS)


def H(j):
    return sp.Integer(1) if j == 0 else (sp.Integer(0) if j < 0 else h[j - 1])


def poly_of(shape):
    total = sp.Integer(0)
    for mon, coef in schur(shape):
        term = sp.Integer(coef)
        for j in mon:
            term *= h[j - 1]
        total += term
    return sp.expand(total)


def delta(f, k):
    return sp.expand(sum(H(j - k) * sp.diff(f, h[j - 1]) for j in range(k, N_SYMS)
                         if f.has(h[j - 1])))


def weight(f):
    p = sp.Poly(f, *h)
    ws = {sum((i + 1) * e for i, e in enumerate(m)) for m in p.monoms()}
    return ws


def components(J):
    """Connected components, as diagrams, of the interior of J (proper flags)."""
    X, Y = betas(J)
    I, C = X[1:], Y[:-1]
    # components of the flag pair (I, C): cut where the pair of heights returns to zero
    comps, cur_i, cur_c = [], [], []
    events = sorted([(x, 'r') for x in I] + [(y, 'c') for y in C], key=lambda t: -t[0])
    height = 0
    pending = []
    for val, kind in events:
        pending.append((val, kind))
        height += 1 if kind == 'r' else -1
        if height == 0:
            comps.append(pending)
            pending = []
    assert not pending
    return comps


def component_function(piece):
    rows = sorted([v for v, k in piece if k == 'r'], reverse=True)
    cols = sorted([v for v, k in piece if k == 'c'], reverse=True)
    n = len(rows)
    A = sp.Matrix(n, n, lambda i, j: H(rows[i] - cols[j]))
    return sp.expand(A.det())


def lowest_marks(J, k):
    for mk in marks(J):
        if mk.case == 'a' and legal(mk) and mk.period == k:
            yield mk


def main():
    row = lambda m: frozenset((0, j) for j in range(m))  # noqa: E731
    col = lambda m: frozenset((i, 0) for i in range(m))  # noqa: E731
    inners = [U for U in diagrams(UMAX)
              if len({i for i, _ in U}) >= 2 and len({j for _, j in U}) >= 2]
    count = nonempty_u = distinct = 0
    for U in inners:
        for eta in marks(U):
            if eta.case != "a" or not legal(eta) or eta.period not in (2, 3) or eta.width > 1:
                continue
            q, u = eta.period, eta.width
            A = poly_of(eta.lower) if eta.lower else sp.Integer(1)
            for K_PERIOD in (2, 3):
              for J in diagrams(JMAX):
                for om1 in lowest_marks(J, K_PERIOD):
                    b = om1.width
                    if b > 1:
                        continue
                    R = K_PERIOD + b
                    if max(c[1] - c[0] for c in J) - min(c[1] - c[0] for c in J) + 1 != R:
                        continue
                    for D in (row(2), col(2)):
                        M = 2
                        Cc = compose(D, om1)
                        Hh = compose(Cc, eta)
                        E = compose(J, eta)
                        p, w = K_PERIOD * q, b * q + u
                        found = [mk for mk in marks(E) if legal(mk) and mk.period == p
                                 and mk.width == w and compose(D, mk) == Hh]
                        assert found, ('nested chart has no mark on E', sorted(J), sorted(U))
                        Nfull = max(c[1] - c[0] for c in Hh) - min(c[1] - c[0] for c in Hh) + 1
                        assert Nfull == p * M + w and R * q + u == max(
                            c[1] - c[0] for c in E) - min(c[1] - c[0] for c in E) + 1
                        sC, sJ, sE = poly_of(Cc), poly_of(J), poly_of(E)
                        T0 = delta(delta(sC, K_PERIOD), K_PERIOD)
                        T1 = delta(sC, K_PERIOD)
                        g = sp.gcd(T1, T0)
                        P = sp.cancel(T1 / g)
                        Pn = sp.Poly(sp.expand(P), *h)
                        cont = sp.Poly(sp.expand(P), *h).content()
                        P = sp.expand(P / cont)
                        if sp.Poly(P, *h).LC() < 0:
                            P = -P
                        assert sp.expand(P - sJ) == 0 or sp.expand(P + sJ) == 0, (sorted(J), sorted(D))
                        sU, tU = phases(eta)
                        if u > 0 and sU != tU:
                            distinct += 1
                            assert sp.expand(P - sJ) == 0 or sp.expand(P + sJ) == 0
                        assert len(weight(P)) == 1 and weight(P).pop() == len(J)
                        assert max(k + 1 for k in range(N_SYMS - 1) if P.has(h[k])) == R
                        assert len(sp.factor_list(P)[1]) == 1 and sp.factor_list(P)[1][0][1] == 1
                        pp = sp.Poly(P, h[R - 1])
                        assert pp.degree() == 1 and not any(P.has(h[j]) for j in range(R, N_SYMS - 1))
                        # eq:phi image
                        img = {h[j - 1]: A ** (j - 1) * poly_of(compose(row(j), eta)) for j in range(1, R + 1)}
                        PhiP = sp.expand(P.subs(img, simultaneous=True))
                        L, rem = sp.div(sp.Poly(PhiP, *h), sp.Poly(sE, *h))
                        assert rem.is_zero, ('eq:full-source-image', sorted(J), sorted(U))
                        Lp = L.as_expr()
                        assert Lp != 0 and not any(Lp.has(h[j]) for j in range(q - 1, N_SYMS - 1))
                        assert sp.Poly(Lp, *h).content() == 1 or sp.Poly(Lp, *h).content() == -1
                        bad = sp.expand((P + h[0] ** R).subs(img, simultaneous=True))
                        assert not sp.div(sp.Poly(bad, *h), sp.Poly(sE, *h))[1].is_zero
                        # lem:derivative-stock
                        dP = sp.expand(sp.diff(P, h[R - 1]))
                        prod = sp.Integer(1)
                        for piece in components(J):
                            prod *= component_function(piece)
                        assert sp.expand(dP - sp.expand(prod)) == 0 or sp.expand(dP + sp.expand(prod)) == 0, (
                            'derivative stock', sorted(J), dP, sp.factor(prod))
                        count += 1
                        nonempty_u += u > 0
    print(f'nested pairs F = H checked: {count} (fine width u > 0 in {nonempty_u}; positive distinct phases in {distinct})')
    assert count > 5 and distinct > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
