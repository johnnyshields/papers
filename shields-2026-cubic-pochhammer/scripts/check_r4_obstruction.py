#!/usr/bin/env python3
r"""Paper section `subsec:first-supercritical-case` (The first supercritical case): the r=4 obstruction.

Where `verify_multiplicity.py` establishes *that* the residue-class certificate fails at
`r = 4`, this script establishes *how* -- exactly, and uniformly in the degree `m`.

The projective lift of `eq:P-def` sends `t = xi/(1+xi)`; with `N = rm-1` and
`J^{(r)}_m(t) = sum_i c_i t^i`,

    P(xi) = (1+xi)^N J^{(r)}_m(xi/(1+xi)) = sum_i c_i xi^i (1+xi)^(N-i),

so the lifted coefficients are `a_j = sum_i c_i C(N-i, j-i)`.  Nonnegativity of every
`a_j` certifies `J^{(r)}_m >= 0` on `(0,1)`; that is the r=3 certificate of
`lem:bernstein` through `eq:G-J` (`subsec:constant-weight-kernel`), whose
strictness comes from `b_2 > 0`.

At `r = 4` it fails, and the failure is a single coefficient whose size is an exact
polynomial identity in `m`.  Because `r = 4` puts the `c_i` at `i` in
`{3, 4, 7, 8, 11, 12, ...}`, the coefficients `a_7, a_8, a_9` see only `k <= 2`
(the next contribution is at `i = 11 > 9`) whatever `m` is.  Their closed forms are
therefore identities, not fits, and everything below is exact: `sympy` over
rationals and `math.comb` over integers, no floating point anywhere.
"""

from math import comb
import sympy as sp

m = sp.symbols('m', positive=True, integer=True)

Q = (m - 2) * (m - 1) * (2*m - 3) * (2*m - 1) * (4*m - 7) * (4*m - 5) * (4*m - 3)


def lift_coeff_int(r, mm, j):
    """a_j of the lift, in exact integer arithmetic, from the definition."""
    n = r*mm - 2
    c = {}
    for k in range(1, mm):
        b = comb(n, r*k - 1)
        c[r*k - 1] = c.get(r*k - 1, 0) + b*k
        c[r*k] = c.get(r*k, 0) - b*(mm - k)
    N = r*mm - 1
    return sum(ci * comb(N - i, j - i) for i, ci in c.items() if i <= j)


def lift_coeffs_int(r, mm):
    return [lift_coeff_int(r, mm, j) for j in range(r*mm)]


def a_symbolic(j):
    """a_j as an exact polynomial in m, from the k <= 2 contributions only."""
    n, N = 4*m - 2, 4*m - 1
    cs = {3: sp.binomial(n, 3),
          4: -sp.binomial(n, 3) * (m - 1),
          7: 2 * sp.binomial(n, 7),
          8: -sp.binomial(n, 7) * (m - 2)}
    return sp.expand(sum(ci * sp.binomial(N - i, j - i) for i, ci in cs.items() if i <= j))


def check_Q_positive_for_all_m_at_least_three():
    """Q > 0 for every real m >= 3, hence a_8 = -28Q/315 < 0 at every such m.

    This is the paper's headline scope claim at r = 4, and a sweep over integer m
    cannot carry it.  Substituting m = 3 + s puts each of Q's seven factors into
    a polynomial in s with nonnegative coefficients and a positive constant term,
    so every factor is positive for s >= 0 and the product is too -- for real m,
    not merely for the integers that were swept.  m = 2 is checked to be the
    exact boundary: the factor (m-2) vanishes there.
    """
    s = sp.symbols('s', nonnegative=True)
    factors = [m - 2, m - 1, 2*m - 3, 2*m - 1, 4*m - 7, 4*m - 5, 4*m - 3]
    assert sp.expand(Q - sp.prod(factors)) == 0
    for fac in factors:
        shifted = sp.Poly(sp.expand(fac.subs(m, 3 + s)), s)
        cs = shifted.all_coeffs()
        assert all(c >= 0 for c in cs), (fac, cs)
        assert cs[-1] > 0, (fac, cs)                 # positive at s = 0
    # the same conclusion by the second route, on the expanded product rather
    # than factor by factor: Q(3+s) itself has every coefficient positive
    expanded = sp.Poly(sp.expand(Q.subs(m, 3 + s)), s).all_coeffs()
    assert expanded == [256, 3136, 16240, 46060, 77224, 76489, 41415, 9450], expanded
    assert all(c > 0 for c in expanded)
    a7, a8 = (a_symbolic(j) for j in (7, 8))
    assert sp.simplify(a8 + sp.Rational(28, 315) * Q) == 0
    assert sp.simplify(a7 - sp.Rational(8, 315) * Q) == 0
    # the boundary: at m = 2 the factor (m-2) is what kills a_7 and a_8
    assert sp.expand((m - 2).subs(m, 2)) == 0
    assert int(Q.subs(m, 2)) == 0 and int(Q.subs(m, 3)) > 0
    # and the sweep the closed forms already run agrees, at the integers
    for v in range(3, 60):
        assert int(Q.subs(m, v)) > 0 and int(a8.subs(m, v)) < 0, v
    print("PASS Q = prod of seven factors each with nonnegative coefficients in "
          "s = m-3, so Q > 0 and a_8 = -28Q/315 < 0 for every REAL m >= 3, with "
          "m = 2 the exact boundary")


def check_closed_forms():
    """a_7, a_8, a_9 in closed form, and a_8 = -(7/2) a_7 identically in m."""
    a7, a8, a9 = (a_symbolic(j) for j in (7, 8, 9))
    assert sp.simplify(a7 - sp.Rational(8, 315) * Q) == 0
    assert sp.simplify(a8 + sp.Rational(28, 315) * Q) == 0
    assert sp.simplify(a9 - sp.Rational(4, 945) * Q * (2*m - 11) * (4*m - 9)) == 0
    # the ratio is degree-free: a_8 is a fixed multiple of a_7 at every m
    assert sp.simplify(a8 + sp.Rational(7, 2) * a7) == 0
    print("PASS a7 = 8Q/315, a8 = -28Q/315, a9 = 4Q(2m-11)(4m-9)/945; a8 = -(7/2)a7")


def check_closed_forms_against_definition():
    """The closed forms are identities: they match the integer lift at every m."""
    a = {j: a_symbolic(j) for j in (7, 8, 9)}
    for mm in list(range(3, 30)) + [40, 55, 90, 140]:
        for j in (7, 8, 9):
            assert lift_coeff_int(4, mm, j) == int(a[j].subs(m, mm)), (mm, j)
    print("PASS closed forms match the integer lift, m in 3..29 and 40, 55, 90, 140")


def check_against_the_m3_lift():
    """The closed forms reproduce the full m = 3 lift.

    An internal consistency pin -- the paper prints no such array: the closed
    forms must give 240, -840, -600 at indices 7, 8, 9 of the m=3 lift, whose
    first negative entry is the obstruction.
    """
    m3_lift = {3: 120, 4: 720, 5: 1680, 6: 1680, 7: 240, 8: -840, 9: -600, 10: -120}
    for j, v in m3_lift.items():
        assert lift_coeff_int(4, 3, j) == v, (j, v, lift_coeff_int(4, 3, j))
    for j in (7, 8, 9):
        assert int(a_symbolic(j).subs(m, 3)) == m3_lift[j], j
    # and nothing beyond index 10 survives: the lift has degree 10 at m = 3
    assert lift_coeffs_int(4, 3) == [0, 0, 0, 120, 720, 1680, 1680, 240, -840, -600, -120, 0]
    print("PASS closed forms reproduce the full m = 3 lift (240, -840, -600 at 7, 8, 9)")


def check_m4_certificate():
    """`subsec:first-supercritical-case`'s m=4 certificate, step by step.

        J^{(4)}_4(t) = 52 t^3 (1-t) * W(t),
        W(t) = 7t^8 - 14t^7 - 14t^6 - 14t^5 + 118t^4 - 14t^3 - 14t^2 - 14t + 7,

    W reciprocal, so with y = t + 1/t and z = y - 2 = (1-t)^2/t,

        t^-4 W(t) = 7y^4 - 14y^3 - 42y^2 + 28y + 160
                  = 7z^4 + 42z^3 + 42z^2 - 84z + 48
                  = 7z^4 + 42z^3 + 42(z-1)^2 + 6 > 0   for z > 0,

    hence J^{(4)}_4 > 0 on (0,1).  The regrouping is the whole content: the naive
    z-form has a negative linear term, and it is the completion of the square that
    removes it.
    """
    t, y, z = sp.symbols('t y z')

    def Jr(r, mm):
        nn = r*mm - 2
        return sum(sp.binomial(nn, r*k - 1) * t**(r*k - 1) * (sp.Integer(k) - (mm - k)*t)
                   for k in range(1, mm))

    J4 = sp.expand(Jr(4, 4))
    W = (7*t**8 - 14*t**7 - 14*t**6 - 14*t**5 + 118*t**4
         - 14*t**3 - 14*t**2 - 14*t + 7)
    assert sp.expand(J4 - 52*t**3*(1 - t)*W) == 0
    coeffs = sp.Poly(W, t).all_coeffs()
    assert coeffs == coeffs[::-1], coeffs
    print("PASS J^(4)_4 = 52 t^3 (1-t) W(t), with W reciprocal")

    Py = 7*y**4 - 14*y**3 - 42*y**2 + 28*y + 160
    assert sp.simplify(sp.expand(W / t**4) - Py.subs(y, t + 1/t)) == 0
    Pz = sp.expand(Py.subs(y, z + 2))
    assert Pz == sp.expand(7*z**4 + 42*z**3 + 42*z**2 - 84*z + 48)
    assert sp.expand(Pz - (7*z**4 + 42*z**3 + 42*(z - 1)**2 + 6)) == 0
    print("PASS t^-4 W = 7y^4-14y^3-42y^2+28y+160 = 7z^4+42z^3+42(z-1)^2+6")

    assert sp.simplify((t + 1/t - 2) - (1 - t)**2 / t) == 0
    # the regrouping is termwise positive for z > 0, so no numerics are needed;
    # spot-check the chain end to end at exact rationals anyway
    for num, den in [(1, 100), (1, 7), (1, 3), (1, 2), (3, 4), (99, 100)]:
        tv = sp.Rational(num, den)
        zv = (1 - tv)**2 / tv
        assert zv > 0
        assert 7*zv**4 + 42*zv**3 + 42*(zv - 1)**2 + 6 > 0
        assert W.subs(t, tv) > 0
        assert J4.subs(t, tv) > 0
    print("PASS z = (1-t)^2/t > 0 on (0,1), and the chain holds at exact rationals")

    # independent route: exact interior root counts, m=4 clean and m=3 not
    p4 = sp.Poly(J4, t)
    interior4 = p4.count_roots(0, 1) - sum(1 for b in (0, 1) if p4.eval(b) == 0)
    assert interior4 == 0, interior4
    p3 = sp.Poly(sp.expand(Jr(4, 3)), t)
    interior3 = p3.count_roots(0, 1) - sum(1 for b in (0, 1) if p3.eval(b) == 0)
    assert interior3 == 1, interior3
    print("PASS independent root count: J^(4)_4 has none in (0,1), J^(4)_3 has one")


def check_absorption_threshold():
    """A lead for the all-m target, not a claim the paper makes.

    The three-term group is nonnegative on xi >= 0 exactly when m >= 7.

    With a_7, a_9 > 0 the quadratic a_7 + a_8 x + a_9 x^2 is nonnegative iff its
    discriminant is, and that reduces to an integer quadratic in m.
    """
    a7, a8, a9 = (a_symbolic(j) for j in (7, 8, 9))
    disc = sp.simplify(4*a7*a9 - a8**2)
    # Q > 0 for m >= 3, so divide it out
    reduced = sp.simplify(sp.cancel(disc / Q**2))
    assert sp.simplify(reduced - sp.Rational(16, 297675) * (64*m**2 - 496*m + 645)) == 0
    print("PASS 4 a7 a9 - a8^2 = (16/297675) Q^2 (64 m^2 - 496 m + 645)")

    # its sign for every REAL m >= 7, by the same shift: 64(7+u)^2 - 496(7+u)
    # + 645 = 64u^2 + 400u + 309, every coefficient positive.  A sweep over
    # integers could not reach the reals between them.
    u = sp.symbols('u', nonnegative=True)
    quad_sym = 64*m**2 - 496*m + 645
    shifted = sp.Poly(sp.expand(quad_sym.subs(m, 7 + u)), u)
    assert shifted.all_coeffs() == [64, 400, 309], shifted.all_coeffs()
    assert all(c > 0 for c in shifted.all_coeffs())
    # and 7 is the least integer that works: the larger root is (31 + 2 sqrt(79))/8,
    # which lies strictly between 6 and 7
    x = sp.Symbol('x')                     # m carries integer=True, so solve on a free symbol
    roots = sorted(sp.solve(sp.Eq(quad_sym.subs(m, x), 0), x))
    assert len(roots) == 2, roots
    assert sp.simplify(roots[1] - (sp.Rational(31, 8) + sp.sqrt(79) / 4)) == 0, roots
    assert sp.Integer(6) < roots[1] < sp.Integer(7)
    # and the smaller root sits below 2, so no integer m >= 3 falls between them
    assert sp.Integer(1) < roots[0] < sp.Integer(2), roots[0]
    assert all(quad_sym.subs(m, v) < 0 for v in (2, 3, 4, 5, 6)), 'sign inside the roots'
    quad = lambda v: 64*v*v - 496*v + 645
    for v in range(3, 7):
        assert quad(v) < 0, v
    print("PASS 64m^2-496m+645 = 64u^2+400u+309 at m = 7+u, so > 0 for every real "
          "m >= 7, with largest root (31+2*sqrt(79))/8 in (6,7); < 0 at m = 3..6")

    # and a_9 >= 0 needs m >= 6, which m >= 7 already gives, so the threshold is m >= 7
    for v in range(3, 60):
        a9v = int(a_symbolic(9).subs(m, v))
        a7v = int(a_symbolic(7).subs(m, v))
        absorbs = (a7v >= 0) and (a9v >= 0) and quad(v) >= 0
        assert absorbs == (v >= 7), (v, a7v, a9v, quad(v))
    print("PASS the group absorbs the negative coefficient exactly for m >= 7")


def check_group_nonneg_pointwise():
    """Directly: a_7 xi^7 + a_8 xi^8 + a_9 xi^9 >= 0 on xi > 0 iff m >= 7."""
    for v in [3, 4, 5, 6, 7, 8, 12, 25]:
        a7v, a8v, a9v = (int(a_symbolic(j).subs(m, v)) for j in (7, 8, 9))
        # the quadratic's minimizer over xi > 0, as an exact rational when a9v > 0
        if a9v > 0:
            x0 = sp.Rational(-a8v, 2*a9v)
            val = a7v + a8v*x0 + a9v*x0**2
            assert (val >= 0) == (v >= 7), (v, val)
        else:
            # a9 <= 0: the group is eventually negative, so it cannot absorb.
            # Evaluated, not inferred -- at a large exact rational the leading
            # term dominates and the group is negative there.
            assert v < 7, v
            xi = sp.Rational(10 ** 6)
            val = a7v + a8v * xi + a9v * xi ** 2
            assert val < 0, (v, a7v, a8v, a9v, val)
    print("PASS the pointwise minimum of the group over xi > 0 confirms the "
          "threshold, and where a_9 <= 0 the group is negative at xi = 10^6")


def check_r4_certificate_holds_only_at_m_two():
    """The r=4 failure starts at m=3, and m=2 is the boundary case.

    At m=2 the lift is 20xi^3 + 60xi^4 + 60xi^5 + 20xi^6, every coefficient
    nonnegative, so the Bernstein-basis certificate DOES hold there -- the closed
    forms above carry a factor (m-2) and give a_7 = a_8 = 0.  The paper's claim is
    therefore scoped to m >= 3, and this is the assert that holds it to that scope.
    """
    L2 = lift_coeffs_int(4, 2)
    assert L2 == [0, 0, 0, 20, 60, 60, 20, 0], L2
    assert all(v >= 0 for v in L2)
    assert int(a_symbolic(7).subs(m, 2)) == 0
    assert int(a_symbolic(8).subs(m, 2)) == 0
    print("PASS at m=2 the lift is nonnegative and a_7 = a_8 = 0: the certificate holds")

    # from m=3 on it fails, and by the single coefficient at index 8
    for mm in range(3, 31):
        a = lift_coeffs_int(4, mm)
        neg = [j for j, v in enumerate(a) if v < 0]
        assert 8 in neg, (mm, neg)
        if mm >= 6:
            assert neg == [8], (mm, neg)
    print("PASS at r=4 index 8 is negative for m = 3..30, and is the only one for m >= 6")
    # the r=3 contrast: the certificate does hold
    for mm in range(2, 21):
        a = lift_coeffs_int(3, mm)
        assert all(v >= 0 for v in a), (mm, [j for j, v in enumerate(a) if v < 0])
    print("PASS at r=3 every lifted coefficient is nonnegative for m = 2..20")


def main():
    check_Q_positive_for_all_m_at_least_three()
    check_closed_forms()
    check_closed_forms_against_definition()
    check_against_the_m3_lift()
    check_m4_certificate()
    check_absorption_threshold()
    check_group_nonneg_pointwise()
    check_r4_certificate_holds_only_at_m_two()
    print("ALL PASS")


if __name__ == "__main__":
    main()
