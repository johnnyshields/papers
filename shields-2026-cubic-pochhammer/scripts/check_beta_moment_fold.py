#!/usr/bin/env python3
r"""Paper section `sec:reduction` (Exact reduction to a residue kernel): the beta-moment route
through `eq:C-beta` and `lem:beta-order`.

`sec:reduction`'s own derivation runs through the beta-binomial law: `eq:C-beta-binomial` turns
the coefficient convolution `eq:C-def` into an expectation over J, `eq:C-beta`
mixes it against P ~ Beta(u,v), and `lem:beta-order` compares two such expectations by
a likelihood-ratio order in the centrality coordinate q = p(1-p).
verify_beta_binomial.py and verify_monotonicity_lemmas.py follow exactly that
route; check_fixed_sum_schur.py checks its conclusion.

This script probes a *different* route to the same two statements -- one that
never leaves the p-coordinate and never names a probability law.  It is the
route the Lean development takes (../lean/CubicPochhammer/BetaOrder.lean,
Bridge.Aint_eq), so the steps checked here are the load-bearing ones there:

  1. Beta-moment shift.  B(a+j, b+k) (a+b)_{j+k} = (a)_j (b)_k B(a,b), the only
     property of the beta function the reduction uses.  Checked exactly and
     symbolically in (a,b).
  2. The cleared form of `eq:C-beta`.  With
        A(u,v) = int_0^1 G_{m,w}(p) p^{u-1} (1-p)^{v-1} dp,
     A(u,v) (u+v)_{3m} = (3m-2)! B(u,v) C_{m,w}(u,v).  Checked by quadrature
     against `eq:C-def`, and again exactly once the integral is expanded
     term by term.  No weight symmetry is used, and asymmetric weights are
     included to show none is needed.
  3. Folding onto [1/2,1].  For symmetric weights,
        int_0^1 H p^{u-1}(1-p)^{v-1} = int_{1/2}^1 H (rho(p) + rho(1-p)),
     and the same with H = 1.  Symmetry of H is load-bearing: the boundary
     probe shows the identity failing at asymmetric weights.
  4. The closed form of the folded kernel,
        rho_d(p) + rho_d(1-p) = 2 (p(1-p))^{s/2-1} cosh(d * logit p),
     which is where cosh enters without a change of variables.
  5. The cross-multiplied cosh inequality
        cosh(d2 x) cosh(d1 y) <= cosh(d2 y) cosh(d1 x)   (0 <= d1 <= d2, 0 <= x <= y),
     with both hypotheses probed at their boundary: it reverses when d1 > d2,
     and it fails when x is allowed below 0.
  6. Single crossing.  Z1 F2 - Z2 F1 is negative then positive on [1/2,1), with
     exactly one sign change and total integral zero -- the statement `lem:beta-order`
     reaches through lr order, here reached from step 5 alone.
  7. End to end.  d |-> C_{m,w}(s/2+d, s/2-d) is nonincreasing, recomputed
     through the beta-moment quotient of step 2 rather than from `eq:C-def`.

Numerical work is mpmath at 40 digits; the algebra of steps 1 and 2 is exact
in SymPy.
"""
from __future__ import annotations

from math import comb, factorial

import mpmath as mp
import sympy as sp

mp.mp.dps = 40

TOL = mp.mpf("1e-25")


def R(a: int, b: int) -> mp.mpf:
    """Exact rational as an mpf, so no float64 rounding enters an input."""
    return mp.mpf(a) / mp.mpf(b)


# Symmetric weight families, w_r = w_{m-r} on 1 <= r <= m-1, nondecreasing
# toward the center: the hypothesis `eq:w-monotone` of `cor:C-schur`.
SYM = [
    (2, {1: R(1, 1)}),
    (3, {1: R(1, 1), 2: R(1, 1)}),
    (4, {1: R(1, 1), 2: R(2, 1), 3: R(1, 1)}),
    (5, {1: R(1, 2), 2: R(3, 1), 3: R(3, 1), 4: R(1, 2)}),
    (6, {1: R(1, 1), 2: R(2, 1), 3: R(5, 2), 4: R(2, 1), 5: R(1, 1)}),
]

# Asymmetric families: `eq:C-beta` needs no symmetry, the fold does.
ASYM = [
    (3, {1: R(1, 1), 2: R(3, 1)}),
    (4, {1: R(1, 1), 2: R(2, 1), 3: R(7, 2)}),
]

PARAMS = [(R(7, 10), R(13, 10)), (R(2, 1), R(7, 2)), (R(1, 4), R(1, 4)),
          (R(4, 1), R(1, 1)), (R(1, 20), R(9, 4))]


def poch(u, k: int):
    out = mp.mpf(1)
    for i in range(k):
        out *= u + i
    return out


def Cmw(m: int, w: dict, u, v):
    """`eq:C-def` at arbitrary weights."""
    return mp.fsum(
        w[r] * poch(u, 3 * r) * poch(v, 3 * (m - r))
        / (mp.mpf(factorial(3 * r - 1)) * mp.mpf(factorial(3 * (m - r) - 1)))
        for r in range(1, m)
    )


def Gmw(m: int, w: dict, p):
    """`eq:G-weighted`."""
    return mp.fsum(
        w[r] * comb(3 * m - 2, 3 * r - 1) * p ** (3 * r) * (1 - p) ** (3 * (m - r))
        for r in range(1, m)
    )


def Bmom(a, b):
    return mp.gamma(a) * mp.gamma(b) / mp.gamma(a + b)


def betaKer(s, d, p):
    return p ** (s / 2 + d - 1) * (1 - p) ** (s / 2 - d - 1)


def foldKer(s, d, p):
    return betaKer(s, d, p) + betaKer(s, d, 1 - p)


def logit(p):
    return mp.log(p) - mp.log(1 - p)


# --- quadrature with the endpoint singularities substituted away ----------
# p^(a-1) and (1-p)^(b-1) are non-smooth at their own endpoint whenever the
# exponent is negative, and at b = 1/100 plain tanh-sinh over [0,1/2,1] is off
# by 20% however far the degree is pushed.  Substituting p = t^(1/a) on [0,1/2]
# turns p^(a-1) dp into dt/a exactly, and 1-p = t^(1/b) does the same at the
# other end, leaving a smooth integrand on each half.
def left_quad(a, b, f):
    """int_0^(1/2) p^(a-1) (1-p)^(b-1) f(p) dp."""
    half = mp.mpf(1) / 2
    return mp.quad(lambda t: (1 - t ** (1 / a)) ** (b - 1) * f(t ** (1 / a)),
                   [0, half ** a]) / a


def half_quad(a, b, f):
    """int_(1/2)^1 p^(a-1) (1-p)^(b-1) f(p) dp."""
    half = mp.mpf(1) / 2
    return mp.quad(lambda t: (1 - t ** (1 / b)) ** (a - 1) * f(1 - t ** (1 / b)),
                   [0, half ** b]) / b


def full_quad(a, b, f):
    """int_0^1 p^(a-1) (1-p)^(b-1) f(p) dp."""
    return left_quad(a, b, f) + half_quad(a, b, f)


def fold_quad(a, b, f):
    """int_(1/2)^1 (rho(p) + rho(1-p)) f(p) dp, rho = p^(a-1)(1-p)^(b-1).

    Deliberately a different rule from full_quad: one substitution
    1-p = t^(1/c), c = min(a,b), applied to the whole folded integrand, so the
    fold identity is not checked by comparing an expression against itself.
    """
    c = min(a, b)
    half = mp.mpf(1) / 2

    def g(t):
        q = t ** (1 / c)                     # q = 1-p
        pp = 1 - q
        return (pp ** (a - 1) * q ** (b - 1) + q ** (a - 1) * pp ** (b - 1)) \
            * q ** (1 - c) / c * f(pp)

    return mp.quad(g, [0, half ** c])


def Aint(m: int, w: dict, u, v):
    return full_quad(u, v, lambda p: Gmw(m, w, p))


def rel(x, y):
    return abs(x - y) / abs(y) if y != 0 else abs(x - y)


# ===========================================================================
# 1.  The beta-moment shift, exactly and symbolically
# ===========================================================================
def check_bmom_shift() -> None:
    """B(a+j, b+k) (a+b)_{j+k} = (a)_j (b)_k B(a,b), symbolic in (a,b).

    This is the only fact about the beta function the reduction consumes; the
    Lean counterpart is BetaOrder.Bmom_shift, proved from Gamma(a+1) = a Gamma(a).
    """
    a, b = sp.symbols("a b", positive=True)
    B = lambda x, y: sp.gamma(x) * sp.gamma(y) / sp.gamma(x + y)
    checked = 0
    for j in range(0, 9):
        for k in range(0, 9):
            lhs = B(a + j, b + k) * sp.rf(a + b, j + k)
            rhs = sp.rf(a, j) * sp.rf(b, k) * B(a, b)
            assert sp.simplify(sp.expand_func(lhs - rhs)) == 0, (j, k)
            checked += 1
    print(f"PASS  beta-moment shift B(a+j,b+k)(a+b)_(j+k) = (a)_j (b)_k B(a,b), "
          f"symbolic in (a,b), over {checked} shift pairs")


# ===========================================================================
# 2.  `eq:C-beta` with the normalizations cleared
# ===========================================================================
def check_star_identity_quadrature() -> None:
    """A(u,v) (u+v)_{3m} = (3m-2)! B(u,v) C_{m,w}(u,v), by quadrature.

    Independent of `eq:C-def` only through the integral: the left side is
    computed from `eq:G-weighted` by quadrature, the right from `eq:C-def` in closed
    form.  Asymmetric weights are included: the identity needs no symmetry.
    """
    worst = mp.mpf(0)
    n = 0
    for m, w in SYM + ASYM:
        for u, v in PARAMS:
            lhs = Aint(m, w, u, v) * poch(u + v, 3 * m)
            rhs = mp.mpf(factorial(3 * m - 2)) * Bmom(u, v) * Cmw(m, w, u, v)
            assert rhs > 0, (m, u, v)
            r = rel(lhs, rhs)
            worst = max(worst, r)
            assert r < TOL, (m, u, v, mp.nstr(r, 8))
            n += 1
    assert worst > 0, "quadrature agreed to the last bit everywhere -- suspect"
    print(f"PASS  `eq:C-beta` cleared: A(u,v)(u+v)_(3m) = (3m-2)! B(u,v) C, "
          f"quadrature over {n} cases, worst relative gap {mp.nstr(worst, 4)}")


def check_star_identity_exact() -> None:
    """The same identity, exactly, once the integral is expanded term by term.

    Term by term the integral is sum_r w_r C(3m-2,3r-1) B(u+3r, v+3(m-r)); the
    remaining content is the shift of step 1 against
    C(3m-2,3r-1)(3r-1)![3(m-r)-1]! = (3m-2)!, and that is what is checked here,
    symbolically in (u,v) and in the weights.
    """
    u, v = sp.symbols("u v", positive=True)
    B = lambda x, y: sp.gamma(x) * sp.gamma(y) / sp.gamma(x + y)
    for m in range(2, 7):
        ws = sp.symbols(f"w1:{m}")  # w_1 ... w_{m-1}
        lhs = sum(ws[r - 1] * sp.binomial(3 * m - 2, 3 * r - 1)
                  * B(u + 3 * r, v + 3 * (m - r)) for r in range(1, m))
        lhs *= sp.rf(u + v, 3 * m)
        C = sum(ws[r - 1] * sp.rf(u, 3 * r) * sp.rf(v, 3 * (m - r))
                / (sp.factorial(3 * r - 1) * sp.factorial(3 * (m - r) - 1))
                for r in range(1, m))
        rhs = sp.factorial(3 * m - 2) * B(u, v) * C
        assert sp.simplify(sp.expand_func(lhs - rhs)) == 0, m
        # the factorial bookkeeping the reduction rests on, stated on its own
        for r in range(1, m):
            assert (comb(3 * m - 2, 3 * r - 1) * factorial(3 * r - 1)
                    * factorial(3 * (m - r) - 1) == factorial(3 * m - 2)), (m, r)
    print("PASS  `eq:C-beta` cleared, exactly: the term-by-term beta sum reduces "
          "to `eq:C-def`, symbolic in (u,v) and in the weights, m = 2..6")


# ===========================================================================
# 3.  Folding onto [1/2,1]
# ===========================================================================
def check_fold() -> None:
    """int_0^1 H rho = int_{1/2}^1 H (rho(p)+rho(1-p)) for symmetric H, and the
    same at H = 1.  The Lean counterpart is BetaOrder.integral_fold.
    """
    cases = [(R(2, 1), R(3, 10)), (R(5, 1), R(6, 5)), (R(3, 5), R(1, 5)),
             (R(1, 10), R(1, 25))]
    worst = mp.mpf(0)
    n = 0
    for m, w in SYM:
        H = lambda p, m=m, w=w: Gmw(m, w, p)
        for s, d in cases:
            a, b = s / 2 + d, s / 2 - d
            lhs = full_quad(a, b, H)
            rhs = fold_quad(a, b, H)
            worst = max(worst, rel(lhs, rhs))
            assert rel(lhs, rhs) < TOL, (m, s, d, "H")
            one = lambda p: mp.mpf(1)
            lb = full_quad(a, b, one)
            rb = fold_quad(a, b, one)
            worst = max(worst, rel(lb, rb))
            assert rel(lb, rb) < TOL, (m, s, d, "1")
            # and the unfolded normalization is the beta function
            assert rel(lb, Bmom(a, b)) < TOL, (s, d)
            n += 1
    print(f"PASS  fold onto [1/2,1] for symmetric G_(m,w) and for H = 1, "
          f"{n} cases, worst relative gap {mp.nstr(worst, 4)}")


def check_fold_needs_symmetry() -> None:
    """Boundary probe: the fold fails at asymmetric weights.

    The identity uses H(1-p) = H(p) once, so an asymmetric G_{m,w} must break
    it; if it did not, step 3 would be checking nothing.
    """
    s, d = R(5, 1), R(6, 5)
    broke = []
    a, b = s / 2 + d, s / 2 - d
    for m, w in ASYM:
        H = lambda p, m=m, w=w: Gmw(m, w, p)
        broke.append(rel(full_quad(a, b, H), fold_quad(a, b, H)))
    assert all(g > mp.mpf("1e-3") for g in broke), broke
    print(f"PASS  fold is not vacuous: asymmetric weights break it, relative "
          f"gaps {[mp.nstr(g, 4) for g in broke]}")


# ===========================================================================
# 4.  The folded kernel in closed form
# ===========================================================================
def check_foldker_cosh() -> None:
    """rho_d(p) + rho_d(1-p) = 2 (p(1-p))^{s/2-1} cosh(d logit p).

    The Lean counterpart is BetaOrder.foldKer_eq_cosh.  This is where cosh
    enters: the paper reaches it after the change of variables q = p(1-p), and
    here it is an identity in p.
    """
    worst = mp.mpf(0)
    n = 0
    for s in [R(2, 1), R(5, 1), R(3, 5), R(1, 10)]:
        for d in [R(0, 1), R(1, 5), R(2, 5)]:
            if d >= s / 2:
                continue
            for p in [R(1, 100), R(1, 5), R(2, 5), R(1, 2), R(3, 5), R(99, 100)]:
                lhs = foldKer(s, d, p)
                rhs = 2 * (p * (1 - p)) ** (s / 2 - 1) * mp.cosh(d * logit(p))
                worst = max(worst, rel(lhs, rhs))
                assert rel(lhs, rhs) < TOL, (s, d, p)
                n += 1
    print(f"PASS  folded kernel = 2 (p(1-p))^(s/2-1) cosh(d logit p), {n} "
          f"points, worst relative gap {mp.nstr(worst, 4)}")


# ===========================================================================
# 5.  The cross-multiplied cosh inequality, and both its hypotheses
# ===========================================================================
def check_cosh_cross() -> None:
    """cosh(d2 x) cosh(d1 y) <= cosh(d2 y) cosh(d1 x) for 0<=d1<=d2, 0<=x<=y.

    The Lean counterpart is BetaOrder.cosh_ratio_cross, proved from
    2 cosh A cosh B = cosh(A+B) + cosh(A-B) together with
    |d2 x +- d1 y| <= |d2 y +- d1 x|.  Both of those bounds are asserted here
    too, since they are the whole proof.
    """
    grid = [R(0, 1), R(1, 10), R(1, 2), R(1, 1), R(7, 3), R(5, 1)]
    n = 0
    strict = 0
    for d1 in grid:
        for d2 in grid:
            if d2 < d1:
                continue
            for x in grid:
                for y in grid:
                    if y < x:
                        continue
                    lhs = mp.cosh(d2 * x) * mp.cosh(d1 * y)
                    rhs = mp.cosh(d2 * y) * mp.cosh(d1 * x)
                    assert lhs <= rhs + TOL, (d1, d2, x, y)
                    if rhs - lhs > mp.mpf("1e-12"):
                        strict += 1
                    assert abs(d2 * x + d1 * y) <= abs(d2 * y + d1 * x) + TOL
                    assert abs(d2 * x - d1 * y) <= abs(d2 * y - d1 * x) + TOL
                    n += 1
    assert strict > 0, "every instance was an equality -- the grid says nothing"
    print(f"PASS  cross-multiplied cosh inequality over {n} quadruples "
          f"({strict} strict), with the two |.| bounds behind it")


def check_cosh_cross_hypotheses() -> None:
    """Boundary probes: the inequality reverses at d1 > d2, and fails for x < 0.

    `lem:beta-order` compares a larger imbalance against a smaller one, on the half
    where the logit is nonnegative.  Both restrictions are real.
    """
    d1, d2, x, y = R(3, 1), R(1, 1), R(1, 2), R(2, 1)      # d1 > d2
    assert mp.cosh(d2 * x) * mp.cosh(d1 * y) > mp.cosh(d2 * y) * mp.cosh(d1 * x)
    d1, d2, x, y = R(1, 1), R(3, 1), R(-2, 1), R(1, 2)     # x < 0 <= y
    assert mp.cosh(d2 * x) * mp.cosh(d1 * y) > mp.cosh(d2 * y) * mp.cosh(d1 * x)
    print("PASS  cross-multiplied cosh inequality is sharp in its hypotheses: "
          "it reverses at d1 > d2 and at x < 0")


# ===========================================================================
# 6.  Single crossing of Z1 F2 - Z2 F1 on [1/2,1)
# ===========================================================================
def check_single_crossing() -> None:
    """g = Z1 foldKer(d2) - Z2 foldKer(d1) is negative then positive, once.

    Z_i is the integral of foldKer(d_i) over [1/2,1], so int g = 0; the sign
    pattern is what BetaOrder.exists_crossing derives from step 5, and it is
    the substance of `lem:beta-order` in this route.
    """
    n = 0
    for s in [R(2, 1), R(5, 1), R(3, 5)]:
        for d1, d2 in [(R(0, 1), R(1, 5)), (R(1, 10), R(2, 5)),
                       (R(0, 1), R(9, 20))]:
            if d2 >= s / 2:
                continue
            one = lambda p: mp.mpf(1)
            Z1 = fold_quad(s / 2 + d1, s / 2 - d1, one)
            Z2 = fold_quad(s / 2 + d2, s / 2 - d2, one)
            assert rel(Z1, Bmom(s / 2 + d1, s / 2 - d1)) < TOL, (s, d1)
            assert rel(Z2, Bmom(s / 2 + d2, s / 2 - d2)) < TOL, (s, d2)
            g = lambda p: Z1 * foldKer(s, d2, p) - Z2 * foldKer(s, d1, p)
            total = (Z1 * fold_quad(s / 2 + d2, s / 2 - d2, one)
                     - Z2 * fold_quad(s / 2 + d1, s / 2 - d1, one))
            assert abs(total) < TOL * Z1 * Z2, (s, d1, d2, total)
            grid = [R(1, 2) + R(1, 2) * R(i, 400) for i in range(0, 400)]
            signs = [mp.sign(g(p)) for p in grid]
            nonzero = [x for x in signs if x != 0]
            changes = sum(1 for a, b in zip(nonzero, nonzero[1:]) if a != b)
            assert changes == 1, (s, d1, d2, changes)
            assert nonzero[0] < 0 < nonzero[-1], (s, d1, d2)
            n += 1
    print(f"PASS  single crossing of Z1 F2 - Z2 F1 on [1/2,1), sign - then +, "
          f"integral zero, over {n} parameter triples")


# ===========================================================================
# 7.  End to end: `eq:fixed-sum` monotone in the imbalance, via the beta moment
# ===========================================================================
def check_end_to_end() -> None:
    """C_{m,w}(s/2+d, s/2-d) recomputed as (s)_{3m}/(3m-2)! * A/B, and
    nonincreasing in d.  This is `cor:C-schur` `eq:w-from-f` on the interior, reached
    through steps 2 and 6 rather than through `eq:C-def`.
    """
    ds = [R(0, 1), R(1, 10), R(1, 5), R(3, 10), R(2, 5), R(9, 20)]
    n = 0
    for m, w in SYM:
        for s in [R(2, 1), R(5, 1), R(3, 5)]:
            vals = []
            for d in ds:
                if d >= s / 2:
                    continue
                u, v = s / 2 + d, s / 2 - d
                direct = Cmw(m, w, u, v)
                viaint = (poch(s, 3 * m) / mp.mpf(factorial(3 * m - 2))
                          * Aint(m, w, u, v) / Bmom(u, v))
                assert rel(viaint, direct) < TOL, (m, s, d)
                vals.append(direct)
                n += 1
            for a, b in zip(vals, vals[1:]):
                assert b <= a + TOL * a, (m, s, a, b)
            assert vals[-1] < vals[0], (m, s)
    print(f"PASS  `cor:C-schur` `eq:w-from-f` on the interior: C via the beta-moment "
          f"quotient matches `eq:C-def` and falls with the imbalance, {n} points")


def main() -> None:
    check_bmom_shift()
    check_star_identity_quadrature()
    check_star_identity_exact()
    check_fold()
    check_fold_needs_symmetry()
    check_foldker_cosh()
    check_cosh_cross_hypotheses()
    check_cosh_cross()
    check_single_crossing()
    check_end_to_end()
    print("ALL PASS  check_beta_moment_fold.py")


if __name__ == "__main__":
    main()
