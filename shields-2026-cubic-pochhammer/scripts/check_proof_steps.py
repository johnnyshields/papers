#!/usr/bin/env python3
r"""Paper sections `sec:reduction`, `sec:kernel`, `sec:cubic-proof` and
`sec:consequences`: the proof steps that are displayed rather than asserted.

Four displays state a *step* whose conclusion another script already covers.  Each
is checked here against the objects that define it, never transcribed.

  * `lem:bernstein` states the value of the second Bernstein coefficient,
    `b_2 = (n-1)/(n+1)`.  `verify_kernel.py` carries the reconstruction
    `b_j = S_{n,j}/(3(n+1))` and the positivity of the `xi^2` coefficient.
  * `lem:central-products` derives `eq:central-products` through the ratios `rho_j = f_{j+1}/f_j`
    rather than through a cross-product asserted to be standard.  The route needs
    `k <= m-k-1`, and it needs interval support: without it the step is FALSE, and
    the witness is `rem:internal-zeros`' own sequence.  The paper states the
    characterization as an equivalence; the converse direction (2) => (1) is in
    `verify_beta_binomial.py`.
  * `cor:C-schur` is stated on the CLOSED range `0 <= d <= s/2`, for arbitrary
    weights satisfying `eq:w-monotone`.
  * `cor:ordinary`'s proof splits finite from infinite support for `R > 0`, and
    bounds the gamma ratio by the explicit majorant
    `(mu)_{3n}/(3n-1)! <= M e^M (3n)^M` on `0 <= mu <= M`, followed by a
    Weierstrass test.

Exact throughout: `sympy` over the rationals and `math.comb` over the integers.
The one transcendental comparison, against `M e^M`, is done in `mpmath` at 60
digits; there is no float64 anywhere.
"""

from fractions import Fraction
from math import comb

import mpmath as mp
import sympy as sp

mp.mp.dps = 60


def poch(a, j):
    out = sp.Integer(1)
    for i in range(j):
        out *= a + i
    return out


def S_sum(n, j):
    """`eq:S-def`: S_{n,j} = sum_{nu <= j, nu = 2 (3)} C(j,nu)(n-nu+1)(2nu+1-j)."""
    return sum(comb(j, nu) * (n - nu + 1) * (2 * nu + 1 - j)
               for nu in range(j + 1) if nu % 3 == 2)


def Jm(m, t):
    n = 3 * m - 2
    return sum(sp.Integer(comb(n, 3 * k - 1)) * t ** (3 * k - 1) * (k - (m - k) * t)
               for k in range(1, m))


def Cmw(w, m, u, v):
    """`eq:C-def`."""
    return sum(w[k] * poch(u, 3 * k) * poch(v, 3 * (m - k))
               / (sp.factorial(3 * k - 1) * sp.factorial(3 * (m - k) - 1))
               for k in range(1, m))


# ---------------------------------------------------------------- `lem:bernstein`

def check_b_two_closed_value():
    """`lem:bernstein`: b_2 = (n-1)/(n+1) > 0, from the Bernstein expansion itself."""
    t = sp.Symbol("t")
    for m in range(2, 26):
        n = 3 * m - 2
        N = n + 1
        b = [sp.Rational(S_sum(n, j), 3 * (n + 1)) for j in range(N + 1)]
        # the expansion `lem:bernstein` displays
        recon = sp.expand(sum(b[j] * comb(N, j) * t ** j * (1 - t) ** (N - j)
                              for j in range(N + 1)))
        assert sp.expand(recon - Jm(m, t)) == 0, m
        assert all(x >= 0 for x in b), (m, [j for j, x in enumerate(b) if x < 0])
        # the closed value, and the identity 3 S_{n,2} = 9(n-1) behind it
        assert 3 * S_sum(n, 2) == 9 * (n - 1), m
        assert b[2] == sp.Rational(n - 1, n + 1), (m, b[2])
        assert b[2] > 0, m
        # delta = 0 at the top index, where the table's j = 0,1 branches would be
        # negative; n+1 = 3m-1 is 2 or 5 mod 6, so that index is never reached
        assert N % 6 in (2, 5), (m, N % 6)
        assert b[N] == 0, (m, b[N])
    print("PASS  `lem:bernstein`: b_j >= 0 with b_2 = (n-1)/(n+1) > 0, and the "
          "expansion reconstructs J_m exactly (m = 2..25)")


# ----------------------------------------------------------------- `thm:main`

def check_rho_route_to_weight_monotonicity():
    """`lem:central-products`: w_{k+1}/w_k = rho_k/rho_{m-k-1}, and k <= m-k-1."""
    f = sp.symbols("f1:60", positive=True)
    for m in range(4, 20):
        for k in range(1, m // 2):
            assert k <= m - k - 1, (m, k)
            w_k, w_k1 = f[k - 1] * f[m - k - 1], f[k] * f[m - k - 2]
            rho_k, rho_mk1 = f[k] / f[k - 1], f[m - k - 1] / f[m - k - 2]
            assert sp.simplify(w_k1 / w_k - rho_k / rho_mk1) == 0, (m, k)
    print("PASS  `lem:central-products`: w_{k+1}/w_k = rho_k/rho_{m-k-1} identically, and "
          "k <= m-k-1 for 1 <= k < floor(m/2) (m = 4..19)")


def check_rho_nonincreasing_gives_the_step():
    """On an interval support, rho nonincreasing plus k <= m-k-1 gives w_{k+1} >= w_k."""
    seqs = {
        "geometric 1/2": {n: Fraction(1, 2) ** n for n in range(1, 24)},
        "constant": {n: Fraction(1) for n in range(1, 24)},
        "1/n!": {n: Fraction(1, 1) / Fraction(int(sp.factorial(n))) for n in range(1, 16)},
        "binomial row 20": {n: Fraction(comb(20, n)) for n in range(1, 21)},
        "window 5..14, constant": {n: (Fraction(1) if 5 <= n <= 14 else Fraction(0))
                                   for n in range(1, 24)},
        "window 5..14, binomial": {n: (Fraction(comb(9, n - 5)) if 5 <= n <= 14
                                       else Fraction(0)) for n in range(1, 24)},
    }
    for name, f in seqs.items():
        top = max(f)
        # the family must satisfy the hypothesis it is testing: log-concave with
        # interval support.  (f_n = 1/n is log-CONVEX and belongs to no such list.)
        sup = sorted(n for n, v in f.items() if v > 0)
        assert sup == list(range(sup[0], sup[-1] + 1)), (name, sup)
        for n in range(2, top):
            assert f.get(n, Fraction(0)) ** 2 >= (f.get(n - 1, Fraction(0))
                                                 * f.get(n + 1, Fraction(0))), (name, n)
        for m in range(4, top + 2):
            w = {k: f.get(k, Fraction(0)) * f.get(m - k, Fraction(0))
                 for k in range(1, m)}
            for k in range(1, m // 2):
                assert w[k + 1] >= w[k], (name, m, k, w[k], w[k + 1])
    print("PASS  `lem:central-products`: `eq:central-products` holds for every log-concave interval-support "
          f"sequence tested ({len(seqs)} families)")


def check_interval_support_is_load_bearing_at_this_step():
    """Without interval support the step is FALSE -- `rem:internal-zeros`' witness."""
    f = {1: Fraction(1), 4: Fraction(1)}
    m = 5
    w = {k: f.get(k, Fraction(0)) * f.get(m - k, Fraction(0)) for k in range(1, m)}
    assert w == {1: Fraction(1), 2: Fraction(0), 3: Fraction(0), 4: Fraction(1)}
    assert w[2] < w[1], w            # `eq:central-products` fails at k = 1
    # log-concavity itself is NOT violated: every triple has a vanishing side
    for n in range(2, 6):
        assert f.get(n, Fraction(0)) ** 2 >= f.get(n - 1, Fraction(0)) * f.get(n + 1, Fraction(0))
    # and rho_1 is undefined precisely because f_2 = 0, which is where the
    # case split sends this sequence
    assert f.get(2, Fraction(0)) == 0
    print("PASS  `rem:internal-zeros`: at f_1=f_4=1 the rho step is unavailable and `eq:central-products` "
          "fails (w_1=1 > w_2=0) -- interval support is load-bearing here")


# ---------------------------------------------------------------- `cor:C-schur`

def check_cor_closed_range():
    """`cor:C-schur`: nonincreasing, and strictly so, on [0, s/2]."""
    s = sp.Symbol("s", positive=True)
    for m in range(2, 8):
        wsym = {k: sp.Symbol(f"w{k}", positive=True) for k in range(1, m)}
        assert sp.expand(Cmw(wsym, m, s, sp.Integer(0))) == 0, m
        assert sp.expand(Cmw(wsym, m, sp.Integer(0), s)) == 0, m
    # weights are built from a half-vector so they are symmetric by construction;
    # each family is then checked against `eq:w-monotone` before it is used
    halves = {
        "centrally increasing": lambda L: [sp.Rational(1, L - j + 1) for j in range(1, L + 1)],
        "constant": lambda L: [sp.Integer(1)] * L,
        "center only": lambda L: [sp.Integer(0)] * (L - 1) + [sp.Integer(1)],
        "all zero": lambda L: [sp.Integer(0)] * L,
    }
    endpoints = 0
    for m in range(2, 8):
        L = m // 2
        for name, hv in halves.items():
            v = hv(L)
            w = {k: v[min(k, m - k) - 1] for k in range(1, m)}
            assert all(w[k] == w[m - k] for k in range(1, m)), (m, name)
            assert all(v[i] <= v[i + 1] for i in range(L - 1)), (m, name)
            assert all(x >= 0 for x in v), (m, name)
            nonzero = any(w[k] != 0 for k in w)
            for sv in [sp.Integer(1), sp.Rational(7, 2), sp.Integer(9)]:
                grid = [sp.Rational(q, 5) * sv / 2 for q in range(6)]
                vals = [Cmw(w, m, sv / 2 + d, sv / 2 - d) for d in grid]
                for q in range(len(vals) - 1):
                    diff = sp.nsimplify(vals[q] - vals[q + 1], rational=True)
                    if nonzero:
                        assert diff > 0, (m, name, sv, q, diff)
                    else:
                        assert diff == 0, (m, name, sv, q)
                assert sp.nsimplify(vals[-1], rational=True) == 0, (m, name, sv)
                endpoints += 1
    print("PASS  `cor:C-schur`: monotone on the CLOSED [0, s/2], strictly when the "
          f"weights are not all zero, endpoint value 0 (m = 2..7, {endpoints} cases)")


# --------------------------------------------------------------- `cor:ordinary`

def check_radius_positive_both_supports():
    """`cor:ordinary`: R = infinity on finite support; R > 0 via f_n <= f_a rho_a^{n-a}."""
    # Finite support makes F_f a polynomial, so its partial sums stop moving at
    # the top of the support however large x is -- that is R = infinity.  The
    # test has teeth because the identical sweep is run below on a geometric f,
    # whose radius is finite and whose partial sums then grow without bound.
    def partials(coeff, x, cutoffs):
        return [sum(coeff(n) * x ** n for n in range(N)) for N in cutoffs]

    def finite_support(n):
        return Fraction(n + 1) if 2 <= n <= 8 else Fraction(0)

    def geometric(n):
        return Fraction(3, 4) ** n

    cutoffs = (30, 200, 900)
    for x in [Fraction(10), Fraction(10) ** 6, Fraction(10) ** 40]:
        got = partials(finite_support, x, cutoffs)
        assert got[0] == got[1] == got[2] > 0, (x, got)
    # the identical sweep on an infinite support whose radius is 4/3, at an x
    # beyond it: there the partial sums grow without bound, which is what the
    # finite-support ones have to be shown NOT to do
    got = partials(geometric, Fraction(3, 2), cutoffs)
    assert got[0] < got[1] < got[2] and got[2] > 10 ** 40, got
    # R > 0 on infinite support, through f_n <= f_a (f_{a+1}/f_a)^{n-a}.  Every
    # family here is strictly log-concave, so the bound is a real inequality; the
    # geometric case, where it holds with equality, is asserted separately as the
    # extremal one, since a sweep made only of those tests nothing.
    strict = {
        "1/n!": lambda n: Fraction(1, int(sp.factorial(n))),
        "2^{-n^2}": lambda n: Fraction(1, 2) ** (n * n),
        "1/(n!)^2": lambda n: Fraction(1, int(sp.factorial(n)) ** 2),
        "(3/5)^n/n!": lambda n: Fraction(3, 5) ** n / int(sp.factorial(n)),
    }
    for name, fn in strict.items():
        for a in (1, 2, 5):
            f = {n: fn(n) for n in range(a, 60)}
            ratio = f[a + 1] / f[a]
            assert all(f[n + 1] / f[n] <= f[n] / f[n - 1]
                       for n in range(a + 1, 59)), (name, a)   # log-concave
            for n in range(a, 60):
                assert f[n] <= f[a] * ratio ** (n - a), (name, a, n)
            assert any(f[n] < f[a] * ratio ** (n - a) for n in range(a + 2, 60)), (name, a)
            assert ratio > 0, (name, a)
    for rho in [Fraction(3, 5), Fraction(9, 10), Fraction(5, 4)]:
        f = {n: rho ** (n - 1) for n in range(1, 60)}
        assert all(f[n] == f[1] * rho ** (n - 1) for n in range(1, 60)), rho
    print("PASS  `cor:ordinary`: R = infinity on finite support (partial sums stop "
          "moving, where a geometric f at x > R does not), and "
          "f_n <= f_a (f_{a+1}/f_a)^{n-a} strictly on 12 log-concave infinite "
          "supports, with equality on the geometric extremals")


def check_gamma_ratio_majorant():
    """`cor:ordinary`: (mu)_{3n}/(3n-1)! = mu prod(1+mu/j) <= M e^M (3n)^M."""
    mu = sp.Symbol("mu")
    for n in range(1, 10):
        assert sp.simplify(poch(mu, 3 * n) / sp.factorial(3 * n - 1)
                           - mu * sp.prod([1 + mu / j for j in range(1, 3 * n)])) == 0, n
    for M in [sp.Rational(1, 4), sp.Rational(1, 2), sp.Integer(1), sp.Integer(3),
              sp.Integer(7), sp.Integer(20)]:
        bound_c = mp.mpf(str(sp.Rational(M))) * mp.e ** mp.mpf(str(sp.Rational(M)))
        for n in range(1, 80):
            grid = [sp.Integer(0), M / sp.Integer(4), M / sp.Integer(2),
                    M * sp.Rational(9, 10), M]
            worst = max(poch(v, 3 * n) / sp.factorial(3 * n - 1) for v in grid)
            bound = bound_c * mp.mpf(3 * n) ** mp.mpf(str(sp.Rational(M)))
            assert mp.mpf(str(sp.Rational(worst))) <= bound, (M, n, worst, bound)
    print("PASS  `cor:ordinary`: (mu)_{3n}/(3n-1)! = mu prod_{j<3n}(1+mu/j) and is "
          "<= M e^M (3n)^M for 0 <= mu <= M (6 values of M, n = 1..79)")


def check_weierstrass_majorant_summable():
    """`cor:ordinary`: n^M (x/y)^n bounded, so the majorant C f_n y^n is summable."""
    for M in [sp.Rational(1, 2), sp.Integer(1), sp.Integer(5), sp.Integer(20)]:
        Mf = mp.mpf(str(sp.Rational(M)))
        for x, y in [(mp.mpf(1) / 2, mp.mpf(3) / 4), (mp.mpf(9) / 10, mp.mpf(99) / 100),
                     (mp.mpf(1) / 100, mp.mpf(1) / 2)]:
            seq = [mp.mpf(n) ** Mf * (x / y) ** n for n in range(1, 4000)]
            top = max(seq)
            # n^M (x/y)^n rises and then falls, so its peak is at an interior
            # index; "the maximum is finite" would hold of any finite list.
            assert 0 <= seq.index(top) < len(seq) - 1, (M, x, y, seq.index(top))
            # and the tail vanishes, which is what the test consumes
            assert seq[-1] < mp.mpf("1e-20") * max(top, mp.mpf(1)), (M, x, y, seq[-1])
    # the dominated sum itself converges for y < R
    for rho in [Fraction(1, 2), Fraction(1, 3)]:
        R = mp.mpf(str(1 / rho))
        y = R * mp.mpf(9) / 10                  # just inside R = 1/rho
        assert R * mp.mpf(9) / 10 < R < R * mp.mpf(11) / 10
        tot = mp.nsum(lambda n: mp.mpf(str(rho)) ** int(n) * y ** int(n), [1, mp.inf])
        assert tot < mp.inf and tot > 0
    print("PASS  `cor:ordinary`: n^M (x/y)^n is bounded with vanishing tail and "
          "sum f_n y^n converges for y < R -- the Weierstrass majorant is summable")


def main():
    check_b_two_closed_value()
    check_rho_route_to_weight_monotonicity()
    check_rho_nonincreasing_gives_the_step()
    check_interval_support_is_load_bearing_at_this_step()
    check_cor_closed_range()
    check_radius_positive_both_supports()
    check_gamma_ratio_majorant()
    check_weierstrass_majorant_summable()
    print("ALL PASS")


if __name__ == "__main__":
    main()
