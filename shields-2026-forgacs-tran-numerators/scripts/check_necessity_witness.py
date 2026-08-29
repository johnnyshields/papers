r"""Paper section `sec:introduction` (the numerator non-uniformity, `eq:P-generating-intro`).

The closed-form cross-check is `prop:linear-case` in `subsec:linear-case`.

`thm:main` gives, for each fixed numerator, a constant `C` bounding the zeros of
every `P_m` off `(0,infty)`.  The introduction asserts that no `C` serves every
numerator at once: taking `N(t,z) = R(z)` forces `P_m = R H_m`, so the zeros of
`R` sit in every coefficient polynomial and `deg R` is unbounded.

The Lean tree states that as a negation,
`ForgacsTran.not_exists_uniform_exceptional_bound`, over the admissible pencil
`Q(t) + z t^r`.  Four things it rests on are checked here, none of them assumed
from the closed form the paper writes down in `subsec:linear-case`:

(1)  Solving the convolution system `sum_j d_j P_{m-j} = [m=0] R` with
     `d_j = Q_j + [j=r] z` reproduces the series coefficients of
     `R(z) / (Q(t) + z t^r)` in `t`.  Two independent routes to `P_m`.

(2)  `R` divides every `P_m` exactly (remainder zero in `Q[z]`), and `P_0` is a
     nonzero constant multiple of `R` -- which is what makes the negation
     non-vacuous, since its conclusion is guarded by `P_m != 0`.

(3)  Every `P_m` carries at least `deg R` zeros off `(0,infty)`, counted with
     multiplicity, on BOTH sides of the real/complex passage.  The two counts
     are pinned to each other by an identity rather than an inequality:

         (complex zeros off posRay) - (real zeros off (0,infty))
             = number of non-real zeros, with multiplicity,

     so `card_exceptionalRoots_le_map` is an equality exactly when `P_m` splits
     over the reals, and the gap is measured rather than bounded.

(4)  The refutation itself: for each candidate `C`, the numerator
     `R = prod_{j=1}^{C+1}(z+j)` gives more than `C` exceptional zeros already at
     `m = 0`.

The pencils are labelled by whether they satisfy `eq:Q-hypotheses`.  The
negation needs only `Q(0) != 0` and `r >= 1`, so the panel deliberately carries
inadmissible pencils too -- if the claim ever came to depend on positive
rootedness, those rows would be the ones to fail.

Exact arithmetic throughout (sympy over `Q`, roots as `CRootOf`); the closing
section corroborates one pencil at 50 decimal digits with mpmath.  No float64
anywhere.
"""

import sympy as sp
import mpmath as mp

z, t = sp.symbols("z t")


def neg_root_poly(L):
    """`negRootPoly L` = prod_{j=1}^{L} (z + j), the witness numerator."""
    return sp.prod([z + j for j in range(1, L + 1)]) if L else sp.Integer(1)


def solve_recurrence(Qcoeffs, r, R, M):
    """Solve `sum_{j=0}^m d_j P_{m-j} = [m=0] R` for `P_0, ..., P_M`.

    `d_j = Qcoeffs[j] + [j == r] * z`; the diagonal `d_0 = Q(0)` is a nonzero
    rational, so each step is a division by a unit of `Q[z]`.
    """
    def d(j):
        c = sp.Integer(Qcoeffs[j]) if j < len(Qcoeffs) else sp.Integer(0)
        return c + (z if j == r else sp.Integer(0))

    assert d(0) != 0, "Q(0) = 0: the pencil is not admissible"
    P = []
    for m in range(M + 1):
        rhs = R if m == 0 else sp.Integer(0)
        tail = sum(d(j) * P[m - j] for j in range(1, m + 1))
        P.append(sp.expand(sp.cancel((rhs - tail) / d(0))))
    return P


def series_coeffs(Qcoeffs, r, R, M):
    """`[t^m] R(z) / (Q(t) + z t^r)`, expanded independently of the recurrence."""
    D = sum(sp.Integer(c) * t**j for j, c in enumerate(Qcoeffs)) + z * t**r
    ser = sp.series(R / D, t, 0, M + 1).removeO()
    poly = sp.Poly(sp.expand(ser), t)
    return [sp.expand(sp.cancel(poly.coeff_monomial(t**m))) for m in range(M + 1)]


def zero_counts(P):
    """Exact zero counts of a nonzero `P` in `Q[z]`, all with multiplicity.

    Returns `(deg, n_real, n_pos, real_exc, cplx_exc)` where `real_exc` counts the
    REAL zeros outside `(0,infty)` and `cplx_exc` the COMPLEX zeros outside the
    positive ray -- the two sides of the passage.
    """
    poly = sp.Poly(P, z)
    deg = poly.degree()
    if deg == 0:
        return 0, 0, 0, 0, 0
    real = poly.real_roots()                      # with multiplicity
    pos = sum(1 for x in real if x.is_positive)
    return deg, len(real), pos, len(real) - pos, deg - pos


PENCILS = [
    # (Q coefficients low-to-high, r, label)
    ([1, -1], 1, "Q = 1 - t,       r = 1  (admissible; prop:linear-case)"),
    ([2, -3, 1], 1, "Q = (1-t)(2-t),  r = 1  (admissible)"),
    ([2, -3, 1], 2, "Q = (1-t)(2-t),  r = 2  (admissible)"),
    ([1, 1, 1], 1, "Q = 1 + t + t^2, r = 1  (not admissible: no positive zero)"),
    ([3, 1], 2, "Q = 3 + t,       r = 2  (not admissible: zero at t = -3)"),
]

M = 6
print("Necessity witness over admissible pencils Q(t) + z t^r")
print("(M = %d coefficient polynomials per pencil)" % M)
print()

for Qc, r, label in PENCILS:
    for L in [0, 1, 2, 3]:
        R = sp.expand(neg_root_poly(L))
        P = solve_recurrence(Qc, r, R, M)
        S = series_coeffs(Qc, r, R, M)

        # (1) two routes to the same coefficient sequence
        for m in range(M + 1):
            assert sp.expand(P[m] - S[m]) == 0, (label, L, m, P[m], S[m])

        # (2) R divides every P_m, exactly, and P_0 is nonzero
        assert P[0] != 0
        for m in range(M + 1):
            if P[m] == 0:
                continue
            quo, rem = sp.div(sp.Poly(P[m], z), sp.Poly(R, z))
            assert rem.is_zero, (label, L, m, "R does not divide P_m")

        # (3) the two exceptional counts, and the identity between them
        for m in range(M + 1):
            if P[m] == 0:
                continue
            deg, n_real, n_pos, real_exc, cplx_exc = zero_counts(P[m])
            assert real_exc >= L, (label, L, m, real_exc)
            assert cplx_exc >= L, (label, L, m, cplx_exc)
            assert cplx_exc - real_exc == deg - n_real, (label, L, m)
            assert real_exc <= cplx_exc

print("PASS  (1) the convolution solve and the t-expansion of R/(Q + z t^r)")
print("          agree coefficientwise, %d pencils x 4 numerators x %d indices"
      % (len(PENCILS), M + 1))
print("PASS  (2) R | P_m exactly for every index, and P_0 != 0 -- the guard")
print("          `P m != 0` of the negation is met at m = 0 in every case")
print("PASS  (3) both exceptional counts are at least deg R, and their")
print("          difference is exactly the number of non-real zeros")
print()

# ------------------------------------------------------------------ claim (4)
# The refutation, run as the proof runs it: given C, take L = C+1 and read the
# count at m = 0.
print("The refutation, per candidate constant C  (Q = 1 - t, r = 1, admissible):")
for C in range(6):
    L = C + 1
    R = sp.expand(neg_root_poly(L))
    P = solve_recurrence([1, -1], 1, R, 0)
    assert P[0] != 0
    _, _, _, real_exc, cplx_exc = zero_counts(P[0])
    assert real_exc > C, (C, real_exc)
    assert cplx_exc > C, (C, cplx_exc)
    print("   C = %d  ->  R = negRootPoly(%d),  exceptional zeros of P_0: "
          "real %d, complex %d   (> C)" % (C, L, real_exc, cplx_exc))
print("PASS  (4) no constant survives: every C is exceeded at m = 0")
print()

# ------------------------------------- the passage is strict, and by how much
# `card_exceptionalRoots_le_map` is an inequality, not an equality.  The gap is
# the non-real zeros, so a polynomial with none has equal counts and one with a
# conjugate pair has a gap of two.
for P0, expect_real, expect_cplx in [
    (z**2 + 1, 0, 2),                 # no real zeros, two complex ones off the ray
    (z**2 - 1, 1, 1),                 # zeros -1 and +1
    ((z + 1) * (z**2 + 1), 1, 3),
    (z**2 - 2, 1, 1),                 # irrational zeros, still real
    (z * (z**2 + z + 1), 1, 3),       # z = 0 is off (0,infty) on both sides
]:
    _, _, _, real_exc, cplx_exc = zero_counts(sp.expand(P0))
    assert (real_exc, cplx_exc) == (expect_real, expect_cplx), (P0, real_exc, cplx_exc)
    assert real_exc <= cplx_exc
print("PASS  (5) the passage is strict where the zeros are non-real: z^2+1 has")
print("          0 real exceptional zeros and 2 complex ones, so the Lean")
print("          inequality cannot be strengthened to an equality")
print()

# ------------------------------------------- mpmath corroboration at 50 digits
# One pencil recomputed numerically, independently of sympy's exact root
# isolation: solve the recurrence in mpmath and count the roots of P_3 that do
# not lie on the positive real axis.
mp.mp.dps = 50
Qc, r, L, m_target = [1, 1, 1], 1, 3, 3
R = sp.expand(neg_root_poly(L))
P = solve_recurrence(Qc, r, R, m_target)
coeffs_high_to_low = [mp.mpf(sp.Rational(c).p) / mp.mpf(sp.Rational(c).q)
                      for c in sp.Poly(P[m_target], z).all_coeffs()]
roots = mp.polyroots(coeffs_high_to_low, maxsteps=200, extraprec=400)
tol = mp.mpf(10) ** (-30)
off_ray = sum(1 for w in roots if not (abs(mp.im(w)) < tol and mp.re(w) > tol))
_, _, _, real_exc_exact, cplx_exc_exact = zero_counts(P[m_target])
assert off_ray == cplx_exc_exact, (off_ray, cplx_exc_exact)
assert off_ray >= L
print("PASS  (6) mpmath at 50 dps, Q = 1 + t + t^2, r = 1, L = 3, m = 3:")
print("          %d of %d zeros of P_3 lie off the positive ray, matching the"
      % (off_ray, len(roots)))
print("          exact count, and %d >= deg R = %d" % (off_ray, L))

print()
print("ALL PASS  check_necessity_witness")
