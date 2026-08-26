r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude).

Targets `eq:principal-simple`, the assertion that `g'(\gamma(\theta)) \ne 0` on the viewing
arc, and the `eq:Dprime-identity` form of the same statement.

The claim under test is stronger and simpler than the arc-restricted one the paper states:
under `eq:Q-hypotheses` -- `Q` with only positive real zeros -- EVERY critical point of
`g(t) = -Q(t)/t^r` is REAL.  Since the principal point `t_+(\theta) = \tau e^{i\theta}` is
nonreal throughout the open arc `0 < \theta < \pi/r`, `eq:principal-simple` follows with no
property of the branch used at all beyond its nonreality.

The route is a partial-fraction sign count.  With `Q = Q(0)\prod_j (1 - t/x_j)`,

    Q'(t)/Q(t) = -\sum_j 1/(x_j - t),

so `g'(t) = 0` iff `t Q'(t) = r Q(t)` iff `\sum_j x_j/(t - x_j) = r - n`.  Taking imaginary
parts, each term contributes `-x_j (\Im t)/|t - x_j|^2`, and `x_j > 0`, so the whole sum has
the strict sign of `-\Im t`.  A nonreal `t` therefore cannot solve a real equation.

Two instruments, and the split is deliberate.  The realness of the critical points is settled
EXACTLY, over `fractions.Fraction`, by a squarefree deflation followed by a Sturm count: a
polynomial has all roots real exactly when its squarefree part has as many distinct real roots
as its degree, and Sturm's theorem decides that with no tolerance anywhere.  Everything else --
the sign count, the load-bearing sweep, the values on the arc -- is mpmath at 60 digits.

A ROOTFINDER IS THE WRONG INSTRUMENT FOR THE FIRST PART, and quietly so.  `polyroots` at 60
digits reports the critical points of `Q = (1-t)^4(1-t/7)`, `r = 3` with `|Im| = 4.8e-21` at
the triple root `t = 1` -- the `\varepsilon^{1/3}` conditioning of a root of multiplicity 3,
not a nonreal critical point.  Any tolerance loose enough to pass it is loose enough to accept
a genuinely nonreal root of a well-separated pencil, so the test would have been vacuous in
exactly the multiplicity regime `lem:amplitude-divisor` cares about.  Hence the exact route.
"""

from fractions import Fraction

from mpmath import mp, mpf, mpc, polyroots, fabs, im, exp, pi

mp.dps = 60

TOL = mpf(10) ** (-40)


def q_coeffs(xs):
    r"""Coefficients of `\prod_j (1 - t/x_j)`, highest degree first, from the zeros `xs`."""
    coeffs = [mpf(1)]  # constant term only, ascending
    for x in xs:
        nxt = [mpf(0)] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            nxt[i] += c
            nxt[i + 1] += -c / x
        coeffs = nxt
    return list(reversed(coeffs))


def poly_eval(coeffs, t):
    """Horner on a highest-degree-first coefficient list."""
    acc = mpc(0)
    for c in coeffs:
        acc = acc * t + c
    return acc


def deriv_coeffs(coeffs):
    n = len(coeffs) - 1
    return [c * (n - i) for i, c in enumerate(coeffs[:-1])] if n > 0 else [mpf(0)]


def critical_poly(coeffs, r):
    r"""Coefficients of `t Q'(t) - r Q(t)`, highest degree first."""
    d = deriv_coeffs(coeffs)
    shifted = d + [mpf(0)]            # multiply by t
    scaled = [-mpf(r) * c for c in coeffs]
    width = max(len(shifted), len(scaled))
    shifted = [mpf(0)] * (width - len(shifted)) + shifted
    scaled = [mpf(0)] * (width - len(scaled)) + scaled
    return [a + b for a, b in zip(shifted, scaled)]


# --------------------------------------------------------------------------
# Exact rational polynomial arithmetic, for the realness test.
# --------------------------------------------------------------------------

def qq_trim(p):
    """Drop leading zeros from an ascending Fraction coefficient list."""
    while len(p) > 1 and p[-1] == 0:
        p = p[:-1]
    return p


def qq_q(xs):
    r"""`\prod_j (1 - t/x_j)` over the rationals, ascending coefficients."""
    p = [Fraction(1)]
    for x in xs:
        x = Fraction(x)
        nxt = [Fraction(0)] * (len(p) + 1)
        for i, c in enumerate(p):
            nxt[i] += c
            nxt[i + 1] += -c / x
        p = nxt
    return qq_trim(p)


def qq_deriv(p):
    return qq_trim([p[i] * i for i in range(1, len(p))]) if len(p) > 1 else [Fraction(0)]


def qq_critical(p, r):
    r"""`t Q'(t) - r Q(t)`, ascending."""
    d = [Fraction(0)] + qq_deriv(p)
    scaled = [-Fraction(r) * c for c in p]
    w = max(len(d), len(scaled))
    d += [Fraction(0)] * (w - len(d))
    scaled += [Fraction(0)] * (w - len(scaled))
    return qq_trim([a + b for a, b in zip(d, scaled)])


def qq_divmod(a, b):
    a = list(a)
    q = [Fraction(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and qq_trim(a) != [Fraction(0)]:
        da, db = len(a) - 1, len(b) - 1
        if da < db:
            break
        coef = a[-1] / b[-1]
        q[da - db] = coef
        for i, c in enumerate(b):
            a[i + da - db] -= coef * c
        a = qq_trim(a)
        if a == [Fraction(0)]:
            break
    return qq_trim(q), qq_trim(a)


def qq_gcd(a, b):
    a, b = qq_trim(list(a)), qq_trim(list(b))
    while b != [Fraction(0)]:
        _, rem = qq_divmod(a, b)
        a, b = b, rem
    lead = a[-1]
    return [c / lead for c in a]


def qq_eval(p, t):
    acc = Fraction(0)
    for c in reversed(p):
        acc = acc * t + c
    return acc


def sturm_real_root_count(p):
    """Number of DISTINCT real roots of a squarefree `p`, by Sturm's theorem.

    Exact: no tolerance, no rootfinder.  The bracket is Cauchy's bound, which is a
    strict outer bound on every root's modulus, so counting on it counts all of them.
    """
    seq = [p, qq_deriv(p)]
    while qq_trim(seq[-1]) != [Fraction(0)]:
        _, rem = qq_divmod(seq[-2], seq[-1])
        if rem == [Fraction(0)]:
            break
        seq.append([-c for c in rem])
    bound = 1 + max(abs(c / p[-1]) for c in p[:-1]) if len(p) > 1 else Fraction(1)

    def sign_changes(t):
        signs = []
        for q in seq:
            v = qq_eval(q, t)
            if v != 0:
                signs.append(1 if v > 0 else -1)
        return sum(1 for i in range(1, len(signs)) if signs[i] != signs[i - 1])

    return sign_changes(-bound) - sign_changes(bound)


# --------------------------------------------------------------------------
# 1. Every critical point of g is real, exactly, over a spread of pencils.
# --------------------------------------------------------------------------

PENCILS = [
    ([1], 1),
    ([1, 2], 1),
    ([1, 2], 2),
    ([1, 1, 1], 1),                          # x_1 of multiplicity 3
    ([1, 1, 4], 3),                          # rho = 2
    ([1, 2, 3, 4], 2),
    ([1, 2, 3, 4, 5], 5),
    ([1, 1, 1, 1, 7], 3),                    # rho = 4, the triple critical root
    (['1/1000', 1, 1000], 2),                # six decades of spread
    ([1, '10000001/10000000', 3], 1),        # near-collision
    ([2, 2, 2, 2, 2, 2], 4),
    (['1/2', '1/2', 3, 9, 27], 6),
]

total_deg = 0
for xs, r in PENCILS:
    q = qq_q(xs)
    cp = qq_critical(q, r)
    if len(cp) <= 1:
        continue
    sqfree, rem = qq_divmod(cp, qq_gcd(cp, qq_deriv(cp)))
    assert rem == [Fraction(0)], f"deflation left a remainder: xs={xs} r={r}"
    deg = len(sqfree) - 1
    n_real = sturm_real_root_count(sqfree)
    total_deg += deg
    assert n_real == deg, (
        f"NONREAL critical point: xs={xs} r={r} -- squarefree part has degree {deg} "
        f"but only {n_real} distinct real roots")

print(f"PASS  every critical point real, exactly (Sturm over Fraction), "
      f"{total_deg} distinct critical points across {len(PENCILS)} pencils")

# mpmath re-enters here; the pencils are reused as floats for the numeric parts.
PENCILS = [([mpf(Fraction(x).numerator) / mpf(Fraction(x).denominator) for x in xs], r)
           for xs, r in PENCILS]


# --------------------------------------------------------------------------
# 2. The sign count itself: for nonreal t, Im sum_j x_j/(t - x_j) has the
#    strict sign of -Im t.  This is the whole proof, tested directly.
# --------------------------------------------------------------------------

def resid_sum(xs, t):
    return sum(x / (t - x) for x in xs)


worst_ratio = mpf('inf')
probes = 0
for xs, r in PENCILS:
    for k in range(1, 25):
        # sweep the upper half plane, including points very close to the real axis
        theta = pi * mpf(k) / mpf(26)
        for rho in (mpf('0.001'), mpf('0.5'), mpf(1), mpf(3), mpf(1000)):
            t = rho * exp(mpc(0, 1) * theta)
            s = resid_sum(xs, t)
            probes += 1
            # strictly negative imaginary part in the upper half plane
            assert im(s) < 0, f"sign count failed: xs={xs} t={t} Im={im(s)}"
            # and the identity that makes it a proof: Im s = -Im(t) * sum x_j/|t-x_j|^2
            predicted = -im(t) * sum(x / fabs(t - x) ** 2 for x in xs)
            assert fabs(im(s) - predicted) < TOL * max(mpf(1), fabs(predicted)), \
                f"partial-fraction identity failed: xs={xs} t={t}"
            # separation from the real value r - n it would have to equal
            gap = fabs(im(s))
            worst_ratio = min(worst_ratio, gap)

print(f"PASS  sign count strict at {probes} probes in the upper half plane; "
      f"smallest |Im| gap = {mp.nstr(worst_ratio, 8)}")


# --------------------------------------------------------------------------
# 3. The hypothesis is load-bearing: drop positivity of the zeros and the
#    conclusion fails.  A pencil with a nonreal or negative zero acquires
#    nonreal critical points.
# --------------------------------------------------------------------------

BAD = [
    ([mpf(1), mpf(-2), mpf(3)], 1),        # a negative zero
    ([mpf(1), mpf(-1), mpf(2), mpf(-3)], 2),
]

found_nonreal = 0
for xs, r in BAD:
    coeffs = q_coeffs(xs)
    cpoly = critical_poly(coeffs, r)
    while len(cpoly) > 1 and fabs(cpoly[0]) < TOL:
        cpoly = cpoly[1:]
    roots = polyroots(cpoly, maxsteps=200, extraprec=400)
    for t in roots:
        if fabs(im(t)) > mpf(10) ** (-20):
            found_nonreal += 1

assert found_nonreal > 0, \
    "positivity of the zeros is not load-bearing -- no nonreal critical point found " \
    "with a negative zero present, so the sweep does not demonstrate the constraint"

print(f"PASS  positivity is load-bearing: {found_nonreal} nonreal critical points "
      f"appear once a zero is allowed negative")


# --------------------------------------------------------------------------
# 4. The consequence on the arc: the principal point is nonreal on (0, pi/r),
#    so d_t D is bounded away from zero there.
# --------------------------------------------------------------------------

def dt_D_on_curve(coeffs, r, t):
    r"""`\partial_t D(t, g(t)) = Q'(t) - r Q(t)/t`, the `eq:Dprime-identity` form."""
    return poly_eval(deriv_coeffs(coeffs), t) - mpf(r) * poly_eval(coeffs, t) / t


worst_dt = mpf('inf')
arc_probes = 0
for xs, r in PENCILS:
    coeffs = q_coeffs(xs)
    for k in range(1, 40):
        theta = (pi / mpf(r)) * mpf(k) / mpf(40)
        for tau in (mpf('0.01'), mpf('0.7'), mpf(1), mpf(5)):
            t = tau * exp(mpc(0, 1) * theta)
            v = fabs(dt_D_on_curve(coeffs, r, t))
            arc_probes += 1
            assert v > TOL, \
                f"d_t D vanished off the real axis: xs={xs} r={r} theta={theta} tau={tau}"
            worst_dt = min(worst_dt, v)

print(f"PASS  d_t D nonvanishing at {arc_probes} nonreal points; "
      f"smallest |d_t D| = {mp.nstr(worst_dt, 8)}")

print("ALL PASS  check_critical_points_real.py")
