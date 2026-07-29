#!/usr/bin/env python3
"""Paper section 8 (Continuation beyond the positive-series domain),
Lemma 8.1 (lem:continuation), first assertion: the series (2.1) and all of its
fixed-order parameter and Euler derivatives converge locally uniformly on C^2,
so Z and those derivatives are entire in (a, lambda).

Section 2 leans on this twice -- once after (2.1), and once to justify that the
Bessel-side order derivatives of log I_nu exist at all -- so it is checked here
rather than left to the proof text.  The checks are

  (1) Z is finite at a = 0, -1, -2, -3, where the quotient 0F1(;a;lambda)/Gamma(a)
      that (2.1) also names is not defined termwise: the summands with a + k a
      nonpositive integer vanish because 1/Gamma does;

  (2) holomorphy in a by Cauchy's theorem: the contour integral of Z around a
      circle enclosing a = 0, -1, -2 vanishes.  Positive control: the same
      contour integral of 0F1(;a;lambda) itself does NOT vanish, so the test has
      the power to detect a pole where one exists;

  (3) holomorphy in lambda by the same route, on a circle about lambda = 0;

  (4) termwise differentiation is legitimate -- i.e. the differentiated series
      converge locally uniformly to the derivatives of the sum -- by comparing
      d^j/da^j (Theta_lambda)^l Z computed two independent ways: the Cauchy
      integral formula over a contour, and the termwise-differentiated series;

  (5) locally uniform convergence directly: on the compact
      |a| <= R, |lambda| <= S the series tail past N is bounded by a quantity
      that decays superexponentially in N *uniformly over the compact*, checked
      on a grid including points adjacent to the 1/Gamma zeros.

Every displayed quantity is asserted, not printed only.
"""

from mpmath import mp, mpf, mpc, gamma, rgamma, hyp0f1, quad, exp, pi, fabs

mp.dps = 40

R_A = mpf(3)             # compact in a: |a| <= R_A  (encloses a = 0, -1, -2)
S_LAM = mpf(2)           # compact in lambda: |lambda| <= S_LAM
NTERMS = 220             # series truncation, far past the tail bound below
TOL = mpf(10) ** (-25)


def Z(a, lam, nterms=NTERMS):
    """Z(a, lambda) = sum_k lambda^k / (k! Gamma(a+k)), via entire 1/Gamma."""
    total = mpc(0)
    term = mpc(1)                      # lambda^k / k!
    for k in range(nterms):
        total += term * rgamma(a + k)
        term = term * lam / (k + 1)
    return total


def Z_deriv(a, lam, j=0, l=0, nterms=NTERMS):
    """Termwise d^j/da^j (lambda d/dlambda)^l Z, i.e. the differentiated series.

    (lambda d/dlambda)^l acts on lambda^k as k^l, and d^j/da^j hits 1/Gamma(a+k).
    """
    total = mpc(0)
    term = mpc(1)
    for k in range(nterms):
        dg = mp.diff(lambda w: rgamma(w + k), a, j) if j else rgamma(a + k)
        total += term * (mpf(k) ** l if l or k else mpf(1)) * dg
        term = term * lam / (k + 1)
    return total


def da(a, lam, j):
    """d^j/da^j Z(a, lambda) by numerical differentiation in a."""
    return mp.diff(lambda w: Z(w, lam), a, j) if j else Z(a, lam)


def euler(F, x, l):
    """(x d/dx)^l F, applied numerically l times."""
    if l == 0:
        return F(x)
    inner = lambda y: euler(F, y, l - 1)
    return x * mp.diff(inner, x)


def contour(f, centre, radius, order=0):
    """(order! / 2 pi i) * oint f(w) / (w - centre)^{order+1} dw over |w-c|=radius.

    order = 0 with f = Z reproduces Z(centre) when Z is holomorphic inside;
    the bare integral (see cauchy_theorem_integral) vanishes for entire f.
    """
    def integrand(th):
        w = centre + radius * exp(mpc(0, 1) * th)
        dw = mpc(0, 1) * radius * exp(mpc(0, 1) * th)
        return f(w) / (w - centre) ** (order + 1) * dw
    val = quad(integrand, [0, 2 * pi])
    return mp.factorial(order) * val / (2 * pi * mpc(0, 1))


def cauchy_theorem_integral(f, centre, radius):
    """oint f(w) dw over |w - centre| = radius; zero for f holomorphic inside."""
    def integrand(th):
        w = centre + radius * exp(mpc(0, 1) * th)
        dw = mpc(0, 1) * radius * exp(mpc(0, 1) * th)
        return f(w) * dw
    return quad(integrand, [0, 2 * pi])


# ---------------------------------------------------------------------------
# (1) Z is finite at the nonpositive integers, where 0F1/Gamma(a) is not
# ---------------------------------------------------------------------------
LAM0 = mpf("0.75")
for a_int in (0, -1, -2, -3):
    val = Z(mpf(a_int), LAM0)
    assert fabs(val) < mpf(10) ** 6 and val == val, \
        "Z must be finite at a = %d, got %s" % (a_int, val)
    # the k < -a_int summands vanish: 1/Gamma kills them
    head = sum(LAM0 ** k / mp.factorial(k) * rgamma(mpf(a_int) + k)
               for k in range(-a_int + 1))
    tail_start = LAM0 ** (-a_int) / mp.factorial(-a_int) * rgamma(mpf(0))
    assert fabs(tail_start) < TOL, "1/Gamma(0) must vanish"
    assert fabs(head) < mpf(10) ** 6, "head of the series at a = %d" % a_int
# and Z agrees with 0F1(;a;lambda)/Gamma(a) away from those points
for a_ok in ("0.6", "2.3", "-0.4", "-1.7"):
    a_v = mpf(a_ok)
    assert fabs(Z(a_v, LAM0) - hyp0f1(a_v, LAM0) / gamma(a_v)) < TOL, \
        "Z vs 0F1/Gamma at a = %s" % a_ok
print('PASS: Z is finite at a = 0,-1,-2,-3, where the quotient 0F1/Gamma(a) is'
      ' not, and agrees with that quotient off the pole set')

# ---------------------------------------------------------------------------
# (2) holomorphy in a, with a positive control that the test can fail
# ---------------------------------------------------------------------------
CIRC_A = mpf("2.5")        # |a| = 2.5 encloses a = 0, -1, -2
loop_Z = cauchy_theorem_integral(lambda w: Z(w, LAM0), mpc(0), CIRC_A)
assert fabs(loop_Z) < mpf(10) ** (-18), \
    "oint Z da must vanish (Z entire in a); got %s" % loop_Z

# positive control: 0F1(;a;lambda) has poles at a = 0, -1, -2, so its loop
# integral must NOT vanish.  This is the mutation test for check (2): it shows
# a nonzero verdict is reachable, so the assertion above is not vacuous.
loop_0f1 = cauchy_theorem_integral(lambda w: hyp0f1(w, LAM0), mpc(0), CIRC_A)
assert fabs(loop_0f1) > mpf("1e-3"), \
    "control: oint 0F1 da must be nonzero, got %s" % loop_0f1
print('PASS: oint Z da = %.3e over |a| = 5/2 (Z entire in a); the same contour'
      ' on 0F1 itself gives %.3e, so the test detects a pole when there is one'
      % (float(fabs(loop_Z)), float(fabs(loop_0f1))))

# ---------------------------------------------------------------------------
# (3) holomorphy in lambda
# ---------------------------------------------------------------------------
A_FIX = mpf("0.6")
loop_lam = cauchy_theorem_integral(lambda w: Z(A_FIX, w), mpc(0), S_LAM)
assert fabs(loop_lam) < mpf(10) ** (-18), \
    "oint Z dlambda must vanish (Z entire in lambda); got %s" % loop_lam
# also at a inside the 1/Gamma zero set, where Z is still entire in lambda
loop_lam0 = cauchy_theorem_integral(lambda w: Z(mpf(-1), w), mpc(0), S_LAM)
assert fabs(loop_lam0) < mpf(10) ** (-18), \
    "oint Z dlambda at a = -1 must vanish; got %s" % loop_lam0
print('PASS: oint Z dlambda vanishes (%.3e at a = 3/5, %.3e at a = -1), so Z is'
      ' entire in lambda including on the 1/Gamma zero set'
      % (float(fabs(loop_lam)), float(fabs(loop_lam0))))

# ---------------------------------------------------------------------------
# (4) termwise differentiation == Cauchy-integral derivative, for the
#     fixed-order parameter and Euler derivatives the paper uses
# ---------------------------------------------------------------------------
A_PTS = [mpf("0.6"), mpf("2.3"), mpf("-0.4"), mpf("-1.7")]
R_SMALL = mpf("0.25")      # small circle, avoids the neighbouring 1/Gamma zeros
for a_v in A_PTS:
    for j in (1, 2):
        cauchy_j = contour(lambda w: Z(w, LAM0), a_v, R_SMALL, order=j)
        series_j = Z_deriv(a_v, LAM0, j=j, l=0)
        assert fabs(cauchy_j - series_j) < mpf(10) ** (-15), \
            "d^%d/da^%d Z at a=%s: contour %s vs series %s" % (
                j, j, a_v, cauchy_j, series_j)
    # mixed and pure Euler derivatives, against numerical differentiation
    for (j, l) in ((0, 1), (0, 2), (1, 1)):
        series_jl = Z_deriv(a_v, LAM0, j=j, l=l)
        got = euler(lambda x, j=j, a_v=a_v: da(a_v, x, j), LAM0, l)
        assert fabs(got - series_jl) < mpf(10) ** (-12), \
            "(j,l)=(%d,%d) at a=%s: numeric %s vs termwise series %s" % (
                j, l, a_v, got, series_jl)
print('PASS: termwise differentiation is legitimate -- d^j/da^j (Theta_lambda)^l Z'
      ' agrees with the Cauchy-integral and numerical routes for j <= 2, l <= 2')

# ---------------------------------------------------------------------------
# (5) locally uniform convergence on |a| <= R_A, |lambda| <= S_LAM:
#     the tail past N decays superexponentially, uniformly over the compact
# ---------------------------------------------------------------------------
GRID = []
for ar in ("-2.999", "-2.0", "-1.5", "-0.0001", "0.5", "2.999"):
    for ai in ("0", "1.2"):
        a_g = mpc(mpf(ar), mpf(ai))
        if fabs(a_g) <= R_A:
            GRID.append(a_g)
assert len(GRID) >= 8, "grid too small to be a uniformity check"

def tail_sup(N):
    """sup over the grid and |lambda| = S_LAM of |sum_{k>=N} lambda^k/(k! Gamma(a+k))|."""
    worst = mpf(0)
    for a_g in GRID:
        s = mpc(0)
        term = S_LAM ** N / mp.factorial(N)
        for k in range(N, N + 90):
            s += term * fabs(rgamma(a_g + k))
            term = term * S_LAM / (k + 1)
        worst = max(worst, fabs(s))
    return worst

prev = None
for N in (10, 20, 30, 40):
    cur = tail_sup(N)
    assert prev is None or cur < prev / mpf(10) ** 3, \
        "tail sup must fall by >1e3 per 10 terms, uniformly: N=%d %s vs %s" % (
            N, cur, prev)
    prev = cur
assert prev < mpf(10) ** (-30), \
    "tail sup at N=40 must be negligible on the compact, got %s" % prev
# the truncation actually used is well past that
assert NTERMS > 100
print('PASS: the series tail is uniformly small on |a| <= 3, |lambda| <= 2 --'
      ' sup over the grid falls by >1e3 per 10 terms, to %.3e at N = 40'
      % float(prev))

print('ALL PASS: verify_continuation')
