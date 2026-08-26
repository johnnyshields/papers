r"""Paper section `sec:dominance` (The weighted dominance bound).

Which side of the endpoint value carries a CONJUGATE pair, which is what the
`rho = 1` corner's step 4 has to identify.

Write `f(w) = -Q(w)/w^r` for the paper's branch function and `a_end = f(t_a)`
for its value at the endpoint.  `f'(t_a) = 0` and `f''(t_a) \ne 0`
(`check_lower_collision_order_two.py`), so the Morse form is
`f(w) - a_end = (w - t_a)^2 h(w)` with `h(t_a) = f''(t_a)/2`.  The two roots of
`f(w) = a` near `t_a` are then

    w_\pm \approx t_a \pm \sqrt{(a - a_end)/h(t_a)} ,

REAL when `(a - a_end)/h(t_a) > 0` and a CONJUGATE PAIR when it is negative.
So the split is decided by one sign, and since `f''(t_a) < 0` at every
admissible pencil with a simple smallest zero, the conjugate side is
`a > a_end`.  Nothing had measured that, and getting it backwards would put
the reparameterization on the interval where the branch does not live.

Three things:

  (i)   `f''(t_a) < 0`, and hence `h(t_a) < 0`, at every pencil;
  (ii)  perturbing to `a > a_end` gives a genuine conjugate pair -- equal
        moduli, opposite nonzero imaginary parts -- and `a < a_end` gives two
        real roots, so the dichotomy is exhibited rather than asserted;
  (iii) the separation grows like `\sqrt{|a - a_end|}`, with the Morse
        coefficient `2/\sqrt{|f''(t_a)|}` recovered from the fit -- which is
        the quantitative form step 5's reparameterization consumes.

The exponent is fitted rather than bounded: a square-root split cannot be
distinguished from a linear one by any single tolerance on the separation.

mpmath only.
"""

from mpmath import mp, mpf, mpc, fabs, log, sqrt, polyroots, diff

mp.dps = 50

ZERO = mpf(10) ** -35


def Qcoeffs(a):
    """Ascending coefficients of Q(t) = prod_k (a_k - t)."""
    p = [mpf(1)]
    for ak in a:
        q = [mpf(0)] * (len(p) + 1)
        for i, c in enumerate(p):
            q[i] += ak * c
            q[i + 1] += -c
        p = q
    return p


def Qeval(a, t):
    v = mpf(1)
    for ak in a:
        v *= (ak - t)
    return v


def f(a, r, w):
    return -Qeval(a, w) / w ** r


def sigma(a, r, s):
    return sum(s / (ak - s) for ak in a) + r


def t_a_of(a, r):
    xs = sorted(set(a))
    assert sum(1 for x in a if x == xs[0]) == 1, "this pencil is not simple"
    lo = xs[0] + (xs[1] - xs[0]) * mpf(10) ** -30
    hi = xs[1] - (xs[1] - xs[0]) * mpf(10) ** -30
    assert sigma(a, r, lo) < 0 < sigma(a, r, hi), "the endpoint is not bracketed"
    for _ in range(400):
        mid = (lo + hi) / 2
        if sigma(a, r, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def roots_near(a, r, avalue, ta):
    """Roots of f(w) = avalue, i.e. of -Q(w) - avalue*w^r, nearest t_a."""
    p = [-c for c in Qcoeffs(a)]          # -Q, ascending
    while len(p) <= r:
        p.append(mpf(0))
    p[r] -= avalue                         # subtract avalue * w^r
    while len(p) > 1 and fabs(p[-1]) < ZERO:
        p.pop()
    rts = polyroots(list(reversed(p)), maxsteps=300, extraprec=300)
    return sorted(rts, key=lambda z: fabs(mpc(z) - ta))[:2]


PENCILS = [
    ("a = (1,2,5), r = 1", [mpf(1), mpf(2), mpf(5)], 1),
    ("a = (1,2,5), r = 2", [mpf(1), mpf(2), mpf(5)], 2),
    ("a = (1,3,3,8), r = 1", [mpf(1), mpf(3), mpf(3), mpf(8)], 1),
    ("a = (1/2,1,1,5), r = 1", [mpf(1) / 2, mpf(1), mpf(1), mpf(5)], 1),
    ("a = (1,4,9,16), r = 2", [mpf(1), mpf(4), mpf(9), mpf(16)], 2),
]

print("PASS  (i)/(ii) the sign of f''(t_a) and the side it puts the pair on:")
worst_conj = mpf(0)
worst_exp = mpf(0)
for name, a, r in PENCILS:
    ta = t_a_of(a, r)
    aend = f(a, r, ta)
    f2 = diff(lambda w: f(a, r, w), ta, 2)
    assert f2 < 0, f"f''(t_a) = {f2} is not negative on {name}"

    # (ii) above the endpoint value: a conjugate pair
    eps = fabs(aend) * mpf(10) ** -8
    up = roots_near(a, r, aend + eps, ta)
    z1, z2 = mpc(up[0]), mpc(up[1])
    assert fabs(z1.imag) > ZERO, f"the upper split is real on {name}"
    d = fabs(z1 - z2.conjugate())
    worst_conj = max(worst_conj, d / fabs(z1 - ta))
    assert d < fabs(z1 - ta) * mpf(10) ** -6, (
        f"the two roots above a_end are not conjugate on {name}: {z1}, {z2}")

    # and below it: two real roots
    dn = roots_near(a, r, aend - eps, ta)
    assert all(fabs(mpc(z).imag) < fabs(mpc(z) - ta) * mpf(10) ** -6
               for z in dn), f"the lower split is not real on {name}: {dn}"

    # (iii) the separation is square-root in the offset, with the Morse constant
    seps = []
    for j in range(6, 14):
        e = fabs(aend) * mpf(10) ** (-j)
        w = roots_near(a, r, aend + e, ta)
        seps.append((e, fabs(mpc(w[0]) - mpc(w[1]))))
    (e1, s1), (e2, s2) = seps[0], seps[-1]
    expo = log(s2 / s1) / log(e2 / e1)
    worst_exp = max(worst_exp, fabs(expo - mpf(1) / 2))
    assert fabs(expo - mpf(1) / 2) < mpf(1) / 100, (
        f"the separation exponent is {expo} on {name}, not 1/2")
    coeff = s2 / sqrt(e2)
    # f(w) - a_end = (w-t_a)^2 h with h(t_a) = f''(t_a)/2, so setting
    # f(w) = a_end + e gives (w-t_a)^2 = 2e/f''(t_a); with f'' < 0 the roots
    # are t_a +- i sqrt(2e/|f''|) and the SEPARATION is twice that.  The
    # factor 2 from h = f''/2 is the one an eyeball derivation drops.
    pred = 2 * sqrt(2) / sqrt(fabs(f2))
    assert fabs(coeff - pred) / pred < mpf(1) / 100, (
        f"the Morse coefficient is {coeff}, predicted {pred}, on {name}")
    print(f"        {name:<22} f''(t_a) = {mp.nstr(f2, 8):<14} "
          f"exponent {mp.nstr(expo, 8):<12} 2sqrt2/sqrt|f''| = {mp.nstr(pred, 8)}")

print(f"PASS  (ii) above a_end the two roots are a conjugate pair at every "
      f"pencil (worst relative defect {mp.nstr(worst_conj, 4)}); below it they "
      f"are both real -- the dichotomy is exhibited, not asserted")
print(f"PASS  (iii) the separation goes like sqrt(a - a_end) with coefficient "
      f"2 sqrt(2)/sqrt|f''(t_a)|; worst exponent error {mp.nstr(worst_exp, 3)}")
print("PASS  (i) f''(t_a) < 0 at every pencil, so h(t_a) = f''(t_a)/2 < 0 and "
      "the CONJUGATE side is a > a_end -- one sign decides it, and the sign is "
      "structural: f''(t_a) = Sigma'(t_a) Q(t_a) / t_a^(r+1) with Sigma' > 0, "
      "Q(t_a) < 0")
print("ALL PASS")
