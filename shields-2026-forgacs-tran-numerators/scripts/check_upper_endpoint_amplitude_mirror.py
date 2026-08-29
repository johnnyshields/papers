r"""Paper section `sec:dominance` (`eq:W-on-g`, `lem:amplitude-divisor`), at the UPPER arc
endpoint with `r >= 2`.

`check_endpoint_amplitude_convention.py` pins one direction of the `x/0` trap: at a
collision the formalized amplitude evaluates to `0` where the true one blows up.  This is
the mirror, and it is the harder of the two to notice because the wrong value is an
ordinary number rather than a suspicious one.

At `2 <= r` the arc's upper endpoint carries `gamma -> 0`.  The pencil does not vanish
there, so there is no collision and no division by zero; the denominator is healthy.  What
the pointwise evaluation loses is a factor in the NUMERATOR.  `eq:W-on-g` reads

    W(gamma) = B(gamma) * gamma / (r Q(gamma) - gamma Q'(gamma)),

whose explicit `gamma` sends `W -> 0`, while evaluating the formalized quotient at the
endpoint point itself gives `-B(0)/Q'(0)`, finite and nonzero.  The two disagree because
the spectral parameter diverges as `theta -> pi/r`, so the true endpoint value is the limit
of an `oo * 0` that cancels, and a pointwise evaluation is not that limit.

Checked at

    Q(t) = (1-t)(2-t)(4-t) = 8 - 14 t + 7 t^2 - t^3,   r = 2,   B(t) = 3 t^2 + 1.

Three claims, and the third is the one that decides what a repair may sit on:

1. the paper's `W` vanishes at the endpoint, to first order, with `W(g)/g -> B(0)/(r Q(0))`;
2. the formalized endpoint value is `-B(0)/Q'(0) = 1/14`, finite and nonzero;
3. `(Q + z t^r).coeff 1 = Q.coeff 1` for every `z` once `r >= 2`, so the endpoint value does
   not see the spectral parameter at all -- no choice of endpoint `z` can reconcile them.

Every claim is an `assert`; mpmath in the limit sweep, sympy for the coefficients.
"""

import mpmath as mp
import sympy as sp

mp.mp.dps = 40

t, z = sp.symbols("t z")

Qs = sp.expand((1 - t) * (2 - t) * (4 - t))
Bs = 3 * t**2 + 1
r = 2

assert Qs == sp.expand(8 - 14 * t + 7 * t**2 - t**3), Qs
assert sp.Poly(Qs, t).coeff_monomial(t) == -14
assert Qs.subs(t, 0) == 8
assert Bs.subs(t, 0) == 1

# ---- (1) the paper's amplitude vanishes at the endpoint, simply -------------------------
Qp = sp.diff(Qs, t)
W_paper = sp.simplify(Bs * t / (r * Qs - t * Qp))

assert sp.simplify(W_paper.subs(t, 0)) == 0, "eq:W-on-g must vanish at gamma = 0"

slope_exact = sp.nsimplify(Bs.subs(t, 0) / (r * Qs.subs(t, 0)))
assert slope_exact == sp.Rational(1, 16), slope_exact

Wf = sp.lambdify(t, W_paper, "mpmath")
prev = None
for k in range(1, 10):
    g = mp.mpf(10) ** (-k)
    val = Wf(g)
    assert abs(val) < g / 10, (k, val)
    ratio = val / g
    err = abs(ratio - mp.mpf(1) / 16)
    assert err < mp.mpf(10) ** (-k + 1), (k, ratio, err)
    if prev is not None:
        assert err < prev, (k, err, prev)
    prev = err

# ---- (2) the formalized endpoint value is finite and nonzero ----------------------------
coeff1 = sp.Poly(Qs, t).coeff_monomial(t)
lean_value = sp.nsimplify(-Bs.subs(t, 0) / coeff1)
assert lean_value == sp.Rational(1, 14), lean_value
assert lean_value != 0

# ---- (3) that value does not depend on the spectral parameter ---------------------------
# `ftDen Q r z = Q + C z * X^r`, and `X^r` reaches degree 1 only at `r = 1`.
for zv in [0, 1, -3, sp.Rational(7, 5), 10**6]:
    den = sp.expand(Qs + zv * t**r)
    assert sp.Poly(den, t).coeff_monomial(t) == coeff1, (zv,)

# and the same fails at `r = 1`, which is why the `r = 1` witnesses never see this
den1 = sp.expand(Qs + z * t**1)
assert sp.Poly(den1, t).coeff_monomial(t) == coeff1 + z

# ---- the two are genuinely different objects, not two writings of one -------------------
assert sp.simplify(W_paper.subs(t, 0) - lean_value) == -sp.Rational(1, 14)

print("check_upper_endpoint_amplitude_mirror: OK")
