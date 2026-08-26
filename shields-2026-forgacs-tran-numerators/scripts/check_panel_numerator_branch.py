"""Panel B: the Laurent restriction, and the index shift it licenses.

`cor:panel-B-attractor` has a bivariate numerator N(t,z) = 1 + z + z^2 + t(2 - z),
while `prop:isolated-dominant-cancellation` takes a univariate B in R[t].  The
bridge is `lem:laurent-reduction`: restricting N to the denominator fiber
g(t) = -Q(t)/t^r and clearing the pole gives that univariate B,

    N(t, g(t)) = t^{-2} B(t),      64 B(t) = panelB64(t),

so the Laurent exponent is lambda_N = -2 and the coefficient sequences are
related by P_m = F_{m+2}.

Both halves are checked here: the restriction identity in exact rational
arithmetic, and the shift term by term -- including where it starts, since the
paper states it only for sufficiently large m and the threshold is m >= 2.
"""
import sympy as sp

t, z = sp.symbols("t z")

Q = sp.expand((1 - t) * (1 - t / 2) * (1 - t / 4))
N = 1 + z + z**2 + t * (2 - z)
panelB64 = t**6 - 22 * t**5 + 141 * t**4 - 252 * t**3 + 548 * t**2 - 288 * t + 64
B = sp.expand(panelB64 / 64)

# --- (A) the Laurent restriction: N(t, g(t)) = t^-2 B(t) ---------------------
g = -Q / t
resid = sp.simplify(sp.expand(N.subs(z, g)) - B / t**2)
print("N(t,g(t)) - t^-2 B(t) =", resid)
assert resid == 0, f"restriction identity failed: {resid}"

# equivalently, panelB64 = 64 t^2 N(t, g(t)) -- the form the Lean tree carries
resid2 = sp.simplify(sp.expand(panelB64 - 64 * t**2 * N.subs(z, g)))
assert resid2 == 0, f"sextic form failed: {resid2}"
print("panelB64 = 64 t^2 N(t, g(t)):  verified")

# --- (B) the amplitude zeros are the sextic's roots inside |t| < 1/2 ---------
roots = sp.nroots(panelB64)
inside = [w for w in roots if abs(complex(w)) < 0.5]
assert len(inside) == 2, f"expected a conjugate pair, got {inside}"
assert abs(complex(inside[0]).conjugate() - complex(inside[1])) < 1e-9
print("roots of panelB64 with |t| < 1/2 (the amplitude zeros):", inside)

# --- (C) the index shift P_m = F_{m+2}, and where it begins ------------------
P = [sp.Poly(z**2 + z + 1, z),
     sp.Poly(-z**3 + sp.Rational(3, 4) * z**2 - sp.Rational(1, 4) * z
             + sp.Rational(15, 4), z)]
P.append(sp.Poly(sp.expand(-(z - sp.Rational(7, 4)) * P[1].as_expr()
                           - sp.Rational(7, 8) * P[0].as_expr()), z))
for m in range(3, 12):
    P.append(sp.Poly(sp.expand(-(z - sp.Rational(7, 4)) * P[m - 1].as_expr()
                               - sp.Rational(7, 8) * P[m - 2].as_expr()
                               + sp.Rational(1, 8) * P[m - 3].as_expr()), z))

ser = sp.series(B / (Q + z * t), t, 0, 15).removeO()
F = [sp.Poly(sp.expand(sp.simplify(ser.coeff(t, M))), z) for M in range(15)]

agree = [m for m in range(10) if sp.simplify(P[m].as_expr() - F[m + 2].as_expr()) == 0]
print("P_m = F_{m+2} holds for m in", agree)
assert agree == list(range(2, 10)), f"unexpected agreement set: {agree}"
# the paper says "sufficiently large m"; the threshold is exactly 2
for m in (0, 1):
    assert sp.simplify(P[m].as_expr() - F[m + 2].as_expr()) != 0, \
        f"expected disagreement at m = {m}"
print("and fails at m = 0, 1 -- so 'sufficiently large' means m >= 2")

# --- (D) the degree claim of the corollary ----------------------------------
for m in range(0, 10):
    assert P[m].degree() == m + 2, f"deg P_{m} = {P[m].degree()}, expected {m+2}"
    assert P[m].coeff_monomial(z**(m + 2)) == (-1)**m, \
        f"[z^{m+2}] P_{m} = {P[m].coeff_monomial(z**(m+2))}, expected {(-1)**m}"
print("deg P_m = m + 2 and [z^{m+2}]P_m = (-1)^m:  verified for m <= 9")

print()
print('ALL PASS: check_panel_numerator_branch')
