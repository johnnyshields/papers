#!/usr/bin/env python3
r"""Targeted probe, app:boundary-proof, sec:phase and sec:scaling: the three closed
forms the manuscript displays without deriving them in full.

Each is checked symbolically against the quantity the paper defines it from, so
the test fails if either side is edited independently:

  * eq:Fm-boundary itself, the closed form of F_m = MD(N_0-hat, N_m-hat) that the
    whole boundary branch is reduced to, rebuilt from eq:Nhat-m and the alpha,
    beta, c formulas rather than assumed (the certificates that consume it are
    check_boundary_polynomial_certificate.py's);
  * E Phi_1 and E Phi_2, rebuilt from eq:Phi1, eq:Phi2 and the central moments
    eq:X2-asymptotic, eq:X4-asymptotic -- and then checked to reassemble the
    second coefficient of eq:MD-expectation-two-term, which the paper states
    separately.  That cross-check is the point: the two new displays and the
    already-published two-term law must agree;
  * the epsilon-expansion of D^(1-eps,1) used for the transition scale, rebuilt
    from eq:D-large-z-refined, together with the rescaled limit -2 + c(a)/s
    whose simple zero at s = c(a)/2 is what the intermediate value theorem is
    applied to.

Exact symbolic arithmetic throughout; g = psi_1(a) is carried as a symbol, so
no numerical tolerance enters.
"""
import sympy as sp

a, m, g, n, z, eps, s = sp.symbols('a m g n z varepsilon s', positive=True)
c_a = 4/g - 4*a + sp.Rational(7, 2)          # c(a), eq:c-critical
fails = []


def check(tag, expr_zero, detail=""):
    ok = sp.simplify(sp.expand(expr_zero)) == 0
    print(f"  {'OK  ' if ok else 'FAIL'}  {tag}" + (f"\n          {detail}" if detail else ""))
    if not ok:
        fails.append(tag)


print("eq:Fm-boundary -> the closed form of F_m = MD(N_0-hat, N_m-hat)")
c_m = lambda mm: mm*(mm-1)/(2*(2*a+2*mm-3))        # eq:cm-kappa-general at kappa=1, m>=2
s_star = a*(2*a-1)/(2*a**2*g-1)                        # eq:tau-star-s-star
# N_m-hat of eq:Nhat-m, with alpha_m carried symbolically and eliminated by
# alpha_m - alpha_1 = -sum_{r=1}^{m-1}(a+r)^-2 and alpha_1 = g - 1/a^2.
Sig = sp.Symbol('Sigma', nonnegative=True)             # the trigamma tail sum
al_m = g - 1/a**2 - Sig
mm = sp.Symbol('mm', positive=True)
F_built = g*(s_star + c_m(mm)) + s_star*al_m - 2*(2*a+mm-2)/(2*(a+mm-1))
F_printed = (g*c_m(mm) - s_star*Sig + (a-1)*(mm-1)/(a*(a+mm-1)))
check("F_m = g c_m - s_* sum_{r<m}(a+r)^-2 + (a-1)(m-1)/(a(a+m-1))",
      sp.simplify(sp.together(F_built - F_printed)),
      "eq:Nhat-m and the alpha/beta/c formulas rebuild the printed display exactly")

print("\neq:Phi1, eq:Phi2 -> the two expectations, and eq:MD-expectation-two-term")
EX2 = sp.Rational(1, 8) + (2*a-1)/(8*n)                # eq:X2-asymptotic
EX4 = sp.Rational(3, 64)                               # eq:X4-asymptotic
EPhi1 = sp.expand(4 + g*(3-4*a) + 4*g*EX2)             # eq:Phi1
EPhi2 = sp.expand(sp.Rational(1, 3)*(48*g*EX4 + (60-96*a)*g*sp.Rational(1, 8)
                                     + 48*sp.Rational(1, 8)
                                     + 24*a**2*g - 36*a*g - 24*a + 13*g + 12))
check("E Phi_1 = g c(a) + g(2a-1)/(2n) + O(n^-2)",
      EPhi1 - (g*c_a + g*(2*a-1)/(2*n)))
check("E Phi_2 = (96a^2 g - 192 a g - 96a + 91g + 72)/12 + O(n^-1)",
      EPhi2 - sp.Rational(1, 12)*(96*a**2*g - 192*a*g - 96*a + 91*g + 72))
check("they reassemble eq:MD-expectation-two-term's 1/n^2 coefficient",
      (g*(2*a-1)/2 + EPhi2)
      - sp.Rational(1, 12)*(96*a**2*g - 180*a*g - 96*a + 85*g + 72),
      "the new displays must agree with the two-term law already stated")

print("\neq:D-large-z-refined -> the transition scale")
D = 2*((1-eps)-1) + (4*1/g - 2*((1-eps)+1)*(a-1) - sp.Rational(1, 2))/z
check("equals -2eps + (c(a) + 2eps(a-1))/z",
      D - (-2*eps + (c_a + 2*eps*(a-1))/z))
check("at eps = 0 the 1/z coefficient is c(a)", D.subs(eps, 0)*z - c_a)
resc = sp.simplify(sp.expand(sp.limit(sp.expand((-2*eps + (c_a + 2*eps*(a-1))/(s/eps))/eps), eps, 0)))
check("eps^-1 D(s/eps) -> -2 + c(a)/s", resc - (-2 + c_a/s))
check("that limit has its zero at s = c(a)/2", (resc).subs(s, c_a/2))
eta = sp.symbols('eta', positive=True)
check("sign at s_- = (c/2)(1-eta) is +2eta/(1-eta)",
      (-2 + c_a/(c_a/2*(1-eta))) - 2*eta/(1-eta))
check("sign at s_+ = (c/2)(1+eta) is -2eta/(1+eta)",
      (-2 + c_a/(c_a/2*(1+eta))) + 2*eta/(1+eta),
      "opposite signs, so the IVT bracket s_- < eps z_eps < s_+ is legitimate")
# The bracket is only legitimate if the O_a(eps) remainder is eventually smaller
# than the sign margin it has to preserve.  The tighter of the two margins above is
# the one at s_+, so that is what the remainder is compared against -- a comparison,
# not merely the observation that sqrt(eps) -> 0.  It separates the choices:
# eta = eps leaves the ratio at C/2, and eta = eps^2 sends it to infinity.
Cst = sp.Symbol('C', positive=True)                    # the O_a(eps) constant
margin = 2*sp.sqrt(eps)/(1 + sp.sqrt(eps))             # the s_+ margin at eta = sqrt(eps)
check("eta = sqrt(eps): the O_a(eps) remainder is o(margin), so both signs survive",
      sp.limit(Cst*eps/margin, eps, 0))

print()
if fails:
    raise SystemExit("FAILED: " + "; ".join(fails))
print("ALL PASS: check_scaling_expansions -- the displayed closed forms rebuild "
      "from the quantities they are derived from")
