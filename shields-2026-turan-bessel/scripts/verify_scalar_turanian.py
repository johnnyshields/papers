#!/usr/bin/env python3
r"""Paper section `sec:scalar` (Classical scalar Bessel directions), sec:scalar:
prop:scalar-H and rem:schur-correction.

With nu > -1, z > 0, kappa real, Theta_z = z d/dz, and

    R_nu(z) = I_{nu+1}(z)/I_nu(z),
    r_nu(z) = z R_nu(z) = Theta_z log I_nu(z) - nu,          eq. (R-r-def)
    H_nu^(kappa)(z) = 2 kappa (Theta_z log I_nu - nu) - Theta_z^2 log I_nu,
                                                             eq. (Hnu-kappa)

this verifies, symbolically (sympy) and at arbitrary precision (mpmath):

  * the second equality of eq. (R-r-def), z R_nu = Theta_z log I_nu - nu, and that
    r_nu > 0 on nu > -1, z > 0 -- which is what makes the sign analysis below a
    statement about the larger root only;
  * the Riccati step the proof takes from the modified Bessel equation,
    Theta_z^2 log I_nu = z^2 + nu^2 - (Theta_z log I_nu)^2 = z^2 - 2 nu r_nu - r_nu^2,
    by two independent routes (the ODE z^2 I'' + z I' = (z^2+nu^2) I, and direct
    numerical differentiation of log I_nu);
  * both forms of eq. (H-r-forms), H^(kappa) = r^2 + 2(nu+kappa) r - z^2 = 2 kappa r - z r',
    against H^(kappa) built from its definition eq. (Hnu-kappa);
  * eq. (H-Amos-general): the positive root of r^2 + 2(nu+kappa) r - z^2 is
    sqrt((nu+kappa)^2+z^2) - (nu+kappa) = z^2/(nu+kappa+sqrt((nu+kappa)^2+z^2)) as an
    exact identity, and the equivalence H^(kappa) > 0 <=> R_nu > z/(nu+kappa+sqrt(...))
    swept in both directions across a (nu, kappa, z) grid that contains failures as
    well as successes;
  * eq. (H-turan-exact) at kappa = 1, both as the algebraic rewrite
    z^2 R(R - R_{nu+1}) = z^2 (I_{nu+1}^2 - I_nu I_{nu+2})/I_nu^2 and as an identity
    with H_nu, together with the recurrence R_{nu+1} = R_nu^{-1} - 2(nu+1)/z the proof
    uses to get there;
  * eq. (Amos-bound-exact): H_nu > 0 on the whole range, equivalently the Amos-type
    lower bound R_nu > z/(nu+1+sqrt((nu+1)^2+z^2));
  * eq. (H-kappa-global): H^(kappa) = H_nu + 2(kappa-1) r_nu, so kappa >= 1 gives
    positivity everywhere; and for kappa < 1 the small-z law
    H^(kappa)(z) = ((kappa-1)/(nu+1)) z^2 + O(z^4), fitted on a log--log grid with the
    slope asserted near 2, exhibits the failure -- so kappa >= 1 is load-bearing;
  * rem:schur-correction: as z -> 0 the corrected matrix tends to
    [[g, 2], [2, 4 tau/g]], whose determinant is 4(tau-1), so tau = 1 is exactly the
    Schur amount that closes the deficit at the rank-one boundary.

The introduction states the same two facts in its unnumbered G/P/H display and names
the matrix of eq. (intro-schur-matrix), which is cor:bessel-matrix's; those are
the displays covered here and in verify_bessel_reduction.py.

The reduction of the matrix determinant itself, eqs. (U-L), (G-L), (bessel-congruence),
(D-Delta), is verify_bessel_reduction.py's; the probabilistic form of the same
coupling is verify_bessel_law.py's.
"""
from __future__ import annotations
import sympy as sp
import mpmath as mp

# ===========================================================================
# Exact symbolic certificates
# ===========================================================================
zs, nus, ks, rs, rps, Rs, Rn1s = sp.symbols('z nu kappa r rp R Rnext', real=True)

# The two forms of eq. (H-r-forms) agree exactly once the Riccati step is imposed.
# Riccati: Theta_z^2 log I = z r' = z^2 - 2 nu r - r^2.
riccati = zs**2 - 2*nus*rs - rs**2                       # = z r'
form_quadratic = rs**2 + 2*(nus + ks)*rs - zs**2
form_derivative = 2*ks*rs - riccati                       # 2 kappa r - z r'
assert sp.simplify(sp.expand(form_quadratic - form_derivative)) == 0
print('PASS: eq. (H-r-forms) r^2+2(nu+kappa)r-z^2 = 2 kappa r - z r\' under the Riccati')
print('      step z r\' = z^2 - 2 nu r - r^2')

# eq. (H-Amos-general): the positive root, in the two shapes the proof prints.
root_surd = sp.sqrt((nus + ks)**2 + zs**2) - (nus + ks)
root_rationalized = zs**2/((nus + ks) + sp.sqrt((nus + ks)**2 + zs**2))
assert sp.simplify(root_surd - root_rationalized) == 0
assert sp.simplify(form_quadratic.subs(rs, root_surd)) == 0
# The other root is negative, so on r > 0 the quadratic is positive exactly above
# root_surd; that is what turns the sign statement into a one-sided bound.
other_root = -sp.sqrt((nus + ks)**2 + zs**2) - (nus + ks)
assert sp.simplify(form_quadratic.subs(rs, other_root)) == 0
assert sp.ask(sp.Q.negative(other_root.subs({nus: sp.Rational(-1, 2), ks: 3, zs: 2}))) is not False
assert other_root.subs({nus: sp.Rational(-1, 2), ks: 3, zs: 2}).evalf() < 0
print('PASS: eq. (H-Amos-general) sqrt((nu+kappa)^2+z^2)-(nu+kappa) is the positive root of')
print('      r^2+2(nu+kappa)r-z^2 and equals z^2/(nu+kappa+sqrt((nu+kappa)^2+z^2))')

# eq. (H-turan-exact): the kappa = 1 quadratic form becomes the Turanian once the
# recurrence 2(nu+1)/z = R^{-1} - R_{nu+1} is substituted.
quad_at_one = (zs**2*Rs**2 + 2*(nus + 1)*zs*Rs - zs**2).subs(
    2*(nus + 1), zs*(1/Rs - Rn1s))
assert sp.simplify(sp.expand(quad_at_one - zs**2*Rs*(Rs - Rn1s))) == 0
Ia, Ib, Ic = sp.symbols('I_nu I_nu1 I_nu2', positive=True)
assert sp.simplify(
    (zs**2*(Ib/Ia)*((Ib/Ia) - (Ic/Ib)) - zs**2*(Ib**2 - Ia*Ic)/Ia**2)) == 0
print('PASS: eq. (H-turan-exact) z^2 R(R-R_{nu+1}) = z^2 (I_{nu+1}^2 - I_nu I_{nu+2})/I_nu^2,')
print('      and equals r^2+2(nu+1)r-z^2 under R_{nu+1} = R^{-1} - 2(nu+1)/z')

# eq. (H-kappa-global), forward half: the kappa-family is an r-shift of the endpoint.
assert sp.simplify(sp.expand(form_quadratic
                             - (rs**2 + 2*(nus + 1)*rs - zs**2)
                             - 2*(ks - 1)*rs)) == 0
print('PASS: eq. (H-kappa-global) H^(kappa) = H_nu + 2(kappa-1) r_nu')

# rem:schur-correction: the z -> 0 limit matrix and its determinant.
gs, taus = sp.symbols('g tau', positive=True)
limit_matrix = sp.Matrix([[gs, 2], [2, 4*taus/gs]])
assert sp.simplify(limit_matrix.det() - 4*(taus - 1)) == 0
assert sp.simplify(limit_matrix.det().subs(taus, 1)) == 0
print('PASS: rem:schur-correction det [[g,2],[2,4 tau/g]] = 4(tau-1), zero exactly at tau=1')

# ===========================================================================
# High-precision numerics from I_nu itself
# ===========================================================================
mp.mp.dps = 50
TOL = mp.mpf('1e-22')

def logI(nu, z):
    return mp.log(mp.besseli(nu, z))

def theta_logI(nu, z):                       # Theta_z log I_nu
    return z*mp.diff(lambda zz: logI(nu, zz), z)

def theta2_logI(nu, z):                      # Theta_z^2 log I_nu = z L' + z^2 L''
    f1 = mp.diff(lambda zz: logI(nu, zz), z, 1)
    f2 = mp.diff(lambda zz: logI(nu, zz), z, 2)
    return z*f1 + z**2*f2

def R(nu, z):
    return mp.besseli(nu + 1, z)/mp.besseli(nu, z)

def r(nu, z):
    return z*R(nu, z)

def Hk(nu, z, kappa):                        # eq. (Hnu-kappa)
    return 2*kappa*(theta_logI(nu, z) - nu) - theta2_logI(nu, z)

NUS = [mp.mpf('-0.9'), mp.mpf('-0.5'), mp.mpf(0), mp.mpf('0.5'),
       mp.mpf(2), mp.mpf('5.5')]
ZS = [mp.mpf('0.05'), mp.mpf('0.3'), mp.mpf(1), mp.mpf(3), mp.mpf(10), mp.mpf(40)]
KAPPAS = [mp.mpf(-1), mp.mpf(0), mp.mpf('0.5'), mp.mpf(1), mp.mpf('1.5'), mp.mpf(3)]

# ---- eq. (R-r-def): r_nu = z R_nu = Theta_z log I_nu - nu, and r_nu > 0. ----
for nu in NUS:
    for z in ZS:
        lhs = r(nu, z)
        assert abs(lhs - (theta_logI(nu, z) - nu)) < TOL*(1 + abs(lhs)), (nu, z)
        assert lhs > 0, (nu, z)
print('PASS: eq. (R-r-def) r_nu = z R_nu = Theta_z log I_nu - nu, and r_nu > 0 on nu>-1, z>0')

# The lowercase name is disambiguated in the text against Segura's z^{-1} I_nu/I_{nu-1};
# check the two quantities really are different, so the warning is not vacuous.
for nu, z in [(mp.mpf('0.5'), mp.mpf(2)), (mp.mpf(2), mp.mpf('0.7'))]:
    segura = mp.besseli(nu, z)/(z*mp.besseli(nu - 1, z))
    assert abs(r(nu, z) - segura) > mp.mpf('0.1'), (nu, z)
print('PASS: z R_nu differs from Segura\'s z^{-1} I_nu/I_{nu-1}, so the naming note is not vacuous')

# ---- The Riccati step, by two routes. ----
for nu in NUS:
    for z in ZS:
        direct = theta2_logI(nu, z)
        # Route 2: z^2 I'' + z I' = (z^2+nu^2) I gives Theta_z^2 log I = z^2+nu^2-(Theta_z log I)^2.
        from_ode = z**2 + nu**2 - theta_logI(nu, z)**2
        assert abs(direct - from_ode) < TOL*(1 + abs(direct)), (nu, z)
        assert abs(direct - (z**2 - 2*nu*r(nu, z) - r(nu, z)**2)) < TOL*(1 + abs(direct)), (nu, z)
        # and the modified Bessel equation itself, on which route 2 rests
        I0 = mp.besseli(nu, z)
        d1 = mp.diff(lambda zz: mp.besseli(nu, zz), z, 1)
        d2 = mp.diff(lambda zz: mp.besseli(nu, zz), z, 2)
        assert abs(z**2*d2 + z*d1 - (z**2 + nu**2)*I0) < TOL*(1 + abs(z**2*d2)), (nu, z)
print('PASS: Theta_z^2 log I_nu = z^2+nu^2-(Theta_z log I_nu)^2 = z^2-2 nu r_nu-r_nu^2,')
print('      from the modified Bessel equation and by direct differentiation')

# ---- eq. (H-r-forms) against the definition eq. (Hnu-kappa). ----
for nu in NUS:
    for z in ZS:
        rv = r(nu, z)
        rp = mp.diff(lambda zz: r(nu, zz), z)
        for kappa in KAPPAS:
            H = Hk(nu, z, kappa)
            quad = rv**2 + 2*(nu + kappa)*rv - z**2
            deriv = 2*kappa*rv - z*rp
            scale = 1 + abs(H)
            assert abs(H - quad) < TOL*scale, (nu, z, kappa)
            assert abs(H - deriv) < TOL*scale, (nu, z, kappa)
print('PASS: eq. (H-r-forms) both forms agree with H^(kappa) built from eq. (Hnu-kappa)')

# ---- eq. (H-Amos-general): the equivalence, in both directions. ----
positives = negatives = 0
for nu in NUS:
    for z in ZS:
        Rv = R(nu, z)
        for kappa in KAPPAS:
            H = Hk(nu, z, kappa)
            bound = z/(nu + kappa + mp.sqrt((nu + kappa)**2 + z**2))
            if H > 0:
                positives += 1
                assert Rv > bound, (nu, z, kappa, H, Rv, bound)
            elif H < 0:
                negatives += 1
                assert Rv < bound, (nu, z, kappa, H, Rv, bound)
# The sweep is only informative if it straddles the boundary.
assert positives > 0 and negatives > 0, (positives, negatives)
print(f'PASS: eq. (H-Amos-general) H^(kappa)>0 <=> R_nu > z/(nu+kappa+sqrt((nu+kappa)^2+z^2)),')
print(f'      on {positives} positive and {negatives} negative sample points')

# ---- eq. (H-turan-exact) and the recurrence, at kappa = 1. ----
for nu in NUS:
    for z in ZS:
        Rv, Rn = R(nu, z), R(nu + 1, z)
        assert abs(Rn - (1/Rv - 2*(nu + 1)/z)) < TOL*(1 + abs(Rn)), (nu, z)
        H = Hk(nu, z, mp.mpf(1))
        ratio_form = z**2*Rv*(Rv - Rn)
        bessel_form = z**2*(mp.besseli(nu + 1, z)**2
                            - mp.besseli(nu, z)*mp.besseli(nu + 2, z))/mp.besseli(nu, z)**2
        assert abs(H - ratio_form) < TOL*(1 + abs(H)), (nu, z)
        assert abs(H - bessel_form) < TOL*(1 + abs(H)), (nu, z)
print('PASS: eq. (H-turan-exact) H_nu = z^2 R(R-R_{nu+1}) = z^2 (I_{nu+1}^2-I_nu I_{nu+2})/I_nu^2,')
print('      with the recurrence R_{nu+1} = R_nu^{-1} - 2(nu+1)/z')

# ---- eq. (Amos-bound-exact): H_nu > 0 and the endpoint Amos bound. ----
FINE_NUS = NUS + [mp.mpf('-0.99'), mp.mpf('-0.25'), mp.mpf(1), mp.mpf(12)]
FINE_ZS = ZS + [mp.mpf('0.001'), mp.mpf('0.01'), mp.mpf(100)]
for nu in FINE_NUS:
    for z in FINE_ZS:
        assert Hk(nu, z, mp.mpf(1)) > 0, (nu, z)
        assert R(nu, z) > z/(nu + 1 + mp.sqrt((nu + 1)**2 + z**2)), (nu, z)
print('PASS: eq. (Amos-bound-exact) H_nu > 0 and R_nu > z/(nu+1+sqrt((nu+1)^2+z^2))')

# ---- eq. (H-kappa-global): the identity, kappa >= 1, and the kappa < 1 failure. ----
for nu in NUS:
    for z in ZS:
        H1 = Hk(nu, z, mp.mpf(1))
        for kappa in KAPPAS:
            H = Hk(nu, z, kappa)
            assert abs(H - (H1 + 2*(kappa - 1)*r(nu, z))) < TOL*(1 + abs(H)), (nu, z, kappa)
for nu in FINE_NUS:
    for z in FINE_ZS:
        for kappa in [mp.mpf(1), mp.mpf('1.5'), mp.mpf(3), mp.mpf(20)]:
            assert Hk(nu, z, kappa) > 0, (nu, z, kappa)
print('PASS: eq. (H-kappa-global) forward half -- H^(kappa) > 0 everywhere for kappa >= 1')

# The converse: the small-z law H^(kappa) = ((kappa-1)/(nu+1)) z^2 + O(z^4).  The slope
# is fitted rather than assumed, and a sign failure is exhibited for every kappa < 1.
GRID = [mp.mpf(2)**(-j) for j in range(6, 15)]
for nu in NUS:
    for kappa in [mp.mpf(-1), mp.mpf(0), mp.mpf('0.5'), mp.mpf('0.9'), mp.mpf('0.999')]:
        coeff = (kappa - 1)/(nu + 1)
        vals = [Hk(nu, z, kappa) for z in GRID]
        # Consecutive-pair slopes: the O(z^4) term makes the coarse end of the ladder
        # miss 2 by O(z^2), so the test is that the estimate converges, not that every
        # pair already sits on the limit.  The z^4 coefficient of H^(kappa) does not
        # vanish with kappa-1 (it is H_nu's own, since H_nu itself starts at z^4), so
        # the relative remainder carries a 1/|kappa-1| and the tolerance must too.
        slopes = [(mp.log(abs(vals[j+1])) - mp.log(abs(vals[j])))
                  / (mp.log(GRID[j+1]) - mp.log(GRID[j])) for j in range(len(GRID) - 1)]
        assert abs(slopes[-1] - 2)*abs(kappa - 1) < mp.mpf('1e-6'), (nu, kappa, slopes[-1])
        assert abs(slopes[-1] - 2) < abs(slopes[0] - 2), (nu, kappa, slopes[0], slopes[-1])
        assert abs(vals[-1]/GRID[-1]**2 - coeff)*abs(kappa - 1) < mp.mpf('1e-7')*abs(coeff), (nu, kappa)
        assert all(v < 0 for v in vals), (nu, kappa)          # negative near zero
print('PASS: eq. (H-kappa-global) converse -- H^(kappa)(z) = ((kappa-1)/(nu+1)) z^2 + O(z^4),')
print('      log--log slope 2, and strictly negative near zero for every kappa < 1')

# ---- rem:schur-correction: the z -> 0 boundary matrix, numerically. ----
def G(nu, z):
    return -mp.diff(lambda n_: logI(n_, z), nu, 2)

def P(nu, z):
    return z*mp.diff(lambda zz: mp.diff(lambda n_: logI(n_, zz), nu), z)

for nu in [mp.mpf('-0.5'), mp.mpf(0), mp.mpf('1.3')]:
    g = mp.polygamma(1, nu + 1)
    z = mp.mpf('1e-4')
    for tau in [mp.mpf('0.5'), mp.mpf(1), mp.mpf(2)]:
        M = mp.matrix([[G(nu, z), 1 + P(nu, z)],
                       [1 + P(nu, z), Hk(nu, z, mp.mpf(1)) + 4*tau/g]])
        lim = mp.matrix([[g, 2], [2, 4*tau/g]])
        assert max(abs(M[i, j] - lim[i, j]) for i in range(2) for j in range(2)) < mp.mpf('1e-6')
        assert abs(mp.det(lim) - 4*(tau - 1)) < mp.mpf('1e-40')
        # the correction is exactly what closes the rank-one deficit at tau = 1
        assert (mp.det(lim) > 0) == (tau > 1)
print('PASS: rem:schur-correction the z->0 matrix is [[g,2],[2,4 tau/g]] with det 4(tau-1),')
print('      so 4/g is exactly the Schur amount that closes the rank-one deficit')

print('ALL PASS: verify_scalar_turanian')
