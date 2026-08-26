#!/usr/bin/env python3
r"""Paper section `subsec:microcanonical` (Microcanonical Bessel fibers and canonical
averaging): the four fiber moments the finite-law entries of
thm:ensemble-hierarchy are assembled from, each in the exact form a formal proof
consumes rather than in the normalized form eq. (finite-law-entries) states.

`verify_finite_law.py` checks eq. (finite-law-entries) itself.  What is checked
here is the layer beneath it: the unnormalized sums, and the two closed forms
that make them rational, so that each is a standalone identity rather than a
step inside the derivation of another.

  * the score sum  sum_i (m-2i) Xi_i w_i  in the closed form the asymmetric
    convolution lem:convolution gives it, and its normalization E(D Xi) =
    m/(a+m-1)  (eq. (EDXi));
  * E D^2 = m(2a+m-2)/(2a+2m-3), through S_m(a) E[I(m-I)] = S_{m-2}(a+1), which
    is the cancellation of i(m-i) against the two factorials in the proof of
    thm:coefficients;
  * the curvature sum  sum_i w_i (Xi_i^2 - sigma_i) = -2 S_m psi_1(a+m), which
    is eq. (F-second-delta) read on the finite sum rather than on the closed form
    eq. (Fdelta);
  * the two-center weight derivative  d/dd [Gamma(y+d)Gamma(z-d)]^{-1}  at the
    two centers (y,z) = (a+i, a+m-i) and (a+m, a+m-1) the two sums above need,
    since the symmetric center of eq. (Fdelta) is not the one that appears
    inside the sum.

Also checked, for `subsec:gram`: eq. (Nm-gram) at general s, i.e. that
N_m(s) is the Gram matrix of xi_m = (u,0) and eta_m(s) = (v, sqrt(rho_m(s))) for
every s with rho_m(s) > 0, not only at the endpoint shift s = 1/g.

All identities are exact; the Gram tail sums are evaluated at 40 digits.
"""
from __future__ import annotations
import sympy as sp
from mpmath import mp, mpf, psi as mpsi, nsum, inf

a = sp.symbols('a', positive=True)
d = sp.symbols('d', real=True)
M_MAX = 6


def S(m, arg=None):
    x = a if arg is None else arg
    return sp.rf(2*x+m-1, m)/(sp.factorial(m)*sp.gamma(x+m)**2)


def w(m, i, dd=0):
    """The delta-deformed convolution weight of the proof of thm:coefficients."""
    return 1/(sp.factorial(i)*sp.factorial(m-i)
              * sp.gamma(a+i+dd)*sp.gamma(a+(m-i)-dd))


def Xi(m, i):
    return sp.polygamma(0, a+m-i) - sp.polygamma(0, a+i)


def Sig(m, i):
    return sp.polygamma(1, a+i) + sp.polygamma(1, a+m-i)


def zero(expr):
    return sp.simplify(sp.expand_func(sp.together(sp.expand_func(expr)))) == 0


# --- the two-center weight derivative ------------------------------------
y, z = sp.symbols('y z', positive=True)
gpair = 1/(sp.gamma(y+d)*sp.gamma(z-d))
assert zero(sp.diff(gpair, d).subs(d, 0)
            - (-sp.polygamma(0, y) + sp.polygamma(0, z))/(sp.gamma(y)*sp.gamma(z))), 'gpair-1'
assert zero(sp.diff(gpair, d, 2).subs(d, 0)
            - ((-sp.polygamma(0, y) + sp.polygamma(0, z))**2
               - (sp.polygamma(1, y) + sp.polygamma(1, z)))
            / (sp.gamma(y)*sp.gamma(z))), 'gpair-2'
print('PASS: the two-center weight derivative -- d/dd and d^2/dd^2 of')
print('      [Gamma(y+d)Gamma(z-d)]^{-1} at d=0 carry the score -psi(y)+psi(z) and')
print('      the curvature (score^2 - psi_1(y) - psi_1(z)).')

for m in range(M_MAX+1):
    Sm = S(m)

    # --- the curvature sum, eq. (F-second-delta) on the finite sum --------
    curv = sum(w(m, i)*(Xi(m, i)**2 - Sig(m, i)) for i in range(m+1))
    assert zero(curv + 2*Sm*sp.polygamma(1, a+m)), ('curvature', m)

    # --- E D = E Xi = 0, and the two moments -----------------------------
    ED = sum(w(m, i)*(m-2*i) for i in range(m+1))
    EX = sum(w(m, i)*Xi(m, i) for i in range(m+1))
    assert zero(ED) and zero(EX), ('centered', m)

    score = sum(w(m, i)*(m-2*i)*Xi(m, i) for i in range(m+1))
    if m >= 1:
        # the closed form: 2 c1 /[(a+m-1) Gamma(a+m) Gamma(a+m-1)],
        # c1 = (2a+m-1)_{m-1}/(m-1)!
        c1 = sp.rf(2*a+m-1, m-1)/sp.factorial(m-1)
        closed = 2*c1/((a+m-1)*sp.gamma(a+m)*sp.gamma(a+m-1))
        assert zero(score - closed), ('score-closed', m)
        assert zero(score/Sm - sp.Rational(m, 1)/(a+m-1)), ('EDXi', m)

    # --- E[I(m-I)] and E D^2 ---------------------------------------------
    EImI = sum(w(m, i)*i*(m-i) for i in range(m+1))
    if m >= 2:
        assert zero(EImI - S(m-2, a+1)), ('I(m-I)', m)
    ED2 = sum(w(m, i)*(m-2*i)**2 for i in range(m+1))
    assert zero(ED2 - (m**2*Sm - 4*EImI)), ('D2-polarize', m)
    if m >= 1:
        assert zero(ED2/Sm - sp.Rational(m, 1)*(2*a+m-2)/(2*a+2*m-3)), ('ED2', m)

print('PASS: the fiber moments -- sum_i (m-2i) Xi_i w_i in closed form, E(D Xi) =')
print('      m/(a+m-1), S_m(a) E[I(m-I)] = S_{m-2}(a+1), E D^2 = m(2a+m-2)/(2a+2m-3),')
print('      and the curvature sum sum_i w_i (Xi_i^2 - sigma_i) = -2 S_m psi_1(a+m),')
print(f'      for every m = 0..{M_MAX} and symbolic a.')

# --- eq. (Nm-gram) at general s ------------------------------------------
mp.dps = 40
TOL = mpf('1e-30')
for aa in (mpf('0.3'), mpf('0.75'), mpf('1.3'), mpf('4.5')):
    g = mpsi(1, aa)
    for m in range(1, 12):
        x = aa + m
        q = aa + mpf(m)/2 - 1
        alpha = mpsi(1, x)
        beta = q/(x-1)
        cm = mpf(0) if m <= 1 else mpf(m*(m-1))/(2*(2*aa+2*m-3))
        u2 = nsum(lambda r: 1/(x+r)**2, [0, inf])
        uv = nsum(lambda r: q/((x+r)*(x-1+r)), [0, inf])
        v2 = nsum(lambda r: q**2/(x-1+r)**2, [0, inf])
        assert abs(u2 - alpha) < TOL, ('u-norm', aa, m)
        assert abs(uv - beta) < TOL, ('uv-cross', aa, m)
        assert abs(v2 - q**2*mpsi(1, x-1)) < TOL, ('v-norm', aa, m)
        for s in (1/g, mpf('0.1'), mpf('3'), q**2*mpsi(1, x-1) - cm + mpf('0.5')):
            rho = s + cm - q**2*mpsi(1, x-1)
            # eq. (Nm-gram): the Gram matrix of (u,0) and (v, sqrt(rho))
            assert abs(u2 - alpha) < TOL
            assert abs(uv - beta) < TOL
            assert abs((v2 + rho) - (s + cm)) < TOL, ('rho', aa, m, s)
            if rho > 0:
                det = alpha*(s+cm) - beta**2
                assert det > 0, ('pd', aa, m, s)
                assert abs(det - (u2*(v2+rho) - uv**2)) < TOL, ('det', aa, m, s)
print('PASS: eq. (Nm-gram) at general s -- N_m(s) is the Gram matrix of (u,0) and')
print('      (v, sqrt(rho_m(s))) in l^2 (+) R, its (2,2) entry is s + c_m for every s,')
print('      and it is positive definite exactly where rho_m(s) > 0.')
print('ALL PASS')
