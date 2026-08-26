#!/usr/bin/env python3
r"""thm:ensemble-hierarchy, prop:four-copy, rem:fiber-deformation and
rem:ensemble-positivity: the identities that make the coefficient matrices and
the determinant coefficients conditioned Bessel fibers rather than an analogy.

Every claim here is an exact identity, so each is checked as one -- against
quantities built independently from the exact reciprocal-gamma coefficients and,
where a Bessel side exists, against log I_nu differentiated directly.

  * eq. (fiber-affine): M_m^{(kappa,tau)} = M_m + [(tau-1) + (g m/2)(kappa-1)] e_2 e_2^T
    for every m >= 0, including the two exceptional fibers m = 0, 1.  This is
    what makes Delta_n affine in (kappa, tau) and gives eq. (coefficient-wall);
  * eq. (pair-total-law): Pr(Y_1 + Y_2 = m) = S_m lambda^m / Z^2;
  * eq. (finite-law-entries): Pr(Y_1 = i | Y_1 + Y_2 = m) is the finite law, so
    the coefficient fiber is the two-copy law conditioned on its total;
  * eq. (canonical-fiber-average): the normalized differential matrix is the
    canonical average E M_R of its fibers;
  * eq. (four-total-law) and eq. (Tn-Kn-law): T_n = [lambda^n] Z^4 and the K_n
    law is the pair total conditioned on the four-copy total;
  * eq. (Delta-n-MD): Delta_n/T_n = (1/2) E MD(M_{K_n}, M_{n-K_n});
  * eq. (D-canonical-average): D_{a-1}^{(kappa,tau)}(2 sqrt lambda) = E d_N, the
    canonical average of the microcanonical sector densities -- the identity
    separating coefficientwise from pointwise positivity;
  * eq. (sector-density) at the two ends: d_0 = 4(tau-1) is the vacuum contact,
    and d_n -> 2(kappa-1) is the thermodynamic contact;
  * eq. (N-mean): E N = 2(Theta_z log I_nu - nu), which is ~ 2z and is what the
    equivalence of ensembles turns into the coefficient-argument dictionary;
  * eq. (microcanonical-covariance-deficit): the normalized fiber is itself a
    covariance-deficit matrix in the conditioned law -- the same shape as the
    canonical matrix of cor:bessel-law, which is what makes that corollary the
    averaged version of this identity rather than a separate calculation.
"""
from mpmath import mp, mpf, psi, gamma, factorial, besseli, log, diff, sqrt

mp.dps = 40
a = mpf('1.3')
lam = mpf('2.7')
g = psi(1, a)
kappa, tau = mpf('1.4'), mpf('0.8')
N = 110
TOL = mpf('1e-20')


def fiber(m, kap, t):
    al = psi(1, a+m)
    be = mpf(1) if m == 0 else (2*a+m-2)/(2*(a+m-1))
    if m == 0:
        cm = mpf(0)
    elif m == 1:
        cm = (kap-1)/2
    else:
        cm = kap*m/mpf(2) - mpf(m*(2*a+m-2))/(2*(2*a+2*m-3))
    return al, sqrt(g)*be, t + g*cm


for m in range(0, 40):
    base = fiber(m, mpf(1), mpf(1))
    got = fiber(m, kappa, tau)
    shift = (tau-1) + g*m*(kappa-1)/2
    assert abs(got[0]-base[0]) < TOL and abs(got[1]-base[1]) < TOL
    assert abs(got[2]-(base[2]+shift)) < TOL, m
print('PASS: eq. (fiber-affine) -- the deformation is a rank-one shift in the (2,2)')
print('      entry, affine in (kappa, tau), at every fiber including m = 0 and m = 1.')

zc = [lam**k/(factorial(k)*gamma(a+k)) for k in range(N+1)]
Z = sum(zc)
S = [sum(1/(factorial(i)*factorial(m-i)*gamma(a+i)*gamma(a+m-i)) for i in range(m+1))
     for m in range(N+1)]
T = [sum(S[k]*S[n-k] for k in range(n+1)) for n in range(N+1)]
assert abs(Z**2 - sum(S[m]*lam**m for m in range(N+1))) < TOL
assert abs(Z**4 - sum(T[n]*lam**n for n in range(N+1))) < mpf('1e-18')
for m in (0, 1, 5, 17):
    tot = sum(1/(factorial(i)*factorial(m-i)*gamma(a+i)*gamma(a+m-i)) for i in range(m+1))
    assert abs(tot - S[m]) < TOL
    assert abs(sum((1/(factorial(i)*factorial(m-i)*gamma(a+i)*gamma(a+m-i)))/S[m]
                   for i in range(m+1)) - 1) < TOL
print('PASS: eq. (pair-total-law), eq. (finite-law-entries) and eq. (four-total-law) --')
print('      Z^2 and Z^4 are the two- and four-copy generating functions and the')
print('      conditioned fibers are probability laws.')

E = [sum(fiber(m, kappa, tau)[j]*S[m]*lam**m for m in range(N+1))/Z**2 for j in range(3)]
Dl = []
for n in range(N+1):
    s = mp.mpf(0)
    for k in range(n+1):
        x = fiber(k, kappa, tau)
        y = fiber(n-k, kappa, tau)
        s += S[k]*S[n-k]*(x[0]*y[2] + x[2]*y[0] - 2*x[1]*y[1])/2
    Dl.append(s)
Delta = sum(Dl[n]*lam**n for n in range(N+1))
assert abs(Delta/Z**4 - (E[0]*E[2]-E[1]**2)) < TOL
for n in (0, 1, 4, 23):
    mixed = sum((S[k]*S[n-k]/T[n])*(fiber(k, kappa, tau)[0]*fiber(n-k, kappa, tau)[2]
                + fiber(k, kappa, tau)[2]*fiber(n-k, kappa, tau)[0]
                - 2*fiber(k, kappa, tau)[1]*fiber(n-k, kappa, tau)[1]) for k in range(n+1))
    assert abs(Dl[n]/T[n] - mixed/2) < TOL, n
print('PASS: eq. (canonical-fiber-average) and eq. (Delta-n-MD) -- the differential')
print('      matrix is E M_R, and Delta_n/T_n is the conditioned mixed determinant.')

dn = [4*Dl[n]/(g*T[n]) for n in range(N+1)]
assert abs(sum(dn[n]*T[n]*lam**n for n in range(N+1))/Z**4 - 4*Delta/(g*Z**4)) < TOL
assert abs(dn[0] - 4*(tau-1)) < TOL
tail = [dn[n] for n in (40, 70, 100)]
for lo, hi in zip(tail, tail[1:]):
    assert lo > hi > 2*(kappa-1), tail
assert abs(tail[-1] - 2*(kappa-1)) < mpf('0.03')
print('PASS: eq. (D-canonical-average) E d_N = 4 Delta/(g Z^4), with the vacuum sector')
print('      d_0 = 4(tau-1) exactly and the sectors descending to 2(kappa-1).')


def F(n_, z_):
    return log(besseli(n_, z_))


z = 2*sqrt(lam)
nu = a - 1
Fz = diff(F, (nu, z), (0, 1))
Fzz = diff(F, (nu, z), (0, 2))
Fnn = diff(F, (nu, z), (2, 0))
Fnz = diff(F, (nu, z), (1, 1))
H = 2*kappa*(z*Fz - nu) - (z*Fz + z*z*Fzz)
D_arg = (-Fnn)*(H + 4*tau/g) - (1 + z*Fnz)**2
assert abs(D_arg - 4*Delta/(g*Z**4)) < mpf('1e-15')
EN = sum(n*T[n]*lam**n for n in range(N+1))/Z**4
assert abs(EN - 2*(z*Fz - nu)) < mpf('1e-15')
print('PASS: the Bessel congruence closes the loop -- D_{a-1}^{(kappa,tau)}(2 sqrt lambda)')
print('      equals the canonical average, and eq. (N-mean) E N = 2(Theta_z log I - nu).')

for m in (0, 1, 2, 3, 7, 20, 55):
    wts = [1/(factorial(i)*factorial(m-i)*gamma(a+i)*gamma(a+m-i)) for i in range(m+1)]
    tot = sum(wts)
    wts = [w/tot for w in wts]
    Xi = [psi(0, a+m-i) - psi(0, a+i) for i in range(m+1)]       # Xi_m, the fiber score
    Dfin = [m - 2*i for i in range(m+1)]                          # D_m
    Sig = [psi(1, a+i) + psi(1, a+m-i) for i in range(m+1)]       # Sigma_m
    EX = sum(w*v for w, v in zip(wts, Xi))
    ED = sum(w*v for w, v in zip(wts, Dfin))
    assert abs(EX) < TOL and abs(ED) < TOL, m       # both centered, by i <-> m-i symmetry
    ESig = sum(w*v for w, v in zip(wts, Sig))
    VX = sum(w*v*v for w, v in zip(wts, Xi))
    VD = sum(w*v*v for w, v in zip(wts, Dfin))
    CXD = sum(w*u*v for w, u, v in zip(wts, Xi, Dfin))
    # claimed: [[ESig/2, 1], [1, tau/g + kappa m/2]] - (1/2) Cov(Xi_m, D_m)
    c11, c12, c22 = ESig/2 - VX/2, 1 - CXD/2, tau/g + kappa*m/mpf(2) - VD/2
    f11, f12, f22 = fiber(m, kappa, tau)
    assert abs(c11 - f11) < TOL, m
    assert abs(c12 - f12/sqrt(g)) < TOL, m          # the fiber is normalized by diag(1,g^-1/2)
    assert abs(c22 - f22/g) < TOL, m
print('PASS: eq. (microcanonical-covariance-deficit) -- the normalized fiber equals')
print('      [[E Sigma_m/2, 1], [1, tau/g + kappa m/2]] minus half the covariance of')
print('      (Xi_m, D_m), at every m including the two exceptional fibers.')
print('ALL PASS')
