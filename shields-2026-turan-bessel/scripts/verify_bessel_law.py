#!/usr/bin/env python3
r"""Paper section `subsec:microcanonical` (Microcanonical Bessel fibers and canonical averaging),
subsec:microcanonical: cor:bessel-law, and the endpoint covariance form
eq. (covariance-ineq).

Everything is arbitrary precision (mpmath).  For a > 0, lambda > 0 the law is

    P(K = k) = lambda^k / (k! Gamma(a+k) Z(a,lambda)),   k >= 0,     eq. (bessel-law)

with Psi = psi(a+K), mu = E K, sigma^2 = Var K, g = psi_1(a), and L = log Z.
Three independent routes to the same numbers are carried side by side and compared:

  (i)   the law itself, summed term by term from eq. (bessel-law);
  (ii)  derivatives of L = log Z with Z = 0F1(;a;lambda)/Gamma(a) taken numerically,
        which never touches the summands of route (i);
  (iii) the Bessel side, G_nu, P_nu, H_nu^(kappa) differentiated from I_nu directly,
        with nu = a-1 and z = 2 sqrt(lambda).

Verified:

  * eq. (bessel-law) is a probability law, and under a = nu+1, z = 2 sqrt(lambda) it is
    the discrete Bessel law (z/2)^{2k+nu}/(I_nu(z) k! Gamma(k+nu+1));
  * eq. (bessel-law-meanvar): L_Theta = mu and L_{Theta Theta} = sigma^2, routes (i) and (ii);
  * eq. (bessel-law-param): L_a = -E Psi, L_{a Theta} = -Cov(Psi, K), and
    -L_{aa} = E psi_1(a+K) - Var Psi, routes (i) and (ii);
  * eq. (H-dispersion): H_nu^(kappa) = 4(kappa mu - sigma^2), route (iii) against route (i),
    so that H_nu > 0 is exactly underdispersion Var K < E K -- checked as an equivalence
    across a grid that contains both signs;
  * eq. (covariance-deficit-matrix): the diag(1,1/2) congruence of the Bessel--Schur matrix
    is [[E psi_1(a+K) - Var Psi, 1 - Cov(Psi,K)], [1 - Cov(Psi,K), tau/g + kappa mu - sigma^2]];
  * eq. (covariance-loewner): that matrix is [[E psi_1(a+K), 1], [1, tau/g + kappa mu]]
    minus the covariance matrix of (Psi, K);
  * eq. (covariance-ineq): the strict endpoint inequality
    (1 - Cov(Psi,K))^2 < (E psi_1(a+K) - Var Psi)(1/g + E K - Var K), swept in a and lambda,
    together with the two scalar deficits it couples.

The matrix reduction behind the congruence, eqs. (U-L), (G-L), (bessel-congruence),
(D-Delta), is verify_bessel_reduction.py's; the scalar forms of H are
verify_scalar_turanian.py's.
"""
from __future__ import annotations
import mpmath as mp

mp.mp.dps = 60
TOL = mp.mpf('1e-25')

# ===========================================================================
# Route (i) -- the law of eq. (bessel-law), summed term by term
# ===========================================================================
def law_moments(a, lam, kmax=None):
    """Total mass and the moments cor:bessel-law needs, from eq. (bessel-law)."""
    if kmax is None:
        # far past the mean 2 sqrt(lambda)/2 and its fluctuation scale
        kmax = int(mp.floor(40 + 6*mp.sqrt(lam) + 12*mp.sqrt(mp.sqrt(lam) + 1)))
        while True:
            tail = lam**kmax/(mp.factorial(kmax)*mp.gamma(a + kmax))
            if tail < mp.mpf('1e-45'):
                break
            kmax *= 2
    w = [lam**k/(mp.factorial(k)*mp.gamma(a + k)) for k in range(kmax + 1)]
    Zs = mp.fsum(w)
    p = [wk/Zs for wk in w]
    psi = [mp.digamma(a + k) for k in range(kmax + 1)]
    tri = [mp.polygamma(1, a + k) for k in range(kmax + 1)]
    EK = mp.fsum(p[k]*k for k in range(kmax + 1))
    EK2 = mp.fsum(p[k]*k*k for k in range(kmax + 1))
    EPsi = mp.fsum(p[k]*psi[k] for k in range(kmax + 1))
    EPsi2 = mp.fsum(p[k]*psi[k]**2 for k in range(kmax + 1))
    EPsiK = mp.fsum(p[k]*psi[k]*k for k in range(kmax + 1))
    Etri = mp.fsum(p[k]*tri[k] for k in range(kmax + 1))
    return {
        'Z': Zs, 'mass': mp.fsum(p), 'p': p,
        'mu': EK, 'sigma2': EK2 - EK**2,
        'EPsi': EPsi, 'VarPsi': EPsi2 - EPsi**2,
        'Cov': EPsiK - EPsi*EK, 'Etri': Etri,
    }

# ===========================================================================
# Route (ii) -- derivatives of L = log Z, Z = 0F1(;a;lambda)/Gamma(a)
# ===========================================================================
def Lfun(a, lam):
    return mp.log(mp.hyp0f1(a, lam)) - mp.loggamma(a)

def L_theta(a, lam):                     # Theta_lambda L
    return lam*mp.diff(lambda x: Lfun(a, x), lam)

def L_thetatheta(a, lam):                # Theta_lambda^2 L = lam L_lam + lam^2 L_lamlam
    d1 = mp.diff(lambda x: Lfun(a, x), lam, 1)
    d2 = mp.diff(lambda x: Lfun(a, x), lam, 2)
    return lam*d1 + lam**2*d2

def L_a(a, lam):
    return mp.diff(lambda y: Lfun(y, lam), a)

def L_aa(a, lam):
    return mp.diff(lambda y: Lfun(y, lam), a, 2)

def L_atheta(a, lam):                    # Theta_lambda d_a L
    return lam*mp.diff(lambda x: mp.diff(lambda y: Lfun(y, x), a), lam)

# ===========================================================================
# Route (iii) -- the Bessel side, from I_nu itself
# ===========================================================================
def logI(nu, z):
    return mp.log(mp.besseli(nu, z))

def G_nu(nu, z):                         # eq. (Gnu)
    return -mp.diff(lambda n_: logI(n_, z), nu, 2)

def P_nu(nu, z):                         # eq. (Pnu)
    return z*mp.diff(lambda zz: mp.diff(lambda n_: logI(n_, zz), nu), z)

def H_nu(nu, z, kappa):                  # eq. (Hnu-kappa)
    f1 = mp.diff(lambda zz: logI(nu, zz), z, 1)
    f2 = mp.diff(lambda zz: logI(nu, zz), z, 2)
    return 2*kappa*(z*f1 - nu) - (z*f1 + z**2*f2)

SAMPLES = [(mp.mpf('0.4'), mp.mpf('0.3')), (mp.mpf(1), mp.mpf(2)),
           (mp.mpf('2.5'), mp.mpf(7)), (mp.mpf('0.8'), mp.mpf(15))]
KAPPAS = [mp.mpf('0.25'), mp.mpf(1), mp.mpf('2.5')]
TAUS = [mp.mpf('0.5'), mp.mpf(1), mp.mpf(3)]

# ---- eq. (bessel-law): a probability law, and the discrete Bessel form. ----
for a, lam in SAMPLES:
    M = law_moments(a, lam)
    assert abs(M['mass'] - 1) < TOL, (a, lam)
    nu, z = a - 1, 2*mp.sqrt(lam)
    for k in [0, 1, 3, 9]:
        bessel_form = (z/2)**(2*k + nu)/(mp.besseli(nu, z)*mp.factorial(k)*mp.gamma(k + nu + 1))
        assert abs(M['p'][k] - bessel_form) < TOL*(1 + abs(bessel_form)), (a, lam, k)
print('PASS: eq. (bessel-law) is a probability law and equals the discrete Bessel law')
print('      (z/2)^{2k+nu}/(I_nu(z) k! Gamma(k+nu+1)) under a = nu+1, z = 2 sqrt(lambda)')

# ---- eq. (bessel-law-meanvar) and eq. (bessel-law-param): routes (i) vs (ii). ----
for a, lam in SAMPLES:
    M = law_moments(a, lam)
    assert abs(Lfun(a, lam) - mp.log(M['Z'])) < TOL, (a, lam)
    assert abs(L_theta(a, lam) - M['mu']) < TOL*(1 + M['mu']), (a, lam)
    assert abs(L_thetatheta(a, lam) - M['sigma2']) < TOL*(1 + M['sigma2']), (a, lam)
    assert abs(L_a(a, lam) + M['EPsi']) < TOL*(1 + abs(M['EPsi'])), (a, lam)
    assert abs(L_atheta(a, lam) + M['Cov']) < TOL*(1 + abs(M['Cov'])), (a, lam)
    deficit = M['Etri'] - M['VarPsi']
    assert abs(-L_aa(a, lam) - deficit) < TOL*(1 + abs(deficit)), (a, lam)
    assert deficit > 0, (a, lam)                    # = G_nu > 0
print('PASS: eq. (bessel-law-meanvar) L_Theta = mu, L_{Theta Theta} = sigma^2')
print('PASS: eq. (bessel-law-param) L_a = -E Psi, L_{a Theta} = -Cov(Psi,K),')
print('      -L_{aa} = E psi_1(a+K) - Var Psi')

# ---- eq. (H-dispersion), and underdispersion as an equivalence. ----
under = over = 0
for a, lam in SAMPLES:
    M = law_moments(a, lam)
    nu, z = a - 1, 2*mp.sqrt(lam)
    for kappa in KAPPAS:
        H = H_nu(nu, z, kappa)
        pred = 4*(kappa*M['mu'] - M['sigma2'])
        assert abs(H - pred) < mp.mpf('1e-20')*(1 + abs(H)), (a, lam, kappa)
        if H > 0:
            under += 1
            assert kappa*M['mu'] > M['sigma2'], (a, lam, kappa)
        else:
            over += 1
            assert kappa*M['mu'] < M['sigma2'], (a, lam, kappa)
    # the endpoint statement itself: H_nu > 0 is exactly Var K < E K
    assert (H_nu(nu, z, mp.mpf(1)) > 0) == (M['sigma2'] < M['mu']), (a, lam)
    assert M['sigma2'] < M['mu'], (a, lam)
assert under > 0 and over > 0, (under, over)
print(f'PASS: eq. (H-dispersion) H_nu^(kappa) = 4(kappa mu - sigma^2), on {under} positive and')
print(f'      {over} negative sample points; at kappa=1 it is exactly Var K < E K')

# ---- eq. (covariance-deficit-matrix) and eq. (covariance-loewner). ----
for a, lam in SAMPLES:
    M = law_moments(a, lam)
    nu, z = a - 1, 2*mp.sqrt(lam)
    g = mp.polygamma(1, a)
    G, P = G_nu(nu, z), P_nu(nu, z)
    for kappa in KAPPAS:
        for tau in TAUS:
            BS = mp.matrix([[G, 1 + P], [1 + P, H_nu(nu, z, kappa) + 4*tau/g]])
            D = mp.matrix([[1, 0], [0, mp.mpf(1)/2]])
            congruent = D*BS*D
            claimed = mp.matrix(
                [[M['Etri'] - M['VarPsi'], 1 - M['Cov']],
                 [1 - M['Cov'], tau/g + kappa*M['mu'] - M['sigma2']]])
            assert max(abs(congruent[i, j] - claimed[i, j])
                       for i in range(2) for j in range(2)) < mp.mpf('1e-20')
            # eq. (covariance-loewner): the same matrix as a Loewner difference
            base = mp.matrix([[M['Etri'], 1], [1, tau/g + kappa*M['mu']]])
            cov = mp.matrix([[M['VarPsi'], M['Cov']], [M['Cov'], M['sigma2']]])
            loewner = base - cov
            assert max(abs(loewner[i, j] - claimed[i, j])
                       for i in range(2) for j in range(2)) < mp.mpf('1e-40')
            # the covariance matrix subtracted is a genuine covariance matrix
            assert cov[0, 0] > 0 and cov[1, 1] > 0
            assert mp.det(cov) > -mp.mpf('1e-40')
print('PASS: eq. (covariance-deficit-matrix) diag(1,1/2) congruence of the Bessel--Schur matrix')
print('PASS: eq. (covariance-loewner) the same matrix is [[E psi_1(a+K),1],[1,tau/g+kappa mu]]')
print('      minus the covariance matrix of (Psi, K)')

# ---- eq. (covariance-ineq): the strict endpoint inequality, swept. ----
AGRID = [mp.mpf(s) for s in ('0.05', '0.2', '0.5', '0.9', '1', '1.7', '3', '6', '11')]
LGRID = [mp.mpf(s) for s in ('0.01', '0.1', '1', '4', '12', '30')]
worst = None
for a in AGRID:
    g = mp.polygamma(1, a)
    for lam in LGRID:
        M = law_moments(a, lam)
        lhs = (1 - M['Cov'])**2
        rhs = (M['Etri'] - M['VarPsi'])*(1/g + M['mu'] - M['sigma2'])
        assert lhs < rhs, (a, lam, lhs, rhs)
        assert M['Etri'] - M['VarPsi'] > 0, (a, lam)      # G_nu > 0
        assert M['mu'] - M['sigma2'] > 0, (a, lam)        # H_nu/4 > 0
        margin = (rhs - lhs)/rhs
        if worst is None or margin < worst[0]:
            worst = (margin, a, lam)
print('PASS: eq. (covariance-ineq) (1-Cov(Psi,K))^2 < (E psi_1(a+K)-Var Psi)(1/g+E K-Var K)')
print(f'      on {len(AGRID)}x{len(LGRID)} points; tightest relative margin '
      f'{mp.nstr(worst[0], 4)} at a={mp.nstr(worst[1], 4)}, lambda={mp.nstr(worst[2], 4)}')

# The correction is load-bearing, and rem:schur-correction says exactly how much of it:
# in these variables the uncorrected (tau = 0) determinant tends to -1 as lambda -> 0,
# because the law degenerates to K = 0, so mu = sigma^2 = Var Psi = Cov = 0 and the
# matrix tends to [[g, 1], [1, 0]].  A general tau leaves tau - 1 in the limit.
broken = 0
for a in AGRID:
    g = mp.polygamma(1, a)
    for lam in LGRID:
        M = law_moments(a, lam)
        if (1 - M['Cov'])**2 > (M['Etri'] - M['VarPsi'])*(M['mu'] - M['sigma2']):
            broken += 1
    small = mp.mpf('1e-12')
    Ms = law_moments(a, small)
    for tau in TAUS + [mp.mpf(0)]:
        det0 = ((Ms['Etri'] - Ms['VarPsi'])*(tau/g + Ms['mu'] - Ms['sigma2'])
                - (1 - Ms['Cov'])**2)
        assert abs(det0 - (tau - 1)) < mp.mpf('1e-6'), (a, tau, det0)
assert broken > 0
print(f'PASS: rem:schur-correction in probabilistic form -- as lambda -> 0 the determinant of')
print(f'      eq. (covariance-deficit-matrix) tends to tau-1, so tau=0 gives -1 and the')
print(f'      correction is load-bearing; it already fails at {broken} of the '
      f'{len(AGRID)*len(LGRID)} swept points')

print('ALL PASS: verify_bessel_law')
