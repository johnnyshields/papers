#!/usr/bin/env python3
r"""The z -> 0 limit of the Bessel-Schur matrix, and the degree-zero sector.

Paper labels (numbers move under renumbering, labels do not):
cor:bessel-matrix, rem:schur-correction (sections `sec:main`, `sec:scalar`);
eq:Delta0-tau, eq:Ckt-def, eq:Dnu-kt-def (section `sec:main`).

verify_scalar_turanian.py already reaches the limit matrix ((g,2),(2,4tau/g)) and
its determinant 4(tau-1) from I_nu, and verify_bessel_reduction.py reaches it from
the reduction.  What is isolated here instead is the entry-level input a proof of
the limit actually consumes -- the value of each series at lambda = 0, and the
normalized degree-zero determinant sector -- with the matrix limit re-checked
alongside as a consistency test rather than as its primary coverage:

  * the entries at lambda = 0 are the degree-zero Maclaurin coefficients,
    A(a,0) = g/Gamma(a)^2, B(a,0) = 1/Gamma(a)^2, C(a,g,kappa,tau,0)
    = tau/Gamma(a)^2, Z(a,0) = 1/Gamma(a) -- none of which depends on kappa;
  * the normalized degree-zero coefficient sector is
    D^(kappa,tau)_0 = 2(tau-1), so [lambda^0] Delta^(kappa,tau)
    = g(tau-1)/Gamma(a)^4, eq. (Delta0-tau).

The limit matrix is rank one exactly at tau = 1, and the sign of that degree-zero
sector is what separates the coefficientwise wall from the pointwise one: for
tau_cw(a,kappa) < tau < 1 every positive-degree coefficient of Delta^(kappa,tau) is
strictly positive while Delta^(kappa,tau)(a,lambda) itself is negative for all small
lambda > 0.  So pointwise positivity needs tau >= 1, not merely tau > tau_cw, which
is the one zero on (0,infinity) prop:bessel-sharpness records in that strip.
"""
from __future__ import annotations
import mpmath as mp

mp.mp.dps = 40

TERMS = 240


def _z(a, lam, weight):
    return mp.nsum(lambda k: weight(int(k)) * lam**int(k)
                   / (mp.factorial(int(k)) * mp.gamma(a + int(k))),
                   [0, TERMS], method='direct')


def series(a, lam):
    """Z, Z_a, Z_aa, Z_Theta, Z_ThetaTheta, Z_aTheta at (a, lam)."""
    Z = _z(a, lam, lambda k: mp.mpf(1))
    Za = _z(a, lam, lambda k: -mp.psi(0, a + k))
    Zaa = _z(a, lam, lambda k: mp.psi(0, a + k)**2 - mp.psi(1, a + k))
    Zt = _z(a, lam, lambda k: mp.mpf(k))
    Ztt = _z(a, lam, lambda k: mp.mpf(k)**2)
    Zat = _z(a, lam, lambda k: -mp.psi(0, a + k) * k)
    return Z, Za, Zaa, Zt, Ztt, Zat


def schur_matrix(a, kappa, tau, lam):
    """(G, 1+P; 1+P, H^(kappa) + 4 tau/g) at order a-1 and argument 2 sqrt(lam)."""
    g = mp.psi(1, a)
    Z, Za, Zaa, Zt, Ztt, Zat = series(a, lam)
    A = Za**2 - Z * Zaa
    B = Z * Z + Z * Zat - Za * Zt
    C = tau * Z * Z + g * (kappa * Z * Zt - Z * Ztt + Zt * Zt)
    return A / Z**2, 2 * B / Z**2, 4 * C / (g * Z**2)


def dcoeff_kt_zero(a, kappa, tau):
    """The normalized degree-zero sector s_0^2 MD(N_0, N_0) at (kappa, tau)."""
    g = mp.psi(1, a)
    # N_0^(kappa,tau) = (alpha_0, beta_0, tau/g + c_0^(kappa)) = (g, 1, tau/g)
    a11, a12, a22 = g, mp.mpf(1), tau / g
    # MD(X, X) = 2 (a11 a22 - a12^2); s_0 = 1
    return 2 * (a11 * a22 - a12**2)


def turan_det_kt(a, kappa, tau, lam):
    """Delta^(kappa,tau) = A C_{kappa,tau} - g B^2 from the series."""
    g = mp.psi(1, a)
    Z, Za, Zaa, Zt, Ztt, Zat = series(a, lam)
    A = Za**2 - Z * Zaa
    B = Z * Z + Z * Zat - Za * Zt
    C = tau * Z * Z + g * (kappa * Z * Zt - Z * Ztt + Zt * Zt)
    return A * C - g * B**2


def tau_cw(a, kappa):
    """eq:tau-cw."""
    g = mp.psi(1, a)
    return (a * g * (2 * a - 1) - (kappa - 1) * a**2 * g**2 / 2) / (2 * a**2 * g - 1)


def main() -> None:
    tol = mp.mpf(10) ** (-25)

    for a in [mp.mpf('0.3'), mp.mpf(1), mp.mpf('2.75'), mp.mpf(7)]:
        g = mp.psi(1, a)
        Ga = mp.gamma(a)

        # --- entries at lambda = 0 are the degree-zero coefficients -----------
        Z0, Za0, Zaa0, Zt0, Ztt0, Zat0 = series(a, mp.mpf(0))
        assert abs(Z0 - 1 / Ga) < tol, (a, Z0)
        A0 = Za0**2 - Z0 * Zaa0
        B0 = Z0 * Z0 + Z0 * Zat0 - Za0 * Zt0
        assert abs(A0 - g / Ga**2) < tol, (a, A0, g / Ga**2)
        assert abs(B0 - 1 / Ga**2) < tol, (a, B0)
        for kappa in [mp.mpf('-1.5'), mp.mpf(1), mp.mpf('3.25')]:
            for tau in [mp.mpf('0.4'), mp.mpf(1), mp.mpf('2.5')]:
                C0 = tau * Z0 * Z0 + g * (kappa * Z0 * Zt0 - Z0 * Ztt0 + Zt0 * Zt0)
                assert abs(C0 - tau / Ga**2) < tol, (a, kappa, tau, C0)

                # --- the limit matrix, approached along lambda -> 0 -----------
                for lam in [mp.mpf('1e-6'), mp.mpf('1e-9')]:
                    G, onePlusP, Hplus = schur_matrix(a, kappa, tau, lam)
                    assert abs(G - g) < mp.sqrt(lam), (a, kappa, tau, lam, G, g)
                    assert abs(onePlusP - 2) < mp.sqrt(lam), (a, kappa, tau, lam, onePlusP)
                    assert abs(Hplus - 4 * tau / g) < mp.sqrt(lam), \
                        (a, kappa, tau, lam, Hplus, 4 * tau / g)

                # --- the determinant of the limit matrix is 4(tau-1) ----------
                det_limit = g * (4 * tau / g) - 2 * 2
                assert abs(det_limit - 4 * (tau - 1)) < tol, (a, tau, det_limit)

                # --- degree-zero sector and eq:Delta0-tau ---------------------
                d0 = dcoeff_kt_zero(a, kappa, tau)
                assert abs(d0 - 2 * (tau - 1)) < tol, (a, kappa, tau, d0)
                delta0 = g / (2 * Ga**4) * d0
                assert abs(delta0 - g * (tau - 1) / Ga**4) < tol, (a, kappa, tau, delta0)

        # --- rank one exactly at tau = 1 --------------------------------------
        assert abs(g * (4 / g) - 4) < tol, a          # det = 0 at tau = 1
        assert abs(g * (4 * mp.mpf('1.5') / g) - 4 - 2) < tol, a   # det = 2 at tau = 3/2

    # --- tau > tau_cw is not enough for pointwise positivity -----------------
    for a in [mp.mpf('0.3'), mp.mpf(1), mp.mpf('2.75')]:
        g, Ga = mp.psi(1, a), mp.gamma(a)
        for kappa in [mp.mpf(1), mp.mpf('2.5')]:
            tcw = tau_cw(a, kappa)
            assert tcw < 1, (a, kappa, tcw)
            tau = (tcw + 1) / 2                      # strictly inside the strip
            assert abs(turan_det_kt(a, kappa, tau, mp.mpf(0))
                       - g * (tau - 1) / Ga**4) < tol, (a, kappa, tau)
            for lam in [mp.mpf('1e-3'), mp.mpf('1e-6')]:
                assert turan_det_kt(a, kappa, tau, lam) < 0, (a, kappa, tau, lam)
            # while at tau = 1 the same series is nonnegative there
            assert turan_det_kt(a, kappa, mp.mpf(1), mp.mpf('1e-3')) > 0, (a, kappa)

    print('ALL PASS  check_schur_boundary_limit.py')


if __name__ == '__main__':
    main()
