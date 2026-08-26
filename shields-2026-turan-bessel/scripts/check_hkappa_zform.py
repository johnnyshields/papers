#!/usr/bin/env python3
r"""The second diagonal direction as a shifted reciprocal-gamma Turanian.

Paper labels (numbers move under renumbering, labels do not):
prop:scalar-H, eq:H-r-forms, eq:H-turan-exact, eq:H-kappa-global (section
`sec:scalar`); eq:Hnu-kappa, eq:G-L (section `sec:main`); eq:Zdef
(section `sec:main`).

The Euler series of Z shift the parameter rather than the argument:

    Z_Theta(a,lam)      = lam Z(a+1,lam),
    Z_ThetaTheta(a,lam) = lam ( lam Z(a+2,lam) + Z(a+1,lam) ),

so eq:G-L's H^(kappa) = 4 kappa L_Theta - 4 L_ThetaTheta becomes

    H^(kappa) = 4 lam [ (kappa-1) Z_1/Z - lam (Z Z_2 - Z_1^2)/Z^2 ],
    Z = Z(a,lam), Z_1 = Z(a+1,lam), Z_2 = Z(a+2,lam),

which is checked here against H^(kappa) built from the modified Bessel ratio by
eq:H-r-forms.  Three consequences the proof of eq:H-kappa-global rests on:

  * at kappa = 1 the bracket is -lam (Z Z_2 - Z_1^2)/Z^2, so H_nu > 0 is exactly
    the Turan inequality Z_1^2 > Z Z_2 for the reciprocal-gamma series, which is
    the midpoint case of strict concavity of a -> log Z(a,lam) -- and that
    concavity is -L_aa = A/Z^2 > 0, already proved for the paper's G_nu;
  * H^(kappa) - H^(1) = 4 (kappa-1) lam Z_1/Z, positive for kappa > 1;
  * H^(kappa)/(4 lam) -> (kappa-1)/a as lam decreases to zero, so for kappa < 1
    the second diagonal direction is negative for all small z > 0.
"""
from __future__ import annotations
import mpmath as mp

mp.mp.dps = 40

TERMS = 240


def _z(a, lam, weight):
    return mp.nsum(lambda k: weight(int(k)) * lam**int(k)
                   / (mp.factorial(int(k)) * mp.gamma(a + int(k))),
                   [0, TERMS], method='direct')


def Z(a, lam):
    return _z(a, lam, lambda k: mp.mpf(1))


def Z_theta(a, lam):
    return _z(a, lam, lambda k: mp.mpf(k))


def Z_theta2(a, lam):
    return _z(a, lam, lambda k: mp.mpf(k)**2)


def H_from_series(a, kappa, lam):
    """4 kappa L_Theta - 4 L_ThetaTheta, eq:G-L."""
    z, e, e2 = Z(a, lam), Z_theta(a, lam), Z_theta2(a, lam)
    return 4 * kappa * e / z - 4 * (z * e2 - e**2) / z**2


def H_from_zshift(a, kappa, lam):
    """The shifted form 4 lam [ (kappa-1) Z_1/Z - lam (Z Z_2 - Z_1^2)/Z^2 ]."""
    z, z1, z2 = Z(a, lam), Z(a + 1, lam), Z(a + 2, lam)
    return 4 * lam * ((kappa - 1) * z1 / z - lam * (z * z2 - z1**2) / z**2)


def H_from_bessel(nu, kappa, zarg):
    """r^2 + 2(nu+kappa) r - z^2 with r = z I_{nu+1}(z)/I_nu(z), eq:H-r-forms."""
    r = zarg * mp.besseli(nu + 1, zarg) / mp.besseli(nu, zarg)
    return r**2 + 2 * (nu + kappa) * r - zarg**2


def main() -> None:
    tol = mp.mpf(10) ** (-22)

    for a in [mp.mpf('0.3'), mp.mpf(1), mp.mpf('2.75'), mp.mpf(7)]:
        nu = a - 1
        for lam in [mp.mpf('0.05'), mp.mpf('1.5'), mp.mpf(9)]:
            # --- the two Euler-series shift identities -----------------------
            assert abs(Z_theta(a, lam) - lam * Z(a + 1, lam)) < tol, (a, lam)
            assert abs(Z_theta2(a, lam)
                       - lam * (lam * Z(a + 2, lam) + Z(a + 1, lam))) < tol, (a, lam)

            zarg = 2 * mp.sqrt(lam)
            for kappa in [mp.mpf('-0.5'), mp.mpf('0.75'), mp.mpf(1), mp.mpf('2.5')]:
                hs = H_from_series(a, kappa, lam)
                hz = H_from_zshift(a, kappa, lam)
                hb = H_from_bessel(nu, kappa, zarg)
                assert abs(hs - hz) < tol * max(1, abs(hs)), (a, kappa, lam, hs, hz)
                assert abs(hs - hb) < mp.mpf(10)**(-18) * max(1, abs(hs)), \
                    (a, kappa, lam, hs, hb)

                # --- the kappa-shift ------------------------------------------
                h1 = H_from_series(a, mp.mpf(1), lam)
                assert abs(hs - h1 - 4 * (kappa - 1) * lam * Z(a + 1, lam) / Z(a, lam)) \
                    < tol * max(1, abs(hs)), (a, kappa, lam)

            # --- Turan inequality for the reciprocal-gamma series -------------
            z, z1, z2 = Z(a, lam), Z(a + 1, lam), Z(a + 2, lam)
            assert z1**2 > z * z2, (a, lam, z1**2, z * z2)
            # equivalently, the midpoint case of concavity of a -> log Z
            assert 2 * mp.log(z1) > mp.log(z) + mp.log(z2), (a, lam)
            assert H_from_series(a, mp.mpf(1), lam) > 0, (a, lam)

        # --- kappa < 1 fails for all small z, at this fixed a -----------------
        for kappa in [mp.mpf('-0.5'), mp.mpf('0.75'), mp.mpf('0.999')]:
            for lam in [mp.mpf('1e-4'), mp.mpf('1e-6')]:
                h = H_from_series(a, kappa, lam)
                assert h < 0, (a, kappa, lam, h)
                # the normalized limit is (kappa-1)/a
                assert abs(h / (4 * lam) - (kappa - 1) / a) < mp.sqrt(lam), \
                    (a, kappa, lam, h / (4 * lam), (kappa - 1) / a)

    print('ALL PASS  check_hkappa_zform.py')


if __name__ == '__main__':
    main()
