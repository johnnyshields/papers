"""Numeric check of every hypothesis `isolated_dominant_cancellation` asks for at
the panel-B data of `cor:panel-B-attractor`.

Q(t) = (1-t)(1-t/2)(1-t/4),  r = 1,  N(t,z) = 1+z+z^2+t(2-z),
64 B(t) = t^6 - 22t^5 + 141t^4 - 252t^3 + 548t^2 - 288t + 64.

Checks, all against mpmath at 40 digits:
  1. B has exactly two roots in |t| < 1/2, a nonreal conjugate pair.
  2. t_* (upper half plane) and z_* = -Q(t_*)/t_*  against the paper's decimals.
  3. The other two denominator roots u, v at z_*, their moduli, and that
     |u|, |v| > 3/2 so R = 3/2 separates.
  4. The true local spectral ratio chi_0 = |t_*| / min(|u|,|v|) against the
     paper's loose choice sigma = 1/3.
  5. B'(t_*) != 0 (t_* is a simple root of B, i.e. nu = 1).
  6. d/dt D(t, z_*) at t_* is nonzero and equals -(1/8)(t_*-u)(t_*-v),
     which is the identity the Lean proof of `hsimple` uses.
"""

import mpmath as mp

mp.mp.dps = 40

B64 = [1, -22, 141, -252, 548, -288, 64]          # t^6 ... constant
Q = lambda t: (1 - t) * (1 - t / 2) * (1 - t / 4)


def main() -> None:
    roots = mp.polyroots(B64, maxsteps=200, extraprec=200)
    inner = [r for r in roots if abs(r) < mp.mpf(1) / 2]
    assert len(inner) == 2, f"expected 2 roots in |t|<1/2, got {len(inner)}"
    assert all(abs(mp.im(r)) > mp.mpf("1e-20") for r in inner), "inner roots must be nonreal"
    t_star = max(inner, key=lambda r: mp.im(r))
    t_bar = min(inner, key=lambda r: mp.im(r))
    assert abs(mp.conj(t_star) - t_bar) < mp.mpf("1e-30"), "inner roots not a conjugate pair"
    print(f"t_*            = {mp.nstr(t_star, 20)}")
    print(f"|t_*|          = {mp.nstr(abs(t_star), 20)}   (< 1/2)")
    assert abs(t_star) < mp.mpf(1) / 2

    z_star = -Q(t_star) / t_star
    print(f"z_*            = {mp.nstr(z_star, 20)}")
    # the paper's displayed decimals
    assert abs(mp.re(z_star) - mp.mpf("-0.5655268358")) < mp.mpf("1e-9"), mp.re(z_star)
    assert abs(mp.im(z_star) - mp.mpf("1.3674915753")) < mp.mpf("1e-9"), mp.im(z_star)

    # the monic cubic -8(Q(t) + z t) = t^3 - 7t^2 + (14 - 8z)t - 8
    cub = [1, -7, 14 - 8 * z_star, -8]
    droots = mp.polyroots(cub, maxsteps=200, extraprec=200)
    near = min(droots, key=lambda r: abs(r - t_star))
    assert abs(near - t_star) < mp.mpf("1e-30"), "t_* is not a denominator root at z_*"
    others = [r for r in droots if abs(r - t_star) > mp.mpf("1e-25")]
    assert len(others) == 2, "expected two other denominator roots"
    u, v = others
    print(f"u              = {mp.nstr(u, 20)}   |u| = {mp.nstr(abs(u), 12)}")
    print(f"v              = {mp.nstr(v, 20)}   |v| = {mp.nstr(abs(v), 12)}")
    assert abs(u) > mp.mpf(3) / 2 and abs(v) > mp.mpf(3) / 2, "R = 3/2 does not separate"

    chi0 = abs(t_star) / min(abs(u), abs(v))
    print(f"chi_0          = {mp.nstr(chi0, 20)}   (paper's sigma = 1/3 is loose but valid)")
    assert chi0 < mp.mpf(1) / 3
    # the ratio the Lean hypothesis `hrho` actually needs: |t_*| / R < 1/3 at R = 3/2
    assert abs(t_star) / (mp.mpf(3) / 2) < mp.mpf(1) / 3

    # nu = 1: t_* is a simple root of B
    dB = mp.polyval([6, -110, 564, -756, 1096, -288], t_star)
    print(f"64 B'(t_*)     = {mp.nstr(dB, 20)}   |.| = {mp.nstr(abs(dB), 12)}")
    assert abs(dB) > mp.mpf("1e-20"), "t_* would be a repeated root of B"

    # hsimple: d_t D(t, z_*) at t_*, and the factored form used in Lean
    dD = -mp.mpf(7) / 4 + (mp.mpf(7) / 4) * t_star - (mp.mpf(3) / 8) * t_star**2 + z_star
    dD_fac = -(mp.mpf(1) / 8) * (t_star - u) * (t_star - v)
    print(f"d_t D(t_*,z_*) = {mp.nstr(dD, 20)}   |.| = {mp.nstr(abs(dD), 12)}")
    assert abs(dD) > mp.mpf("1e-20"), "t_* would be a repeated denominator root"
    assert abs(dD - dD_fac) < mp.mpf("1e-30"), "the factored identity for hsimple fails"

    print("ALL PASS")


if __name__ == "__main__":
    main()
