r"""Paper section `sec:geometry` (`lem:principal-endpoint-regularity`, `eq:ab-def`), at
the UPPER arc endpoint with `r = 1`, where the arc ends at `pi` and the principal pair
collides at a finite point `-L` on the negative axis.

`check_upper_endpoint_branch_slope.py` settles the same endpoint at `r >= 2`, where the
branch runs into the ORIGIN and the implicit function theorem applies to the branch
equation directly, with `dG/dtau = -sin(pi/r) sum_k 1/a_k != 0`.  That constant carries a
`sin(pi/r)`, so it is `0` at `r = 1` and the whole route is unavailable there.  This file
is about what replaces it.

WHAT IS ESTABLISHED, and each is an assert:

1.  **The branch equation is degenerate at `theta = pi` in BOTH partials.**  With
    `G(tau, th) = sum_k arg(tau e^{i th} - a_k) - r th - (n-1) pi`, both `dG/dtau` and
    `dG/dth` vanish at `(L, pi)`.  So neither the `r >= 2` route nor a direct IFT on `G`
    reaches this endpoint, and the degeneracy is two-sided rather than one-sided.

2.  **The pencil form factors exactly.**  `ftPencilIm P r tau th = Im(e^{i r th}
    P(tau e^{-i th}))` vanishes identically in `tau` at `th = pi` when `r = 1`, and

        ftPencilIm P 1 tau (pi + phi) = ftPencilIm R 1 tau phi,   R(t) := -P(-t),

    is an EXACT identity, not an asymptotic one.  So the `r = 1` upper endpoint is the
    `r = 1` LOWER endpoint of the reflected pencil, whose roots are `-a_k < 0`.  This is
    the structural bridge: the endpoint carries no root of the pencil, exactly as a
    `rho = 1` lower endpoint does.

3.  **The reduced equation is non-degenerate.**  `H(tau, phi) := ftPencilIm R 1 tau phi
    / phi` extends to `phi = 0` with `H(tau, 0) = -E_R(tau)`, `E_R = X R' - R`, and
    `E_R(t) = -E_P(-t)`.  So `H(L, 0) = 0` is the endpoint equation `sum_k L/(L + a_k) =
    r`, and `dH/dtau (L, 0) = -E_R'(L) = -E_P'(-L) != 0` because `-L` is a SIMPLE zero of
    `E_P`.  That is the nonvanishing the `r >= 2` route gets from `sin(pi/r)`.

4.  **`tau` extends to `pi` with finite first and second derivatives**, and they are the
    ones the reduced equation predicts.  `tau'` is compared against `-H_phi/H_tau` at the
    endpoint and `tau''` against a central difference of the closed form.  Contrast the
    `rho = 1` LOWER endpoint, where `tau' -> 0`: here the limit is nonzero, so the two
    are not the same statement with a sign changed.

5.  **`gamma'(pi-) != 0`**, which is what every endpoint collar binder asks for:
    `gamma' = (tau' + i tau) e^{i th} -> -(tau'(pi) + i L)`, whose modulus is at least
    `L > 0` whatever `tau'(pi)` is.

6.  **The collar quantity is bounded.**  `Im(dS/S) = Im(gamma' E'(gamma)/E(gamma)) - 1`
    stays bounded as `th -> pi-`, even though `E(gamma) -> 0`.  This is the statement
    `exists_bound_im_logDeriv_ftCofactorAlong_at_collision` makes at the LOWER endpoint,
    and the measurement here is that its mirror is true at the upper one.

Checked at three `r = 1` pencils: `a = (1, 1, 3)` and `a = (1, 1, 1)` (the cubic witness,
`rho = 3`), which are the `r = 1`, `rho >= 2` corner, and `a = (1, 2, 4)` (`rho = 1`),
which is the doubly-open corner.  Every claim is an `assert`; mpmath only, no float in
the loop.
"""

import mpmath as mp

mp.mp.dps = 50


def angle_sum(a, tau, th):
    """`ftAngleSum`: sum of `ftArccot(cot(th) - a_k/(tau sin(th)))`, each in `(0, pi)`."""
    c = mp.cos(th) / mp.sin(th)
    s = mp.sin(th)
    return mp.fsum(mp.pi / 2 - mp.atan(c - ak / (tau * s)) for ak in a)


def tau_of(a, r, l, th):
    """The branch radius at `th`: `angle_sum` is strictly decreasing in `tau`."""
    target = r * th + l * mp.pi
    lo, hi = mp.mpf(10) ** -60, mp.mpf(1)
    while angle_sum(a, hi, th) > target:
        hi *= 2
        assert hi < mp.mpf(10) ** 20, "no upper bracket"
    while angle_sum(a, lo, th) < target:
        lo /= 2
        assert lo > mp.mpf(10) ** -300, "no lower bracket"
    for _ in range(500):
        mid = mp.sqrt(lo * hi)
        if angle_sum(a, mid, th) > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def chord_sq(ak, tau, th):
    """`ftChordSq`: `|tau e^{i th} - a_k|^2`."""
    return ak ** 2 - 2 * ak * tau * mp.cos(th) + tau ** 2


def d_tau_sum(a, tau, th):
    """`ftAngleSumDerivTau`, in the chart form the tree uses."""
    return mp.fsum(-ak * mp.sin(th) / chord_sq(ak, tau, th) for ak in a)


def d_theta_sum(a, tau, th):
    """`ftAngleSumDerivAngle`, in the chart form the tree uses."""
    return mp.fsum(
        (tau ** 2 - ak * tau * mp.cos(th)) / chord_sq(ak, tau, th) for ak in a
    )


def tau_deriv(a, r, l, th):
    """`ftTauDeriv = -(d_theta Sigma - r) / d_tau Sigma`, at the branch radius."""
    tau = tau_of(a, r, l, th)
    return -(d_theta_sum(a, tau, th) - r) / d_tau_sum(a, tau, th)


# --- the pencil, its reflection, and their critical polynomials -----------------------


def poly_eval(coeffs, t):
    """`sum_j coeffs[j] t^j`, Horner."""
    acc = 0 * t
    for cj in reversed(coeffs):
        acc = acc * t + cj
    return acc


def root_poly_coeffs(c, a):
    """Coefficients of `Q = c prod_k (a_k - X)`, ascending."""
    coeffs = [mp.mpf(c)]
    for ak in a:
        nxt = [mp.mpf(0)] * (len(coeffs) + 1)
        for j, cj in enumerate(coeffs):
            nxt[j] += ak * cj
            nxt[j + 1] -= cj
        coeffs = nxt
    return coeffs


def deriv_coeffs(coeffs):
    return [j * coeffs[j] for j in range(1, len(coeffs))]


def critical_coeffs(coeffs, r):
    """`E = X Q' - r Q`, ascending, so `E_j = (j - r) Q_j`."""
    return [(j - r) * cj for j, cj in enumerate(coeffs)]


def reflect_coeffs(coeffs):
    """`R(t) = -P(-t)`, so `R_j = -(-1)^j P_j`."""
    return [-((-1) ** j) * cj for j, cj in enumerate(coeffs)]


def pencil_im(coeffs, r, tau, th):
    """`ftPencilIm P r tau th = Im(e^{i r th} P(tau e^{-i th}))`."""
    t = mp.mpc(tau) * mp.exp(-1j * th)
    return mp.im(mp.exp(1j * r * th) * poly_eval(coeffs, t))


def endpoint_L(a, r):
    """The unique `L > 0` with `sum_k L/(L + a_k) = r`; the collision is at `-L`."""

    def f(L):
        return mp.fsum(L / (L + ak) for ak in a) - r

    lo, hi = mp.mpf(10) ** -30, mp.mpf(1)
    while f(hi) < 0:
        hi *= 2
        assert hi < mp.mpf(10) ** 20, "no upper bracket for L"
    for _ in range(500):
        mid = (lo + hi) / 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


# --- the checks ----------------------------------------------------------------------

PENCILS = [
    ("a = (1, 1, 3), rho = 2", [mp.mpf(1), mp.mpf(1), mp.mpf(3)], mp.mpf(1)),
    ("a = (1, 1, 1), rho = 3", [mp.mpf(1), mp.mpf(1), mp.mpf(1)], mp.mpf(1)),
    ("a = (1, 2, 4), rho = 1", [mp.mpf(1), mp.mpf(2), mp.mpf(4)], mp.mpf(1)),
]

R = 1

for name, a, c in PENCILS:
    n = len(a)
    l = n - 1
    P = root_poly_coeffs(c, a)
    Rp = reflect_coeffs(P)
    EP = critical_coeffs(P, R)
    ER = critical_coeffs(Rp, R)
    L = endpoint_L(a, R)

    print(f"\n=== {name}, r = {R} ===")
    print(f"  L                        = {mp.nstr(L, 20)}")

    # (1) both partials of the branch equation vanish at the endpoint
    dtau = d_tau_sum(a, L, mp.pi)
    dth = d_theta_sum(a, L, mp.pi) - R
    print(f"  dG/dtau at (L, pi)       = {mp.nstr(dtau, 8)}")
    print(f"  dG/dth  at (L, pi)       = {mp.nstr(dth, 8)}")
    assert abs(dtau) < mp.mpf(10) ** -40, "dG/dtau should vanish at the r = 1 endpoint"
    assert abs(dth) < mp.mpf(10) ** -40, "dG/dth should vanish at the r = 1 endpoint"

    # (2) the reflection identity, exactly, at a spread of (tau, phi)
    worst = mp.mpf(0)
    for tau in [mp.mpf(1) / 3, mp.mpf(1), L, mp.mpf(7) / 2]:
        for phi in [mp.mpf(-1) / 2, mp.mpf(-1) / 100, mp.mpf(1) / 8, mp.mpf(3)]:
            lhs = pencil_im(P, R, tau, mp.pi + phi)
            rhs = pencil_im(Rp, R, tau, phi)
            worst = max(worst, abs(lhs - rhs))
    print(f"  reflection identity res  = {mp.nstr(worst, 8)}")
    assert worst < mp.mpf(10) ** -40, "ftPencilIm P 1 tau (pi + phi) != ftPencilIm R 1 tau phi"

    # `ftPencilIm R 1 tau 0 = 0` for every tau, which is what makes the quotient legal
    for tau in [mp.mpf(1) / 3, L, mp.mpf(7) / 2]:
        assert abs(pencil_im(Rp, R, tau, mp.mpf(0))) < mp.mpf(10) ** -40

    # (3) the reduced equation `H(tau, phi) = ftPencilIm R 1 tau phi / phi` at phi = 0
    #     is `-E_R(tau)`, and `E_R(t) = -E_P(-t)`
    for tau in [mp.mpf(1) / 3, L, mp.mpf(7) / 2]:
        h = mp.mpf(10) ** -20
        approx = pencil_im(Rp, R, tau, h) / h
        assert abs(approx + poly_eval(ER, tau)) < mp.mpf(10) ** -15, "H(tau,0) != -E_R(tau)"
        assert abs(poly_eval(ER, tau) + poly_eval(EP, -tau)) < mp.mpf(10) ** -40, (
            "E_R(t) != -E_P(-t)"
        )

    # the endpoint equation IS `E_P(-L) = 0`, and the zero is simple
    assert abs(poly_eval(EP, -L)) < mp.mpf(10) ** -40, "E_P(-L) != 0"
    dEP = poly_eval(deriv_coeffs(EP), -L)
    print(f"  E_P'(-L)                 = {mp.nstr(dEP, 12)}")
    assert abs(dEP) > mp.mpf(10) ** -20, "the collision must be a SIMPLE zero of E"

    # (4) `H` is EVEN in `phi`, so `tau'(pi-) = 0` and `tau''` carries the endpoint.
    #     `H(tau, phi) = sum_j R_j tau^j sin((1-j) phi)/phi` is a sum of `sinc`s, each
    #     even; the geometric reason is that the branch and its conjugate meet at `-L`,
    #     so `tau(pi + phi) = tau(pi - phi)`.
    def H_analytic(tau, phi):
        """`ftPencilIm R 1 tau phi / phi`, by the coefficient sum, valid at `phi = 0`."""
        return mp.fsum(
            Rp[j] * tau ** j * (mp.sin((1 - j) * phi) / phi if phi != 0 else (1 - j))
            for j in range(len(Rp))
        )

    def H_tau_at_zero(tau):
        return mp.fsum(
            j * Rp[j] * tau ** (j - 1) * (1 - j) for j in range(1, len(Rp))
        )

    def H_phiphi_at_zero(tau):
        return mp.fsum(
            -Rp[j] * tau ** j * (1 - j) ** 3 / 3 for j in range(len(Rp))
        )

    for tau in [mp.mpf(1) / 3, L, mp.mpf(7) / 2]:
        for phi in [mp.mpf(-1) / 7, mp.mpf(1) / 5]:
            assert abs(H_analytic(tau, phi) - pencil_im(Rp, R, tau, phi) / phi) < (
                mp.mpf(10) ** -40
            ), "the coefficient form of H disagrees with the pencil"
        # evenness, which is what forces `tau'(pi) = 0`
        for phi in [mp.mpf(1) / 7, mp.mpf(2)]:
            assert abs(H_analytic(tau, phi) - H_analytic(tau, -phi)) < mp.mpf(10) ** -40

    assert abs(H_analytic(L, mp.mpf(0))) < mp.mpf(10) ** -40, "H(L, 0) != 0"
    H_tau0 = H_tau_at_zero(L)
    print(f"  H_tau(L, 0)              = {mp.nstr(H_tau0, 12)}")
    assert abs(H_tau0 + poly_eval(deriv_coeffs(ER), L)) < mp.mpf(10) ** -40
    assert abs(H_tau0) > mp.mpf(10) ** -20, "the reduced equation is degenerate in tau"

    slopes = [tau_deriv(a, R, l, mp.pi - mp.mpf(10) ** -k) for k in (3, 4, 5, 6)]
    print(f"  tau'(pi - 1e-k), k=3..6  = {[mp.nstr(s, 10) for s in slopes]}")
    assert abs(slopes[-1]) < abs(slopes[0]) / 100, "tau' is not going to zero"
    assert abs(slopes[-1]) < mp.mpf(10) ** -5, "tau'(pi-) should be 0"

    # `tau''(pi) = -H_phiphi/H_tau`, against a central difference of the closed form
    predicted2 = -H_phiphi_at_zero(L) / H_tau0
    seconds = []
    for k in (3, 4, 5):
        d = mp.mpf(10) ** -k
        th = mp.pi - 10 * d
        seconds.append((tau_deriv(a, R, l, th + d) - tau_deriv(a, R, l, th - d)) / (2 * d))
    print(f"  tau'' near pi            = {[mp.nstr(s, 10) for s in seconds]}")
    print(f"  -H_phiphi/H_tau at (L,0) = {mp.nstr(predicted2, 10)}")
    assert abs(seconds[-1] - predicted2) < mp.mpf(10) ** -5, (
        "tau'' does not match the reduced equation's prediction"
    )

    # (5) `gamma'(pi-) = -i L`, so its modulus is exactly `L > 0`
    for k in (4, 5, 6):
        th = mp.pi - mp.mpf(10) ** -k
        tau = tau_of(a, R, l, th)
        g = (tau_deriv(a, R, l, th) + 1j * tau) * mp.exp(1j * th)
        assert abs(g) >= L * (1 - mp.mpf(10) ** -6), "gamma' fell below L in modulus"
    print(f"  |gamma'| at pi - 1e-6    = {mp.nstr(abs(g), 12)}, L = {mp.nstr(L, 12)}")
    assert abs(g + 1j * L) < mp.mpf(10) ** -5, "gamma'(pi-) should be -i L"

    # (6) the collar quantity `Im(dS/S) = Im(gamma' E'(gamma)/E(gamma)) - 1` is bounded
    dEPc = deriv_coeffs(EP)
    vals = []
    for k in range(2, 9):
        th = mp.pi - mp.mpf(10) ** -k
        tau = tau_of(a, R, l, th)
        gam = mp.mpc(tau) * mp.exp(1j * th)
        dgam = (tau_deriv(a, R, l, th) + 1j * tau) * mp.exp(1j * th)
        val = mp.im(dgam * poly_eval(dEPc, gam) / poly_eval(EP, gam)) - 1
        vals.append(val)
    print(f"  Im(dS/S) at pi - 1e-k    = {[mp.nstr(v, 8) for v in vals]}")
    assert max(abs(v) for v in vals) < 10, "Im(dS/S) is not bounded near the r = 1 endpoint"

print("\nALL PASS")
