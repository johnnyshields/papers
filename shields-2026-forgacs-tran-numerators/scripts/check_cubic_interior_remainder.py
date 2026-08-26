r"""Paper subsection `subsec:weighted-dominance` (Weighted principal-pair dominance).

Targets `eq:interior-remainder` and `lem:contour-separation` at the witness pencil
`Q = (1-t)^3`, `r = 1`, `B = 3t^2 + 1`, in the explicit form the Lean now proves, and then
instantiates the strong-clock statement built on top of it.

TWO CLAIMS, and the first is what makes the second non-vacuous.

(1) The separating radius is `R0 = 1` and the constants are explicit.  The denominator
    `D(t) = (1-t)^3 + z t` has three zeros: the principal pair at modulus `tau` and a third
    at `1/tau^2`.  Since `tau < 1` on the open arc, `R0 = 1` separates them at every angle,
    and on `[e, pi-e]` the whole subarc is served by the single pair `(tau(e), tau(e))` of
    `(tau_max, sigma)`.  On `|t| = 1` the factorization then gives

        |D(t)| >= (1 - tau)^2 (1/tau^2 - 1) >= (1 - tau(e))^2 (1/tau(e)^2 - 1) =: Dlo,

    so `|B/D| <= 4/Dlo` there and the remainder obeys `|R_M| <= tau(e) (4/Dlo) tau(e)^M`.
    Every inequality in that chain is asserted here against the remainder computed directly.

(2) The composed strong-clock statement is instantiable.  Its window binders ask for a
    `u0` with `cos u0 = 0` sitting inside `[Phi(a) + delta, Phi(b) - pi - delta]`, which is
    non-empty only once `Phi` turns by more than `2 pi + 2 delta` across the subarc.  A
    theorem whose hypotheses cannot be met is worth nothing, so the threshold in `M` is
    located here rather than asserted, and a witness `u0` is exhibited at each `M` past it.

`F_M` runs through the defining recurrence of `eq:F-M-def`, never Horner.  The branch is the
closed form `tau = 1/(2 cos((pi-theta)/3))` the Lean tree carries, cross-checked in
`check_cubic_second_derivatives.py`.  The subarc `[1.75, 2.55]` avoids `pi/2`, where `B`
vanishes on the branch and the amplitude floor does not exist.
"""

from mpmath import mp, mpf, mpc, fabs, re, im, pi, cos, sin, exp, floor, ceil

mp.dps = 120

I = mpc(0, 1)
BCO = [mpf(1), mpf(0), mpf(3)]


def tau(t):
    return 1 / (2 * cos((pi - t) / 3))


def gam(t):
    return tau(t) * exp(I * t)


def zbranch(t):
    g = gam(t)
    z = -(1 - g) ** 3 / g
    assert fabs(im(z)) < mpf(10) ** (-60), f"z left the reals at {t}"
    return re(z)


def D(t, x):
    return (1 - x) ** 3 + zbranch(t) * x


def dD(t, x):
    return -3 * (1 - x) ** 2 + zbranch(t)


def W(t):
    """`ftAmp` = -B(gamma)/D'(gamma)."""
    g = gam(t)
    return -(3 * g ** 2 + 1) / dD(t, g)


def coeff_F(M, z):
    c = []
    for m in range(M + 1):
        v = BCO[m] if m < len(BCO) else mpf(0)
        if m >= 1:
            v -= (z - 3) * c[m - 1]
        if m >= 2:
            v -= 3 * c[m - 2]
        if m >= 3:
            v += c[m - 3]
        c.append(v)
    return c[M], max(fabs(x) for x in c)


def remainder(M, t):
    """`ftRemainder`: the normalized coefficient with the principal pair removed."""
    val, big = coeff_F(M, zbranch(t))
    margin = mp.dps - (mp.log(max(big, mpf(1))) / mp.log(10))
    assert margin > 30, f"precision margin collapsed to {mp.nstr(margin,6)} at M={M}"
    scaled = tau(t) ** (M + 1) * val
    pair = 2 * re(W(t) * exp(-I * (M + 1) * t))
    return fabs(scaled - pair)


# --------------------------------------------------------------------------
# (1) The explicit constants of `cubic_interior_remainder`.
# --------------------------------------------------------------------------

E = mpf('0.5')
taue = tau(E)
Dlo = (1 - taue) ** 2 * (1 / taue ** 2 - 1)
CI = taue * (4 / Dlo)
SIGMA = taue

print(f"      e = {mp.nstr(E,4)}   tau(e) = {mp.nstr(taue,8)}   Dlo = {mp.nstr(Dlo,8)}   "
      f"CI = {mp.nstr(CI,8)}   sigma = {mp.nstr(SIGMA,8)}")
assert taue < 1, "tau(e) is not below the separating radius R0 = 1"
assert Dlo > 0, "the denominator floor is not positive"

# the separation R0 = 1 really does separate, at every angle of the subarc
worst_pair, worst_third = mpf(0), mpf('inf')
for k in range(0, 201):
    th = E + (pi - E - E) * mpf(k) / mpf(200)
    worst_pair = max(worst_pair, tau(th))
    worst_third = min(worst_third, 1 / tau(th) ** 2)
print(f"      on [e, pi-e]: max |principal pair| = {mp.nstr(worst_pair,8)}, "
      f"min |third zero| = {mp.nstr(worst_third,8)}")
assert worst_pair < 1 < worst_third, \
    "R0 = 1 does not separate the principal pair from the third zero on the subarc"
print("PASS  R0 = 1 separates the pair from the third zero at every angle of [e, pi-e]")

# the floor on |D| over the unit circle, and the B/D bound it gives
worst_ratio = mpf(0)
for k in range(0, 41):
    th = E + (pi - E - E) * mpf(k) / mpf(40)
    for j in range(0, 60):
        x = exp(2 * pi * I * mpf(j) / mpf(60))
        dv = fabs(D(th, x))
        assert dv >= Dlo * (1 - mpf(10) ** (-30)), \
            f"|D| = {mp.nstr(dv,8)} fell below the floor Dlo = {mp.nstr(Dlo,8)} " \
            f"at theta={mp.nstr(th,6)}"
        worst_ratio = max(worst_ratio, fabs(3 * x ** 2 + 1) / dv)
print(f"PASS  |D| >= Dlo on the unit circle at every sampled angle; worst |B/D| = "
      f"{mp.nstr(worst_ratio,8)} against the asserted bound 4/Dlo = {mp.nstr(4/Dlo,8)}")
assert worst_ratio <= 4 / Dlo, "the B/D bound the Lean asserts is violated"

# and the remainder bound itself
print()
worst_slack = mpf('inf')
for M in (8, 12, 18, 26, 36, 50):
    worst = mpf(0)
    for k in range(0, 25):
        th = E + (pi - E - E) * mpf(k) / mpf(24)
        worst = max(worst, remainder(M, th))
    bound = CI * SIGMA ** M
    print(f"      M = {M:>3d}   max |R_M| = {mp.nstr(worst,8):>14s}   "
          f"bound CI sigma^M = {mp.nstr(bound,8):>14s}   slack = {mp.nstr(bound/worst,6)}")
    assert worst <= bound, \
        f"the remainder {mp.nstr(worst,8)} exceeds the Lean's bound {mp.nstr(bound,8)} at M={M}"
    worst_slack = min(worst_slack, bound / worst)
print(f"\nPASS  |R_M| <= tau(e)(4/Dlo) tau(e)^M on [e, pi-e] at every M tested; "
      f"tightest slack {mp.nstr(worst_slack,6)}")


# --------------------------------------------------------------------------
# (2) The composed statement is instantiable: a `u0` exists past a threshold in M.
# --------------------------------------------------------------------------

A, Bb = mpf('1.75'), mpf('2.55')
DELTA = pi / 4
assert A > pi / 2, "the subarc must avoid the amplitude divisor at pi/2"
assert Bb < pi and E <= A and Bb <= pi - E, "the subarc must sit inside [e, pi-e]"


def psi_diff(M, lo, hi, samples=20000):
    """`psi(hi) - psi(lo)` by integrating `psi' = Im(W'/W)` -- only the difference is
    needed, and the branch is continuous on a subarc missing pi/2."""
    h = (hi - lo) / mpf(samples)
    total = mpf(0)
    for k in range(samples):
        t = lo + h * (mpf(k) + mpf('0.5'))
        eps = mpf(10) ** (-25)
        lg = (W(t + eps) - W(t - eps)) / (2 * eps) / W(t)
        total += im(lg) * h
    return total


dpsi = psi_diff(1, A, Bb)
print(f"\n      subarc [{mp.nstr(A,4)}, {mp.nstr(Bb,4)}], delta = pi/4, "
      f"psi(b) - psi(a) = {mp.nstr(dpsi,8)}")

found = None
for M in range(2, 40):
    turn = (mpf(M) + 1) * (Bb - A) - dpsi
    room = turn - pi - 2 * DELTA
    if room >= pi:                     # a half-integer multiple of pi is then guaranteed
        found = M
        break
assert found is not None, "the phase never turns enough for a u0 to exist"
print(f"      Phi turns by more than 2pi + 2delta from M = {found} onward, so the window "
      f"[Phi(a)+delta, Phi(b)-pi-delta] contains a point of pi/2 + pi Z")

for M in (found, found + 3, found + 9):
    # Phi(a) is only defined up to the branch constant; take psi(a) = 0, which is the
    # normalization `cubicPsi a a = 0` the Lean's branch carries.
    phi_a = (mpf(M) + 1) * A
    phi_b = (mpf(M) + 1) * Bb - dpsi
    lo, hi = phi_a + DELTA, phi_b - pi - DELTA
    n = ceil((lo - pi / 2) / pi)
    u0 = pi / 2 + n * pi
    assert lo <= u0 <= hi, f"no admissible u0 at M={M}"
    assert fabs(cos(u0)) < mpf(10) ** (-60), "the exhibited u0 is not a zero of cos"
    print(f"      M = {M:>3d}   window [{mp.nstr(lo,8)}, {mp.nstr(hi,8)}]   "
          f"u0 = {mp.nstr(u0,8)}   cos u0 = {mp.nstr(cos(u0),3)}")

print("\nPASS  the strong-clock window binders are satisfiable, with a witness u0 exhibited")
print("\nALL PASS  check_cubic_interior_remainder.py")
