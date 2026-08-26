r"""Paper section `subsec:strong-clock` (The strong clock).

Targets `eq:local-strong-clock` and `eq:local-phase-quantization` at the witness pencil
`Q = (1-t)^3`, `r = 1`, `B = 3t^2 + 1` -- the pencil the Lean tree already carries as
`cubicQ`/`witB`, whose phase `cubicPsi` has a closed-form derivative.

`prop:local-strong-clock` is the one result of the manuscript with no unconditional instance
at any pencil in the formalization, so this script supplies the numeric target: the second
derivative of the phase, which the `O(M^{-3})` term needs and which nothing has yet bounded,
and the spacing law itself fitted on a log-log ladder rather than sampled.

Everything runs through the DEFINING RECURRENCE of `eq:F-M-def`,

    c_m = b_m - (z-3)c_{m-1} - 3c_{m-2} + c_{m-3},

never through Horner on the expanded coefficient list.  Measured on a sibling pencil, Horner
at `M = 60` wiped out 40 working digits against coefficients reaching `9.2e39` and reported
2968 violations of 3001 that were not there.  A precision-adequacy margin is asserted at every
`M` and printed, so a future run cannot silently lose that headroom.
"""

from mpmath import (mp, mpf, mpc, fabs, im, re, exp, sin, cos, pi, findroot, diff, log,
                    arg, sqrt, matrix, lu_solve)

mp.dps = 170

I = mpc(0, 1)


# --------------------------------------------------------------------------
# The pencil.
# --------------------------------------------------------------------------

def Q(t):
    return (1 - t) ** 3


def B(t):
    return 3 * t ** 2 + 1


def g(t):
    r"""`g(t) = -Q(t)/t^r` at `r = 1`."""
    return -Q(t) / t


def dtD(t, z):
    r"""`\partial_t D(t,z) = Q'(t) + r z t^{r-1}`, at `r = 1`."""
    return -3 * (1 - t) ** 2 + z


def tau(theta):
    r"""The branch radius: the `\tau > 0` on the ray at angle `\theta` with `\Im g = 0`."""
    e = exp(I * theta)

    def h(x):
        t = x * e
        return im((1 - t) ** 3 / t)

    # the branch runs from tau(0+) = 1 (the triple zero) outward; bracket and solve
    return findroot(h, mpf('0.9') if theta < pi / 2 else mpf('1.5'), tol=mpf(10) ** (-70))


def zbranch(theta):
    z = g(tau(theta) * exp(I * theta))
    assert fabs(im(z)) < mpf(10) ** (-60), f"z left the reals at theta={theta}: {im(z)}"
    return re(z)


def W(theta):
    r"""`eq:W-def`: the principal amplitude `W(\theta) = -B(t_+)/\partial_tD(t_+,z)`."""
    t = tau(theta) * exp(I * theta)
    return -B(t) / dtD(t, zbranch(theta))


# --------------------------------------------------------------------------
# 1. The phase and its first two derivatives on a compact subarc.
#    psi' is what `cubicPsi`'s closed form gives; psi'' is what the O(M^-3)
#    term of `eq:local-strong-clock` needs and what nothing bounds yet.
# --------------------------------------------------------------------------

# A compact subarc of (0, pi), off both endpoints AND clear of the amplitude divisor.
# `lem:amplitude-divisor` puts a zero of `W` wherever `B` vanishes on the branch, and
# `B = 3t^2+1` does so at `theta = pi/2` -- the single angle `cubicWitness_hinterior`
# carries.  `prop:local-strong-clock` is stated on a zero-FREE subarc, so a window
# straddling pi/2 is not a numerical inconvenience but a different hypothesis: `psi`
# jumps by pi there, and every derivative below would be meaningless.
SUB_LO, SUB_HI = mpf('1.75'), mpf('2.55')


def psi(theta):
    return arg(W(theta))


# psi is continuous on the subarc (no branch crossing): verify before differentiating
prev = psi(SUB_LO)
worst_jump = mpf(0)
for k in range(1, 121):
    th = SUB_LO + (SUB_HI - SUB_LO) * mpf(k) / mpf(120)
    cur = psi(th)
    worst_jump = max(worst_jump, fabs(cur - prev))
    prev = cur
assert worst_jump < mpf('0.05'), \
    f"psi is not continuous on the subarc as sampled (jump {worst_jump}); a jump near pi is a " \
    f"ZERO of W inside the window -- the amplitude divisor of `lem:amplitude-divisor` -- and " \
    f"`prop:local-strong-clock` is stated on a zero-free subarc, so move the window off it"

psi1_max = mpf(0)
psi2_max = mpf(0)
for k in range(0, 41):
    th = SUB_LO + (SUB_HI - SUB_LO) * mpf(k) / mpf(40)
    d1 = diff(psi, th)
    d2 = diff(psi, th, 2)
    psi1_max = max(psi1_max, fabs(d1))
    psi2_max = max(psi2_max, fabs(d2))

# `eq:phase-derivative-bound` asserts |psi'| <= kappa; the Lean tree carries 3/2 for this
# pencil (`cubicPsi_sub_le`).  Confirm the closed-form bound really holds here.
assert psi1_max <= mpf('1.5'), \
    f"|psi'| = {mp.nstr(psi1_max, 10)} exceeds the 3/2 the tree carries for this pencil"
assert psi2_max < mpf(50), \
    f"|psi''| unexpectedly large ({mp.nstr(psi2_max, 10)}); the O(M^-3) constant would not close"

print(f"PASS  on [{mp.nstr(SUB_LO,4)}, {mp.nstr(SUB_HI,4)}]: "
      f"max|psi'| = {mp.nstr(psi1_max, 10)} (<= 3/2), "
      f"max|psi''| = {mp.nstr(psi2_max, 10)}")


# --------------------------------------------------------------------------
# 2. The coefficient polynomial, through the defining recurrence.
# --------------------------------------------------------------------------

BCO = [mpf(1), mpf(0), mpf(3)]          # B = 1 + 0t + 3t^2


def coeff_F(M, z):
    r"""`F_M(z) = [t^M] B(t)/D(t,z)` by the recurrence of `eq:F-M-def`."""
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


def G(M, theta):
    r"""`eq:principal-decomposition`'s left side, `\tau^{M+1}F_M(z(\theta))`."""
    val, big = coeff_F(M, zbranch(theta))
    margin = mp.dps - (log(max(big, mpf(1))) / log(10))
    assert margin > 40, \
        f"precision margin collapsed to {mp.nstr(margin,6)} digits at M={M}; raise mp.dps"
    return tau(theta) ** (M + 1) * val, margin


# --------------------------------------------------------------------------
# 3. `eq:local-phase-quantization`: at a zero of G, Phi_M is a half-integer
#    multiple of pi, up to an exponentially small offset.
# --------------------------------------------------------------------------

def zeros_of_G(M, lo, hi, samples=700):
    """Sign-change bisection for the zeros of `theta -> G(M, theta)` on [lo, hi]."""
    out = []
    prev_t = lo
    prev_v = G(M, lo)[0]
    for k in range(1, samples + 1):
        th = lo + (hi - lo) * mpf(k) / mpf(samples)
        v = G(M, th)[0]
        if prev_v == 0:
            out.append(prev_t)
        elif (prev_v < 0) != (v < 0):
            a, b = prev_t, th
            fa = prev_v
            for _ in range(200):
                m_ = (a + b) / 2
                fm = G(M, m_)[0]
                if fm == 0:
                    a = b = m_
                    break
                if (fa < 0) != (fm < 0):
                    b = m_
                else:
                    a, fa = m_, fm
                if b - a < mpf(10) ** (-55):
                    break
            out.append((a + b) / 2)
        prev_t, prev_v = th, v
    return out


M_Q = 40
zs = zeros_of_G(M_Q, SUB_LO, SUB_HI)
assert len(zs) >= 6, f"too few zeros on the subarc at M={M_Q}: {len(zs)}"

worst_off = mpf(0)
for th in zs:
    Phi = (M_Q + 1) * th - psi(th)
    # distance to the nearest (k + 1/2)pi
    kk = mp.floor(Phi / pi - mpf(1) / 2 + mpf(1) / 2)
    off = min(fabs(Phi - (kk + mpf(1) / 2) * pi) for kk in (kk - 1, kk, kk + 1))
    worst_off = max(worst_off, off)

assert worst_off < mpf('1e-6'), \
    f"eq:local-phase-quantization offset {mp.nstr(worst_off,8)} is not exponentially small at M={M_Q}"
print(f"PASS  eq:local-phase-quantization at M={M_Q}: {len(zs)} zeros, "
      f"worst offset from (k+1/2)pi = {mp.nstr(worst_off, 8)}")


# --------------------------------------------------------------------------
# 4. `eq:local-strong-clock`, as a RATE.  The residual after subtracting
#    pi/(M+1) and pi psi'(theta_k)/(M+1)^2 must fall like M^{-3}: a log-log
#    slope, not a spot check.
# --------------------------------------------------------------------------

LADDER = [24, 34, 48, 68, 96, 136]
rows = []
for M in LADDER:
    z_M = zeros_of_G(M, SUB_LO, SUB_HI)
    assert len(z_M) >= 4, f"too few zeros at M={M}: {len(z_M)}"
    worst = mpf(0)
    # use interior consecutive pairs only, so both endpoints stay off the subarc edge
    for a, b in zip(z_M[1:-2], z_M[2:-1]):
        predicted = pi / (M + 1) + pi * diff(psi, a) / (M + 1) ** 2
        worst = max(worst, fabs((b - a) - predicted))
    rows.append((M, worst, len(z_M)))
    print(f"      M = {M:4d}   zeros = {len(z_M):3d}   "
          f"max residual = {mp.nstr(worst, 8)}   "
          f"residual*(M+1)^3 = {mp.nstr(worst * (M + 1) ** 3, 8)}")

# least-squares slope of log(residual) against log(M+1)
xs = [log(mpf(M + 1)) for M, _, _ in rows]
ys = [log(w) for _, w, _ in rows]
n = len(xs)
xbar = sum(xs) / n
ybar = sum(ys) / n
slope = sum((x - xbar) * (y - ybar) for x, y in zip(xs, ys)) / sum((x - xbar) ** 2 for x in xs)

assert slope < mpf('-2.6'), \
    f"eq:local-strong-clock residual decays at slope {mp.nstr(slope,8)}, not the -3 claimed"
assert slope > mpf('-3.6'), \
    f"slope {mp.nstr(slope,8)} is steeper than -3; the psi' correction may be over-fitted"

# and the constant: residual*(M+1)^3 must settle rather than drift
consts = [w * (M + 1) ** 3 for M, w, _ in rows]
spread = max(consts) / min(consts)
assert spread < mpf(6), \
    f"residual*(M+1)^3 spans a factor {mp.nstr(spread,6)} over the ladder; not a constant"

print(f"PASS  eq:local-strong-clock: log-log slope = {mp.nstr(slope, 8)} (target -3), "
      f"constant settles within a factor {mp.nstr(spread, 6)}, "
      f"C_3 ~ {mp.nstr(max(consts), 8)}")


# --------------------------------------------------------------------------
# 5. The psi' correction is load-bearing: drop it and the rate degrades to
#    M^{-2}.  Without this the fit above would be consistent with a weaker law.
# --------------------------------------------------------------------------

rows0 = []
for M in LADDER:
    z_M = zeros_of_G(M, SUB_LO, SUB_HI)
    worst = mpf(0)
    for a, b in zip(z_M[1:-2], z_M[2:-1]):
        worst = max(worst, fabs((b - a) - pi / (M + 1)))
    rows0.append((M, worst))

ys0 = [log(w) for _, w in rows0]
ybar0 = sum(ys0) / n
slope0 = (sum((x - xbar) * (y - ybar0) for x, y in zip(xs, ys0))
          / sum((x - xbar) ** 2 for x in xs))

assert slope0 > mpf('-2.4'), \
    f"dropping the psi' term still gives slope {mp.nstr(slope0,8)}; the correction is not " \
    f"load-bearing in this sweep, so the M^-3 fit above proves less than it appears to"

print(f"PASS  the psi' correction is load-bearing: without it the slope is "
      f"{mp.nstr(slope0, 8)} (an M^-2 law), with it {mp.nstr(slope, 8)}")

print("ALL PASS  check_cubic_strong_clock.py")
