r"""Paper subsection `subsec:strong-clock` (Local phase quantization and strong-clock spacing).

The witness for `cubic_local_strong_clock_closed`: WHICH threshold in `M` actually binds, and
what it is.  A theorem whose hypotheses are never met compiles, passes every axiom guard and
means nothing, so the thresholds are located here rather than asserted.

THREE conditions must hold simultaneously, and they are not the same condition.

  (W)  the WINDOW binders.  `[Phi(a)+delta, Phi(b)-pi-delta]` must contain a zero of `cos`,
       which needs `Phi` to turn by more than `2 pi + 2 delta` -- not `pi + 2 delta`, since a
       shorter window can fall between two consecutive half-integer multiples of `pi`.
  (C0) the VALUE threshold.  `C sigma^M < sin delta`: the error cannot reach the cosine's
       own scale, or the sign changes the count rests on are not there.
  (C1) the DERIVATIVE threshold.  `(M+1) C sigma^M < (sqrt 2 / 2)(M - 1/2)`: the error's
       derivative cannot overcome the phase's, or the zero near a quantization point is not
       unique.

(C1) carries an extra factor of `M` on the left, which looks like it should make it bind later
than (C0).  IT DOES NOT, and that is what this script found: the right-hand side of (C1) grows
too, and by the time the geometric decay has brought `C sigma^M` under `sin delta` the factor
`(sqrt 2 / 2)(M - 1/2)` is already some fifty times larger than `sin delta` -- which more than
absorbs the `(M+1)` on the left.  The two flip at the same `M`.  The prediction was that (C1)
would be strictly later; it is not, at the true conditions.  The Lean proves (C0)
and (C1) through `exists_succ_pow_mul_geometric_le` at the slightly conservative targets
`sin delta / 2` and `1/2`, so both the true conditions and the Lean's own are reported --
the Lean's threshold can only be the larger, and reporting only the true one would understate
what the theorem requires.

Constants are the pencil's own: `Q = (1-t)^3`, `r = 1`, `B = 3t^2+1`, subarc `[1.75, 2.55]`
(clear of the amplitude divisor at `pi/2`), `e = 1/2`, `delta = pi/4`.
"""

from mpmath import mp, mpf, mpc, fabs, re, im, pi, cos, sin, exp, sqrt, ceil

mp.dps = 60

I = mpc(0, 1)

E = mpf('0.5')
A_ARC, B_ARC = mpf('1.75'), mpf('2.55')
DELTA = pi / 4


def tau(t):
    return 1 / (2 * cos((pi - t) / 3))


def tau1(t):
    return -sin((pi - t) / 3) / (6 * cos((pi - t) / 3) ** 2)


def gam(t):
    return tau(t) * exp(I * t)


def gam1(t):
    return exp(I * t) * (tau1(t) + I * tau(t))


def zbranch(t):
    g = gam(t)
    z = -(1 - g) ** 3 / g
    assert fabs(im(z)) < mpf(10) ** (-40), f"z left the reals at {t}"
    return re(z)


def zbranch1(t):
    """`cubicZbranchDeriv`: z as a function of tau alone, by the chain rule."""
    u = tau(t)
    return -2 * (u ** 2 - 1) ** 2 * (u ** 2 + 2) / u ** 5 * tau1(t)


def L(x):
    return 1 / x + 6 * x / (3 * x ** 2 + 1) + 2 / (1 - x) - 2 / (2 * x + 1)


def W(t):
    g = gam(t)
    return g * (3 * g ** 2 + 1) / ((1 - g) ** 2 * (2 * g + 1))


def Wderiv(t):
    return gam1(t) * L(gam(t)) * W(t)


# --------------------------------------------------------------------------
# The constants `cubic_interior_cos_error_C1` builds its `C` from.
# --------------------------------------------------------------------------

taue = tau(E)
SIGMA = taue
Dlo = (1 - taue) ** 2 * (1 / taue ** 2 - 1)
CI = taue * (4 / Dlo)
Qd = 4 / (Dlo / 2) ** 2

N = 4000
grid = [A_ARC + (B_ARC - A_ARC) * mpf(k) / mpf(N) for k in range(N + 1)]
Amin = min(fabs(W(t)) for t in grid)
Wd = max(fabs(Wderiv(t)) for t in grid)
Zs = max(fabs(zbranch1(t)) for t in grid)
Ts = max(fabs(tau1(t)) for t in grid)

KN = 2 * CI * Ts + taue * Zs * Qd
C = max(CI / (2 * Amin), KN / (2 * Amin) + CI * (2 * Wd) / (4 * Amin ** 2))

print(f"      subarc [{mp.nstr(A_ARC,4)}, {mp.nstr(B_ARC,4)}], e = {mp.nstr(E,3)}, "
      f"delta = pi/4")
print(f"      sigma = tau(e) = {mp.nstr(SIGMA,8)}   D_lo = {mp.nstr(Dlo,6)}   "
      f"C_I = {mp.nstr(CI,6)}")
print(f"      A = {mp.nstr(Amin,6)}   W_d = {mp.nstr(Wd,6)}   Z_s = {mp.nstr(Zs,6)}   "
      f"T_s = {mp.nstr(Ts,6)}")
print(f"      K_N = {mp.nstr(KN,6)}   C = {mp.nstr(C,8)}")
assert Amin > 0, "the amplitude floor vanished on the subarc"
assert C > 0


# --------------------------------------------------------------------------
# (W) the window threshold, recomputed here so all three sit side by side.
# --------------------------------------------------------------------------

def psi_diff(lo, hi, samples=20000):
    h = (hi - lo) / mpf(samples)
    total = mpf(0)
    for k in range(samples):
        t = lo + h * (mpf(k) + mpf('0.5'))
        eps = mpf(10) ** (-25)
        total += im((W(t + eps) - W(t - eps)) / (2 * eps) / W(t)) * h
    return total


dpsi = psi_diff(A_ARC, B_ARC)
M_window = None
for M in range(2, 400):
    turn = (mpf(M) + 1) * (B_ARC - A_ARC) - dpsi
    if turn - pi - 2 * DELTA >= pi:
        M_window = M
        break
assert M_window is not None
print(f"\n  (W)  window:      Phi turns by more than 2pi + 2delta from M = {M_window}")


# --------------------------------------------------------------------------
# (C0) and (C1), true conditions and the Lean's own.
# --------------------------------------------------------------------------

def first_M(pred, cap=100000):
    for M in range(2, cap):
        if pred(M):
            return M
    return None


sind = sin(DELTA)
M_C0 = first_M(lambda M: C * SIGMA ** M < sind)
M_C1 = first_M(lambda M: (mpf(M) + 1) * C * SIGMA ** M < sqrt(2) / 2 * (mpf(M) - mpf('0.5')))
M_C0_lean = first_M(lambda M: C * SIGMA ** M <= sind / 2)
M_C1_lean = first_M(lambda M: C * ((mpf(M) + 1) * SIGMA ** M) <= mpf('0.5'))
for nm, v in (("C0", M_C0), ("C1", M_C1), ("C0 lean", M_C0_lean), ("C1 lean", M_C1_lean)):
    assert v is not None, f"threshold {nm} never reached"

print(f"  (C0) value:       C sigma^M < sin delta          from M = {M_C0}"
      f"   (Lean's C sigma^M <= sin delta / 2: M = {M_C0_lean})")
print(f"  (C1) derivative:  (M+1) C sigma^M < (r2/2)(M-1/2) from M = {M_C1}"
      f"   (Lean's (M+1) C sigma^M <= 1/2:     M = {M_C1_lean})")

assert M_C1 >= M_C0, \
    f"the C1 threshold {M_C1} is BELOW the C0 threshold {M_C0}, which contradicts the extra " \
    f"factor of M on its left-hand side"
assert M_C1_lean >= M_C0_lean, "the same, at the Lean's own conservative targets"

M0 = max(M_window, M_C1_lean, 2)
print(f"\n      the binding threshold is "
      f"{'(C1), the derivative' if M_C1_lean >= M_window else '(W), the window'}; "
      f"M_0 = max(W, C0, C1, 2) = {M0}")

if M_C1 > M_C0:
    print(f"PASS  (C1) binds strictly later than (C0): {M_C1} against {M_C0}, as predicted")
else:
    rhs = sqrt(2) / 2 * (mpf(M_C1) - mpf('0.5'))
    print(f"PASS  (C1) and (C0) bind at the SAME M = {M_C1}: the prediction that (C1) would "
          f"be strictly later is REFUTED. At that M the right side of (C1) is "
          f"{mp.nstr(rhs, 6)} against sin delta = {mp.nstr(sind, 6)}, a factor "
          f"{mp.nstr(rhs / sind, 5)}, which more than absorbs the M+1 = {M_C1 + 1} on its "
          f"left. The gap that does appear -- {M_C1_lean} against {M_C0_lean} -- is between "
          f"the LEAN'S targets sin delta / 2 and 1/2, and is an artifact of the slack chosen "
          f"in the proof rather than of the mathematics.")

# and a witness: every condition genuinely holds at the threshold
Mw = M0
turn = (mpf(Mw) + 1) * (B_ARC - A_ARC) - dpsi
lo = (mpf(Mw) + 1) * A_ARC + DELTA
hi = (mpf(Mw) + 1) * B_ARC - dpsi - pi - DELTA
n = ceil((lo - pi / 2) / pi)
u0 = pi / 2 + n * pi
assert lo <= u0 <= hi, "no admissible u0 at the threshold"
assert fabs(cos(u0)) < mpf(10) ** (-40)
assert C * SIGMA ** Mw < sind
assert (mpf(Mw) + 1) * C * SIGMA ** Mw < sqrt(2) / 2 * (mpf(Mw) - mpf('0.5'))
print(f"\nPASS  witness at M = {Mw}: u0 = {mp.nstr(u0,10)} with cos u0 = "
      f"{mp.nstr(cos(u0),3)}, C sigma^M = {mp.nstr(C * SIGMA ** Mw, 6)} < sin delta = "
      f"{mp.nstr(sind,6)}, and (M+1) C sigma^M = "
      f"{mp.nstr((mpf(Mw)+1) * C * SIGMA ** Mw, 6)} < "
      f"{mp.nstr(sqrt(2)/2*(mpf(Mw)-mpf('0.5')), 6)}")
print("\nALL PASS  check_cubic_strong_clock_threshold.py")
