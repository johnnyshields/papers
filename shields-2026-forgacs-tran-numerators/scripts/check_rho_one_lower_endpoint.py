"""The lower endpoint of the viewing arc at a SIMPLE smallest zero (rho = 1).

Paper: `sec:geometry`, `thm:FT-geometry`, `eq:ab-def`;
`lem:principal-endpoint-regularity` (the endpoint regularity the branch collar
consumes).

At a repeated smallest zero (rho >= 2) the branch radius runs into that zero, and
the collar is written against `tau(0) = a_i` with slope `-a_i cot(pi/rho)`.  This
script checks the rho = 1 picture, which is a DIFFERENT point and a different
slope:

  R1  tau(theta) -> L with a_i < L, so `a_i` is not the endpoint value;
  R2  L is a zero of Sigma(s) = sum_k s/(a_k - s) + r, i.e. of E = XQ' - rQ;
  R3  (tau(theta) - L)/theta -> 0 and (tau(theta) - L)/theta^2 -> finite nonzero,
      so the radius arrives with slope ZERO, not with the rho >= 2 slope;
  R4  gamma'(0+) = 0 + iL is nonzero, and the rho >= 2 formula does not extend
      to rho = 1 (cot(pi/1) is a pole);
  R5  L misses every zero of Q, so the endpoint is not a collision with a root;
  R6  Sigma'(L) > 0, so the critical point is simple;
  R7  f''(L) < 0, by numerical differentiation AND by the closed form
      Sigma'(L) Q(L) / L^(r+1) -- two mechanisms, because this sign is what
      decides which arc of the level set the branch runs along;
  R8  z(theta) > z_0 and z is increasing, the other half of that decision.
"""

import math

import mpmath as mp

mp.mp.dps = 40


def branch_sum(a, tau, theta):
    """sum_k arg(gamma - a_k) with gamma = tau e^{i theta}."""
    g = tau * mp.exp(mp.mpc(0, 1) * theta)
    return sum(mp.arg(g - ak) for ak in a)


def ft_tau(a, r, l, theta):
    """Solve sum_k arg(gamma - a_k) = r theta + l pi for tau > 0."""
    target = r * theta + l * mp.pi
    f = lambda t: branch_sum(a, t, theta) - target
    lo, hi = mp.mpf("1e-12"), mp.mpf(1)
    while f(hi) > 0:
        hi *= 2
        assert hi < mp.mpf("1e6"), "no bracket above"
    while f(lo) < 0:
        lo /= 2
        assert lo > mp.mpf("1e-30"), "no bracket below"
    return mp.findroot(f, (lo, hi), solver="bisect", tol=mp.mpf("1e-35"),
                       maxsteps=400)


def sigma(a, r, s):
    return sum(s / (ak - s) for ak in a) + r


def sigma_deriv(a, s):
    return sum(ak / (ak - s) ** 2 for ak in a)


A = [mp.mpf(1), mp.mpf(2), mp.mpf(4)]
R, N = 1, 3
L_INDEX = N - 1

# --- R2/R6 first: locate L as the first positive zero of Sigma. -------------
L = mp.findroot(lambda s: sigma(A, R, s), (A[0] + mp.mpf("1e-9"), A[1] - mp.mpf("1e-9")),
                solver="bisect", tol=mp.mpf("1e-60"))
assert abs(sigma(A, R, L)) < mp.mpf("1e-30"), f"R2 Sigma(L) = {sigma(A, R, L)}"
assert A[0] < L < A[1], f"R2 L = {L} not in the first gap"
assert sigma_deriv(A, L) > 0, "R6 Sigma'(L) <= 0"
print(f"R2/R6  L = {mp.nstr(L, 20)}, Sigma(L) = {mp.nstr(sigma(A, R, L), 5)}, "
      f"Sigma'(L) = {mp.nstr(sigma_deriv(A, L), 10)} > 0")

# --- R1: the branch radius tends to L, and NOT to the smallest zero. --------
thetas = [mp.mpf(2) ** (-k) for k in range(4, 13)]
taus = [ft_tau(A, R, L_INDEX, th) for th in thetas]
assert abs(taus[-1] - L) < mp.mpf("1e-6"), f"R1 tau({thetas[-1]}) = {taus[-1]} vs L = {L}"
jump = L - A[0]
assert jump > mp.mpf("0.37"), f"R1 endpoint jump {jump} too small to be visible"
print(f"R1     tau -> L: |tau(2^-12) - L| = {mp.nstr(abs(taus[-1] - L), 5)}; "
      f"a_i = {A[0]}, L - a_i = {mp.nstr(jump, 10)} > 0")

# --- R3: first-order slope 0, second-order coefficient finite and nonzero. --
first = [(t - L) / th for t, th in zip(taus, thetas)]
second = [(t - L) / th ** 2 for t, th in zip(taus, thetas)]
for k in range(1, len(first)):
    assert abs(first[k]) < abs(first[k - 1]), "R3 first-order ratio not decreasing"
assert abs(first[-1]) < mp.mpf("1e-3"), f"R3 (tau-L)/theta = {first[-1]} does not vanish"
c2 = second[-1]
assert abs(c2 - second[-2]) < mp.mpf("1e-4"), "R3 second-order ratio not converging"
assert abs(c2) > mp.mpf("0.1"), f"R3 second-order coefficient {c2} degenerate"
print(f"R3     (tau-L)/theta  = {mp.nstr(first[-1], 5)} -> 0;  "
      f"(tau-L)/theta^2 = {mp.nstr(c2, 10)} (finite, nonzero)")

# --- R4: gamma'(0+) = tau'(0) + i tau(0) = 0 + iL. --------------------------
# gamma(theta) = tau(theta) e^{i theta}; the difference quotient at 0 with the
# endpoint value L supplied.
def gamma(th):
    return ft_tau(A, R, L_INDEX, th) * mp.exp(mp.mpc(0, 1) * th)


q = [(gamma(th) - L) / th for th in thetas]
# the error is first order in theta, so the check is on the RATE, not on a fixed
# tolerance: a fixed one would only be testing which theta the loop stopped at.
rate = [abs(qq - mp.mpc(0, 1) * L) / th for qq, th in zip(q, thetas)]
for k in range(1, len(rate)):
    assert rate[k] < 2 * rate[k - 1], "R4 error not first order in theta"
assert rate[-1] < mp.mpf(2), f"R4 error rate {rate[-1]} not bounded"
assert abs(q[-1] - mp.mpc(0, 1) * L) < 2 * thetas[-1], f"R4 quotient {q[-1]} vs iL"
assert abs(mp.mpc(0, 1) * L) > 0, "R4 gamma'(0+) = 0"
print(f"R4     (gamma(theta) - L)/theta = {mp.nstr(q[-1], 8)} -> iL = {mp.nstr(mp.mpc(0,1)*L, 8)}; "
      f"|error|/theta = {mp.nstr(rate[-1], 5)}")

# the rho >= 2 slope formula is a pole at rho = 1, so it does not extend.
assert abs(math.sin(math.pi / 2)) > 0.5, "R4 cot(pi/2) sanity"
assert abs(math.sin(math.pi / 1)) < 1e-15, "R4 sin(pi/rho) does not vanish at rho = 1"
print("R4     sin(pi/rho) = 0 at rho = 1: the rho >= 2 slope -a_i cot(pi/rho) has a pole there")

# --- R5: L is not a zero of Q, so the endpoint is not a root collision. -----
clear = min(abs(L - ak) for ak in A)
assert clear > mp.mpf("0.3"), f"R5 clearance {clear} too small"
print(f"R5     min_k |L - a_k| = {mp.nstr(clear, 10)} > 0: the endpoint misses every zero of Q")

# --- the rho >= 2 comparison, for contrast: a repeated smallest zero. -------
A2 = [mp.mpf(1), mp.mpf(1), mp.mpf(4)]
tau2 = [ft_tau(A2, R, L_INDEX, th) for th in thetas]
assert abs(tau2[-1] - A2[0]) < mp.mpf("1e-3"), f"rho=2 tau -> {tau2[-1]}, expected a_i = 1"
slope2 = (tau2[-1] - A2[0]) / thetas[-1]
assert abs(slope2) < mp.mpf("1e-2"), f"rho=2 slope {slope2}, expected -a_i cot(pi/2) = 0"
print(f"contrast  rho = 2: tau -> a_i = {A2[0]} with slope {mp.nstr(slope2, 5)} "
      "(-a_i cot(pi/2) = 0)")

# --- R7: the Morse coefficient is negative, checked two ways. --------------
def Qreal(a, s):
    out = mp.mpf(1)
    for ak in a:
        out *= ak - s
    return out


def fiber(a, r, s):
    return -Qreal(a, s) / s ** r


f2_numeric = mp.diff(lambda s: fiber(A, R, s), L, 2)
f2_closed = sigma_deriv(A, L) * Qreal(A, L) / L ** (R + 1)
assert abs(f2_numeric - f2_closed) < mp.mpf("1e-20"), (
    f"R7 f''(L): numeric {f2_numeric} vs closed form {f2_closed}")
assert f2_numeric < 0, f"R7 f''(L) = {f2_numeric} is not negative"
assert Qreal(A, L) < 0, f"R7 Q(L) = {Qreal(A, L)} is not negative"
assert abs(mp.diff(lambda s: fiber(A, R, s), L, 1)) < mp.mpf("1e-25"), "R7 f'(L) != 0"
print(f"R7     f'(L) = 0, f''(L) = {mp.nstr(f2_numeric, 10)} < 0; closed form agrees to "
      f"{mp.nstr(abs(f2_numeric - f2_closed), 3)}; Q(L) = {mp.nstr(Qreal(A, L), 8)} < 0")

# --- R8: the branch value exceeds its one-sided limit, and increases. -------
def fiber_c(a, r, w):
    """The fiber map at a COMPLEX point -- the branch value is f(gamma), not f(tau)."""
    num = mp.mpc(1)
    for ak in a:
        num *= ak - w
    return -num / w ** r


z0 = fiber(A, R, L)
zc = [fiber_c(A, R, gamma(th)) for th in thetas]
# the branch is a level set of Im f, so the value is real there
for th, w in zip(thetas, zc):
    assert abs(mp.im(w)) < mp.mpf("1e-20"), f"R8 Im f(gamma({th})) = {mp.im(w)} not real"
zs = [mp.re(w) for w in zc]
for th, zz in zip(thetas, zs):
    assert zz > z0, f"R8 z({th}) = {zz} not above z_0 = {z0}"
for k in range(1, len(zs)):
    assert zs[k] < zs[k - 1], "R8 z is not increasing in theta"
assert z0 > 0, f"R8 z_0 = {z0} is not positive"
print(f"R8     z_0 = {mp.nstr(z0, 10)} > 0 and z(theta) > z_0, increasing: "
      f"z(2^-4) = {mp.nstr(zs[0], 10)} > z(2^-12) = {mp.nstr(zs[-1], 10)} > z_0")
print("       so kappa = f''(L)/2 < 0 and z - z_0 > 0: kappa H^2 > 0 forces H^2 < 0")

print("check_rho_one_lower_endpoint.py: PASS")
