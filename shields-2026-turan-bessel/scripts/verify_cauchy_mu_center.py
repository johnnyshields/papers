#!/usr/bin/env python3
"""Paper section `subsec:large-argument-deformation-wall` (Large argument and the deformation wall), sec:phase,
lem:large-argument-limit:
the Cauchy estimate in the order variable, evaluated at the center mu = nu.

A circle of fixed positive radius in the order variable cannot be chosen uniformly
for every mu in the interior of the closed disc K, since dist(mu, boundary K) -> 0
near the boundary.  The lem:large-argument-limit proof does not need that: the estimate is required
at mu = nu, the center of K, and only there, because G_nu = -d^2/dnu^2 log I_nu and
P_nu = d/dnu (Theta_z log I_nu) are evaluated at the prescribed order.  This script
checks

  (1) with K = closed disc of radius 1 about nu and the Cauchy circle
      |mu - nu| = 1/2 (fixed, well inside K), the remainder
          R(mu, w) = log E_mu(w) + (4 mu^2 - 1)/(8 w),
          E_mu(w) = (2 pi w)^{1/2} e^{-w} I_mu(w),
      satisfies |d^j/dmu^j R(nu, w)| = O(w^{-2}) for j = 0, 1, 2, i.e.
      w^2 |d^j R| stays bounded along a ladder in w;

  (2) two independent routes to d^j/dmu^j R(nu, w) agree: the Cauchy contour
      integral over that circle, and direct numerical differentiation;

  (3) the resulting asymptotics of the paper hold numerically:
          z G_nu -> 1,  1 + P_nu -> 1,
          H^{(kappa)}_nu - ((2 kappa - 1) z - kappa (1 + 2 nu)) -> 0,
          D^{(kappa)}_nu(z) -> 2 (kappa - 1);

  (4) the end-of-section-5 lower bound chain
          Delta_1(a) lambda = 2 (a psi_1(a) - 1) lambda / (a^3 Gamma(a)^4)
                            > lambda / (a^4 Gamma(a)^4)
      holds for a > 0 (equivalently a psi_1(a) - 1 > 1/(2a));

  (5) the fixed-a first-negative-degree argument of thm:critical-scaling, in the form
      the monotonicity identity
      Delta^(kappa) = Delta^(1) + (kappa-1) g A Z Z_Theta supplies: with
      c_n = [lambda^n] g A Z Z_Theta > 0 and Delta_n^(1) > 0, degree n stays
      positive exactly while 1 - kappa < Delta_n^(1)/c_n, so the admissible window
      min_{n<=N} Delta_n^(1)/c_n is positive for every N and decreasing in N.

Every displayed quantity is asserted, not printed only.
"""

from mpmath import mp, mpf, mpc, besseli, log, exp, pi, sqrt, psi, gamma, cos, sin

mp.dps = 40

NU = mpf("0.7")          # prescribed order; center of K
RAD_K = mpf(1)           # radius of K
R_CIRC = RAD_K / 2       # Cauchy circle radius, fixed and inside K
KAPPA = mpf("0.6")       # a kappa < 1, where the limit 2(kappa-1) < 0


def E(mu, w):
    return sqrt(2 * pi * w) * exp(-w) * besseli(mu, w)


def R(mu, w):
    """Remainder in log E_mu(w) = -(4 mu^2 - 1)/(8 w) + R(mu, w)."""
    return log(E(mu, w)) + (4 * mu**2 - 1) / (8 * w)


def dR_cauchy(j, w, n=64):
    """j-th mu-derivative of R at mu = NU by Cauchy's integral over |mu-NU|=R_CIRC."""
    total = mpc(0)
    for k in range(n):
        th = 2 * pi * k / n
        mu = NU + R_CIRC * mpc(cos(th), sin(th))
        # d^j/dmu^j f(NU) = j!/(2 pi i) * contour integral f(mu)/(mu-NU)^{j+1} dmu
        # dmu = i * R_CIRC * e^{i th} dth ; the i cancels the 1/i.
        total += R(mu, w) / (R_CIRC * mpc(cos(th), sin(th))) ** j
    return mp.factorial(j) * total / n


def dR_direct(j, w):
    if j == 0:
        return R(NU, w)
    return mp.diff(lambda m: R(m, w), NU, j)


def L(mu, z):
    return log(besseli(mu, z))


def bessel_quantities(z, kappa):
    g = psi(1, NU + 1)
    G = -mp.diff(lambda m: L(m, z), NU, 2)
    Lp = mp.diff(lambda x: L(NU, x), z)
    Lpp = mp.diff(lambda x: L(NU, x), z, 2)
    theta1 = z * Lp
    theta2 = z * Lp + z**2 * Lpp
    P = z * mp.diff(lambda m, x: L(m, x), (NU, z), (1, 1))
    H = 2 * kappa * (theta1 - NU) - theta2
    D = G * (H + 4 / g) - (1 + P) ** 2
    return G, P, H, D


print("== (1)+(2) Cauchy estimate at the center mu = nu =", NU)
print("   K = disc(nu, %s), Cauchy circle radius %s\n" % (RAD_K, R_CIRC))
print("%8s %3s %22s %22s %14s" % ("w", "j", "d^j R (Cauchy)", "d^j R (direct)", "w^2 |d^j R|"))
scaled = {0: [], 1: [], 2: []}
for w in [mpf(50), mpf(200), mpf(800), mpf(3200)]:
    for j in (0, 1, 2):
        a_c = dR_cauchy(j, w)
        a_d = dR_direct(j, w)
        assert abs(a_c - a_d) < mpf("1e-12") * max(1, abs(a_d)) + mpf("1e-25"), (
            "routes disagree at w=%s j=%s: %s vs %s" % (w, j, a_c, a_d))
        s = w**2 * abs(a_c)
        scaled[j].append(s)
        print("%8s %3d %22s %22s %14s" % (w, j, mp.nstr(a_c.real, 10), mp.nstr(a_d, 10), mp.nstr(s, 8)))

for j in (0, 1, 2):
    lo, hi = min(scaled[j]), max(scaled[j])
    # bounded: the w^2-scaled derivative varies by a bounded factor, no growth in w
    assert hi < 10 * lo + mpf("1e-6"), "w^2 |d^%d R| not bounded: %s" % (j, scaled[j])
    assert scaled[j][-1] < 2 * scaled[j][0] + mpf("1e-6"), (
        "w^2 |d^%d R| growing in w: %s" % (j, scaled[j]))
print("\n   d^j/dmu^j R(nu, w) = O(w^-2) for j = 0,1,2: mu-derivatives preserve the order. OK\n")

print("== (3) resulting large-z asymptotics at nu = %s, kappa = %s\n" % (NU, KAPPA))
print("%8s %14s %14s %18s %16s" % ("z", "z*G_nu", "1+P_nu", "H-((2k-1)z-k(1+2nu))", "D^(kappa)"))
prev_err_D = None
for z in [mpf(40), mpf(160), mpf(640), mpf(2560)]:
    G, P, H, D = bessel_quantities(z, KAPPA)
    Hres = H - ((2 * KAPPA - 1) * z - KAPPA * (1 + 2 * NU))
    print("%8s %14s %14s %18s %16s" % (z, mp.nstr(z * G, 10), mp.nstr(1 + P, 10),
                                       mp.nstr(Hres, 10), mp.nstr(D, 10)))
    assert abs(z * G - 1) < 3 / z, "z G_nu -> 1 fails at z=%s: %s" % (z, z * G)
    assert abs(P) < 3 / z, "P_nu = O(1/z) fails at z=%s: %s" % (z, P)
    assert abs(Hres) * z < 20, "H residual not O(1/z) at z=%s: %s" % (z, Hres)
    err_D = abs(D - 2 * (KAPPA - 1))
    assert err_D * z < 40, "D^(kappa) -> 2(kappa-1) too slowly at z=%s: %s" % (z, err_D)
    if prev_err_D is not None:
        assert err_D < prev_err_D, "D error not decreasing at z=%s" % z
    prev_err_D = err_D
assert D < 0, "D^(kappa) limit must be negative for kappa < 1: %s" % D
print("\n   D^(kappa) -> 2(kappa-1) = %s, negative for kappa < 1. OK\n"
      % mp.nstr(2 * (KAPPA - 1), 10))

print("== (4) lower bound chain closing sec:endpoint\n")
print("%10s %22s %22s" % ("a", "Delta_1(a)", "1/(a^4 Gamma(a)^4)"))
for a in [mpf("0.01"), mpf("0.1"), mpf("0.5"), mpf(1), mpf(2), mpf(5), mpf(20)]:
    g = psi(1, a)
    d1 = 2 * (a * g - 1) / (a**3 * gamma(a) ** 4)
    rhs = 1 / (a**4 * gamma(a) ** 4)
    assert a * g - 1 > 1 / (2 * a), "a psi_1(a) - 1 > 1/(2a) fails at a=%s" % a
    assert d1 > rhs, "Delta_1 lower bound fails at a=%s" % a
    print("%10s %22s %22s" % (a, mp.nstr(d1, 12), mp.nstr(rhs, 12)))
print("\n   Delta_1(a) > 1/(a^4 Gamma(a)^4) for every tested a > 0. OK")

print("\n== (5) first-negative-degree argument of the remark, at a fixed a\n")
# Delta^(kappa) = Delta^(1) + (kappa-1) g A Z Z_Theta.  With c_n = [lam^n] g A Z Z_Theta > 0
# and Delta_n^(1) > 0, degree n stays positive iff 1 - kappa < Delta_n^(1)/c_n.  The
# threshold min_{n<=N} Delta_n^(1)/c_n is therefore positive for every N, which is the
# fixed-a statement; it decreases in N, so the first negative degree -> infinity.
NTRUNC = 16


def series(a, kind):
    out = []
    for k in range(NTRUNC + 1):
        base = 1 / (mp.factorial(k) * gamma(a + k))
        ps = psi(0, a + k)
        if kind == "Z":
            out.append(base)
        elif kind == "Za":
            out.append(-ps * base)
        elif kind == "Zaa":
            out.append((ps**2 - psi(1, a + k)) * base)
        elif kind == "Zt":
            out.append(k * base)
        elif kind == "Ztt":
            out.append(k**2 * base)
        elif kind == "Zat":
            out.append(-k * ps * base)
    return out


def mul(u, v):
    out = [mpf(0)] * (NTRUNC + 1)
    for i, ui in enumerate(u):
        for j, vj in enumerate(v):
            if i + j <= NTRUNC:
                out[i + j] += ui * vj
    return out


def add(*ss):
    out = [mpf(0)] * (NTRUNC + 1)
    for s in ss:
        for i, si in enumerate(s):
            out[i] += si
    return out


def scal(c, s):
    return [c * si for si in s]


for a in [mpf("0.3"), mpf(1), mpf(3)]:
    g = psi(1, a)
    Z, Za, Zaa = series(a, "Z"), series(a, "Za"), series(a, "Zaa")
    Zt, Ztt, Zat = series(a, "Zt"), series(a, "Ztt"), series(a, "Zat")
    A = add(mul(Za, Za), scal(-1, mul(Z, Zaa)))
    B = add(mul(Z, Z), mul(Z, Zat), scal(-1, mul(Za, Zt)))
    C = add(mul(Z, Z), scal(g, add(mul(Z, Zt), scal(-1, mul(Z, Ztt)), mul(Zt, Zt))))
    D1 = add(mul(A, C), scal(-g, mul(B, B)))          # Delta^(1)
    Cc = scal(g, mul(A, mul(Z, Zt)))                  # g A Z Z_Theta
    assert abs(D1[0]) < mpf("1e-30"), "Delta^(1) constant term must vanish: %s" % D1[0]
    closed_D1 = 2 * (a * g - 1) / (a**3 * gamma(a) ** 4)
    assert abs(D1[1] - closed_D1) < mpf("1e-25") * abs(closed_D1), (
        "Delta_1 disagrees with closed form at a=%s: %s vs %s" % (a, D1[1], closed_D1))
    ratios = []
    for n in range(1, NTRUNC + 1):
        assert D1[n] > 0, "Delta_%d^(1) <= 0 at a=%s" % (n, a)
        assert Cc[n] > 0, "[lam^%d] g A Z Z_Theta <= 0 at a=%s" % (n, a)
        ratios.append(D1[n] / Cc[n])
    thresholds = [min(ratios[:N]) for N in range(1, NTRUNC + 1)]
    for N in range(1, NTRUNC + 1):
        assert thresholds[N - 1] > 0, "threshold at N=%d not positive (a=%s)" % (N, a)
        if N > 1:
            assert thresholds[N - 1] <= thresholds[N - 2], "threshold not monotone (a=%s)" % a
    print("a = %-5s  1-kappa admissible for degrees <= N:  N=1: %s   N=4: %s   N=%d: %s"
          % (a, mp.nstr(thresholds[0], 8), mp.nstr(thresholds[3], 8),
             NTRUNC, mp.nstr(thresholds[-1], 8)))
print("\n   Positive threshold for every N, decreasing in N: at each fixed a the first")
print("   negative degree exceeds N once kappa < 1 is close enough to 1. OK")

print("\nALL PASS: verify_cauchy_mu_center")
