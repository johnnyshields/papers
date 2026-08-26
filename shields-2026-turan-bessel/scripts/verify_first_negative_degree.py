#!/usr/bin/env python3
"""Paper section `sec:scaling` (Critical wall fan and equivalence of ensembles), sec:scaling,
where thm:critical-scaling of section `sec:main` is proved; eq. (first-negative-asymptotic):
first-negative-degree behavior of Delta_n^{(kappa)}(a) for kappa < 1.

The theorem fixes a > 0 and gives N_a(kappa) ~ c(a)/(1-kappa) as kappa -> 1, so in
particular no bounded set of degrees detects every kappa < 1.  The rate itself is
checked in verify_critical_scaling.py; what is separated here are the two
quantifiers behind the qualitative statement:

  (Q1) fixed a, kappa -> 1   : n_min(a,kappa) -> infinity      [what the theorem gives]
  (Q2) fixed kappa < 1, all a: is n_min(.,kappa) unbounded in a? [not claimed by the
       paper; recorded as context for why the remark fixes a first]

Route 1 (paper): Delta_n^{(kappa)} = sum_{k} S_k S_{n-k} (alpha_k gamma_{n-k} - g beta_k beta_{n-k}),
  equivalently (1/2) sum_k S_k S_{n-k} MD(M_k, M_{n-k}), from thm:coefficients.
Route 2 (independent): Cauchy convolution of the termwise Maclaurin coefficients of
  Z, Z_a, Z_aa, Z_Theta, Z_ThetaTheta, Z_aTheta, then A*C_kappa - g*B^2 directly.
  Uses no Chu-Vandermonde identity.

All arithmetic in mpmath at 60 digits.
"""

import mpmath as mp

mp.mp.dps = 60


# ----------------------------------------------------------------- paper route
def S(a, m):
    """S_m = (2a+m-1)_m / (m! Gamma(a+m)^2)."""
    return mp.rf(2 * a + m - 1, m) / (mp.factorial(m) * mp.gamma(a + m) ** 2)


def alpha(a, m):
    return mp.polygamma(1, a + m)


def beta(a, m):
    if m == 0:
        return mp.mpf(1)
    return (2 * a + m - 2) / (2 * (a + m - 1))


def c(a, m, kappa):
    if m == 0:
        return mp.mpf(0)
    if m == 1:
        return (kappa - 1) / 2
    return m * ((kappa - 1) * (2 * a + 2 * m - 3) + m - 1) / (2 * (2 * a + 2 * m - 3))


def gamma_(a, m, kappa):
    return 1 + mp.polygamma(1, a) * c(a, m, kappa)


def delta_paper(a, n, kappa):
    """[lambda^n] (A C_kappa - g B^2) via thm:coefficients."""
    g = mp.polygamma(1, a)
    tot = mp.mpf(0)
    for k in range(n + 1):
        j = n - k
        tot += S(a, k) * S(a, j) * (
            alpha(a, k) * gamma_(a, j, kappa) - g * beta(a, k) * beta(a, j)
        )
    return tot


def delta_MD(a, n, kappa):
    """Same coefficient via the mixed-determinant form eq:Delta-n-MD."""
    g = mp.polygamma(1, a)

    def M(m):
        return (alpha(a, m), mp.sqrt(g) * beta(a, m), gamma_(a, m, kappa))

    def MD(X, Y):
        return X[0] * Y[2] + X[2] * Y[0] - 2 * X[1] * Y[1]

    return sum(S(a, k) * S(a, n - k) * MD(M(k), M(n - k)) for k in range(n + 1)) / 2


# ------------------------------------------------------ independent route
def series_coeffs(a, N):
    """Termwise Maclaurin coefficients (degree 0..N) of Z and its derivatives."""
    z, za, zaa, zt, ztt, zat = [], [], [], [], [], []
    for k in range(N + 1):
        base = 1 / (mp.factorial(k) * mp.gamma(a + k))
        p0 = mp.polygamma(0, a + k)
        p1 = mp.polygamma(1, a + k)
        z.append(base)
        za.append(-p0 * base)
        zaa.append((p0 ** 2 - p1) * base)
        zt.append(k * base)
        ztt.append(k * k * base)
        zat.append(-k * p0 * base)
    return z, za, zaa, zt, ztt, zat


def conv(u, v, n):
    return sum(u[k] * v[n - k] for k in range(n + 1))


def delta_direct(a, n, kappa):
    """[lambda^n](A C_kappa - g B^2) from the defining series alone."""
    g = mp.polygamma(1, a)
    z, za, zaa, zt, ztt, zat = series_coeffs(a, n)
    A = [conv(za, za, m) - conv(z, zaa, m) for m in range(n + 1)]
    B = [conv(z, z, m) + conv(z, zat, m) - conv(za, zt, m) for m in range(n + 1)]
    C = [
        conv(z, z, m)
        + g * (kappa * conv(z, zt, m) - conv(z, ztt, m) + conv(zt, zt, m))
        for m in range(n + 1)
    ]
    return conv(A, C, n) - g * conv(B, B, n)


# --------------------------------------------------------------- cross-check
print("=== cross-check: three routes agree on Delta_n^{(kappa)} ===")
for a in [mp.mpf("0.2"), mp.mpf("0.9"), mp.mpf(3), mp.mpf(12)]:
    for kappa in [mp.mpf("0.4"), mp.mpf("0.95"), mp.mpf(1), mp.mpf("1.3")]:
        for n in range(1, 7):
            v1, v2, v3 = (
                delta_paper(a, n, kappa),
                delta_MD(a, n, kappa),
                delta_direct(a, n, kappa),
            )
            scale = max(abs(v1), mp.mpf(1))
            assert abs(v1 - v2) / scale < mp.mpf("1e-45"), (a, kappa, n, "paper vs MD")
            assert abs(v1 - v3) / scale < mp.mpf("1e-45"), (a, kappa, n, "paper vs direct")
print("  all three routes agree to 45 digits over a in {0.2,0.9,3,12},")
print("  kappa in {0.4,0.95,1,1.3}, n = 1..6.")


# ---------------------------------------------- Delta_1 sign, closed form
# Delta_1^{(kappa)} = 2/(a^3 Gamma(a)^4) * [ (kappa-1)/2 * (a g)^2 + a g - 1 ],
# so its sign is that of P(u) = -(eps/2) u^2 + u - 1 with u = a*psi_1(a) > 1,
# eps = 1 - kappa.  P has real roots iff eps <= 1/2, i.e. kappa >= 1/2.
print()
print("=== Delta_1^{(kappa)} closed form and its sign ===")
for a in [mp.mpf("0.05"), mp.mpf("0.5"), mp.mpf(1), mp.mpf(4), mp.mpf(30)]:
    for kappa in [mp.mpf("0.4"), mp.mpf("0.49"), mp.mpf("0.51"), mp.mpf("0.9")]:
        g = mp.polygamma(1, a)
        u = a * g
        closed = 2 / (a ** 3 * mp.gamma(a) ** 4) * ((kappa - 1) / 2 * u ** 2 + u - 1)
        assert abs(closed - delta_paper(a, 1, kappa)) / max(abs(closed), mp.mpf(1)) < mp.mpf("1e-45")
        print(f"  a={float(a):8.3f} kappa={float(kappa):5.2f}  ag={float(u):10.5f}"
              f"  Delta_1={mp.nstr(closed, 6):>14}  sign={'+' if closed > 0 else '-'}")

print()
print("  claim: for kappa < 1/2, Delta_1^{(kappa)}(a) < 0 for EVERY a > 0.")
for kappa in [mp.mpf("0.0"), mp.mpf("0.25"), mp.mpf("0.45"), mp.mpf("0.499")]:
    worst = None
    for e in range(-4, 5):            # a from 1e-4 to 1e4, log grid
        for f in range(0, 10):
            a = mp.mpf(10) ** (e + mp.mpf(f) / 10)
            d1 = delta_paper(a, 1, kappa)
            assert d1 < 0, (kappa, a, d1)
            u = a * mp.polygamma(1, a)
            p = -(1 - kappa) / 2 * u ** 2 + u - 1
            if worst is None or p > worst[1]:
                worst = (a, p)
    print(f"    kappa={float(kappa):6.3f}: Delta_1 < 0 on the whole grid; "
          f"max of P(ag) = {mp.nstr(worst[1], 5)} at a={float(worst[0]):.4g}  (< 0)")
print("  => at kappa < 1/2 the single degree n=1 witnesses failure at every a>0,")
print("     so 'no single degree can serve every a' is FALSE at fixed kappa < 1/2.")


# --------------------------- n_min(a,kappa): least n with Delta_n < 0
def n_min(a, kappa, nmax=60):
    for n in range(1, nmax + 1):
        if delta_paper(a, n, kappa) < 0:
            return n
    return None


print()
print("=== lem:Delta-n-noneq2, the necessity part of thm:two-parameter-coeff, cor:eventual-negative-tail ===")
NCAP = 60
AGRID = [mp.mpf("0.05"), mp.mpf("0.3"), mp.mpf("0.5"), mp.mpf(1), mp.mpf(4), mp.mpf(30)]


def delta_and_q(a, N):
    """Delta_n and q_n = [lambda^n] Q for n <= N, from the thm:coefficients entries.

    Delta_n^(kappa) = Delta_n + (kappa-1) q_n, because c_m^(kappa) = c_m + (kappa-1)m/2
    for every m >= 0; that is eq. (affine-two-param) on the tau = 1 slice, and it is
    cross-checked against delta_paper below rather than assumed.
    """
    g = mp.polygamma(1, a)
    Ss = [S(a, k) for k in range(N + 1)]
    al = [alpha(a, k) for k in range(N + 1)]
    be = [beta(a, k) for k in range(N + 1)]
    ga = [gamma_(a, k, mp.mpf(1)) for k in range(N + 1)]
    d, q = [mp.mpf(0)]*(N + 1), [mp.mpf(0)]*(N + 1)
    for n in range(N + 1):
        d[n] = mp.fsum(Ss[k]*Ss[n-k]*(al[k]*ga[n-k] - g*be[k]*be[n-k])
                       for k in range(n + 1))
        q[n] = g/2*mp.fsum(Ss[k]*Ss[n-k]*al[k]*(n - k) for k in range(n + 1))
    return d, q


COEFF = {}
for a in AGRID:
    COEFF[a] = delta_and_q(a, NCAP)
    d, q = COEFF[a]
    for n, kappa in [(1, mp.mpf("0.5")), (7, mp.mpf("0.8")), (NCAP, mp.mpf("0.95"))]:
        fast = d[n] + (kappa - 1)*q[n]
        slow = delta_paper(a, n, kappa)
        assert abs(fast - slow) <= mp.mpf("1e-40")*max(abs(slow), mp.mpf(1)), (float(a), n)

# lem:Delta-n-noneq2: at the endpoint kappa = 1 every coefficient of degree n != 2 is
# strictly positive.  (Degree two is the exceptional case, closed separately by
# lem:Delta2-positive; it is checked here too, but named on its own line.)
for a in AGRID:
    d, _ = COEFF[a]
    for n in range(1, NCAP + 1):
        assert d[n] > 0, (float(a), n, d[n])
print(f"  OK  Delta_n(a) > 0 for 1 <= n <= {NCAP} on the a-grid, lem:Delta-n-noneq2")
print("      (n = 2 included; that degree is lem:Delta2-positive's, proved separately)")

# Neither corollary carries an effective n, so the cap has to be chosen where the
# transition is reachable: eq. (first-negative-asymptotic) puts it near c(a)/(1-kappa),
# and a kappa too close to 1 pushes it past any finite cap -- at a = 0.05, kappa = 0.95
# it already sits above n = 60.  Only kappa with 3 c(a)/(1-kappa) <= NCAP is tested.
# The sign pattern is also not monotone -- at a = 0.05, kappa = 1/2 degree 2 is negative
# and degree 3 positive again -- so the eventual claim is read at the top of the ladder,
# not from the first negative degree onward.
tested = 0
for a in AGRID:
    d, q = COEFF[a]
    c_a = 4/mp.polygamma(1, a) - 4*a + mp.mpf(7)/2
    kappas = [k for k in [mp.mpf("0.5"), mp.mpf("0.8"), mp.mpf("0.95")]
              if 3*c_a/(1 - k) <= NCAP]
    assert kappas, (float(a), float(c_a))
    for kappa in kappas:
        signs = [d[n] + (kappa - 1)*q[n] < 0 for n in range(1, NCAP + 1)]
        assert any(signs), (float(a), float(kappa), "no negative degree under the cap")
        nonneg = [n for n in range(1, NCAP + 1) if not signs[n-1]]
        last_nonneg = max(nonneg) if nonneg else 0     # 0 = negative from degree one on
        assert last_nonneg <= NCAP - 10, (float(a), float(kappa), last_nonneg)
        tested += 1
print(f"  OK  on {tested} (a,kappa) pairs whose predicted transition c(a)/(1-kappa) sits")
print(f"      under the cap, a negative degree appears (the necessity part of thm:two-parameter-coeff) and the")
print(f"      last nonnegative degree is at most {NCAP - 10}, so the top of the ladder is")
print("      all negative (cor:eventual-negative-tail)")

print()
print("=== (Q1) fixed a, kappa -> 1: n_min grows without bound ===")
# This is the qualitative content of eq. (first-negative-asymptotic): with a fixed,
# the degree of the first negative coefficient tends to infinity as kappa -> 1.  It
# is asserted, not merely printed: n_min must be nondecreasing along the kappa
# ladder, and must eventually exceed the cap.
for a in [mp.mpf("0.3"), mp.mpf(1), mp.mpf(5)]:
    row = []
    for kappa in [mp.mpf("0.5"), mp.mpf("0.8"), mp.mpf("0.95"), mp.mpf("0.99"), mp.mpf("0.999")]:
        row.append((float(kappa), n_min(a, kappa)))
    print(f"  a={float(a):5.2f}: " + "  ".join(f"k={k:.3f}->n={n}" for k, n in row))
    seen = [(k, n) for k, n in row if n is not None]
    for (k1, n1), (k2, n2) in zip(seen, seen[1:]):
        assert n2 >= n1, (float(a), k1, n1, k2, n2, "n_min must not decrease as kappa -> 1")
    assert row[-1][1] is None or row[-1][1] > row[0][1], (
        float(a), row, "n_min must grow past the cap as kappa -> 1")
print("  (None = no negative coefficient found up to n=60, i.e. n_min already")
print("   exceeds the cap -- which is the unboundedness the remark claims)")

print()
print("=== (Q2) fixed kappa < 1, sweep a: is n_min unbounded in a? ===")
for kappa in [mp.mpf("0.25"), mp.mpf("0.6"), mp.mpf("0.9"), mp.mpf("0.99")]:
    vals = []
    for e in range(-2, 3):
        for f in [0, 3, 5, 7]:
            a = mp.mpf(10) ** (e + mp.mpf(f) / 10)
            vals.append((float(a), n_min(a, kappa)))
    finite = [n for _, n in vals if n is not None]
    print(f"  kappa={float(kappa):5.3f}: max n_min over the a-grid = "
          f"{max(finite) if finite else 'n/a'}"
          f"{'  (some a hit the n=60 cap)' if any(n is None for _, n in vals) else ''}")
    print("     " + "  ".join(f"a={a:.3g}:n={n}" for a, n in vals))


# ---------------------------------------------------------------------------
# The degree-one window in a, at fixed kappa < 1.
#
# sign Delta_1^{(kappa)}(a) = sign P(u),  u = a*psi_1(a) in (1, infinity),
# P(u) = -(eps/2) u^2 + u - 1,  eps = 1 - kappa.
# discriminant of P is 1 - 2 eps = 2 kappa - 1.
#   kappa <  1/2 : no real root, P < 0 identically -> Delta_1 < 0 for EVERY a > 0
#   kappa in (1/2,1) : P > 0 only for u in (u_-, u_+), u_pm = (1 -+ sqrt(2k-1))/eps
# u = a psi_1(a) decreases from +infinity (a -> 0) to 1 (a -> infinity), so the set
# {a : Delta_1 > 0} is a bounded interval; Delta_1 < 0 for all small AND all large a.
# ---------------------------------------------------------------------------
print()
print("=== the degree-one window in a (kappa < 1) ===")
for kappa in [mp.mpf("0.25"), mp.mpf("0.6"), mp.mpf("0.9"), mp.mpf("0.99"), mp.mpf("0.999")]:
    eps = 1 - kappa
    disc = 2 * kappa - 1
    if disc <= 0:
        assert all(delta_paper(mp.mpf(10) ** mp.mpf(e) / 2, 1, kappa) < 0 for e in range(-3, 4))
        print(f"  kappa={float(kappa):6.4f}: discriminant 2k-1={float(disc):+.3f} <= 0"
              f"  ->  Delta_1 < 0 for every a>0  (degree one serves every a)")
        continue
    um, up = (1 - mp.sqrt(disc)) / eps, (1 + mp.sqrt(disc)) / eps

    def invert_u(target):
        """Solve a*psi_1(a) = target by bisection; a*psi_1(a) decreases from
        +infinity (a -> 0) to 1 (a -> infinity)."""
        lo, hi = mp.mpf(10) ** -40, mp.mpf(10) ** 40
        for _ in range(400):
            mid = mp.sqrt(lo * hi)
            if mid * mp.polygamma(1, mid) > target:
                lo = mid
            else:
                hi = mid
        return mp.sqrt(lo * hi)

    a_hi = invert_u(um)   # large-a end of the window (u near 1)
    a_lo = invert_u(up)   # small-a end
    assert delta_paper(a_lo / 2, 1, kappa) < 0 and delta_paper(a_hi * 2, 1, kappa) < 0
    assert delta_paper(mp.sqrt(a_lo * a_hi), 1, kappa) > 0
    print(f"  kappa={float(kappa):6.4f}: Delta_1 > 0 only for a in "
          f"({float(a_lo):.4g}, {float(a_hi):.4g});  Delta_1 < 0 below and above")
print("  => at every fixed kappa<1 degree one also detects failure at LARGE a,")
print("     not 'only for small a>0'.")


# --------------------- does a single fixed degree serve every a at fixed kappa? ---
print()
print("=== a single fixed degree n with Delta_n^{(kappa)}(a) < 0 for every grid a? ===")
a_grid = [mp.mpf(10) ** (mp.mpf(e) / 4) for e in range(-8, 13)]   # a = 1e-2 .. 1e3
for kappa in [mp.mpf("0.25"), mp.mpf("0.6"), mp.mpf("0.9")]:
    good = []
    for n in range(1, 41):
        if all(delta_paper(a, n, kappa) < 0 for a in a_grid):
            good.append(n)
    print(f"  kappa={float(kappa):5.2f}: degrees serving every grid a = "
          f"{good if good else 'none up to n=40'}")
    # At fixed kappa < 1 such degrees DO exist, which is why the remark's claim
    # has to be quantified over kappa rather than stated at fixed kappa.
    assert good, (float(kappa), "expected some degree to serve every grid a")

print()
print("ALL PASS: verify_first_negative_degree")
