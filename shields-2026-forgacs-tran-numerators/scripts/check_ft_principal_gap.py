"""Minimum-modulus gap for the constructed Forgacs-Tran branch.

Section: sec:geometry, thm:FT-geometry -- the binder `hmin` of
`ForgacsTran/FTGeometryBranch.lean`, discharged in
`ForgacsTran/FTMinModulus/PrincipalGap.lean`.

For the admissible class Q(t) = c prod_k (a_k - t) with a_k > 0, c > 0, r >= 1,
at the principal index l = n - 1, this checks four statements.

  (1) TARGET.  The principal pair tau(theta) e^{+- i theta} are the only zeros of
      Q(t) + z(theta) t^r in the closed disk |t| <= tau(theta).  This is `hmin`.
  (2) `exists_ftAngleSum_index_of_root`.  Every zero sigma e^{-i phi} of the
      pencil with phi in (0, pi/r) has sum_k theta_k(sigma; phi) = r phi + l pi
      for a natural l with l < n, and (-1)^{n+l+1} z > 0, and 1 <= l unless
      n < r.  Checked against zeros manufactured at every index, not only at
      n - 1, so the sweep is not vacuous.
  (3) `hcone` is satisfiable: every zero of the pencil in the closed disk has
      |arg| strictly inside (0, pi/r).
  (4) `hidx` is NOT free: the (n, r, l) triples of the right parity with
      n > (l+1) r are exactly the ones `ftBranchAt_arc_of_le_two_mul` cannot
      reach, and the smallest is (4, 1, 1).
  (5) The paper's own closing squeeze has no branch to run along: at 2r < n the
      index-1 branch is absent at psi = pi/(n-r), inside the viewing arc.  This is
      why `ftProp1_closing_principal` squeezes on the principal index instead.
  (6) `ftTau_principal_le`, the lower end of the bracket that squeeze runs the
      intermediate value theorem over: tau(psi; n-1) <= tau(psi; l) for l <= n-1.
  (7) `negDivPow_ftTau_lt_ftBranchZ`: -Q(tau)/tau^r < z(theta), the magnitude
      comparison the cone argument opens with; and `E < 0` on (0, tau), the
      hypothesis `negDivPow_lt_ftBranchZ_of_ftCritical_neg` consumes.  Also
      records that tau <= min a_k is FALSE, so the cheap route to the real
      exclusion is unavailable and the critical point cannot be dispensed with.
  (8) The two statements that close `hcone` at r = 1: `E` has no zero below the
      branch radius, and the fiber map on the negative axis is bounded below by
      its value at the negative critical point (their Lemma 5).  Both under a
      simple smallest zero, which is the hypothesis the Lean proofs carry.
  (9) `ftTau_le_of_repeated_min`: at a repeated smallest zero the branch radius
      stays under that zero across the whole arc.  This replaces the first-gap
      bracket, which does not exist there, and is why the repeated case needs no
      critical point at all.
"""

import numpy as np
from scipy.optimize import brentq

def ft_angle(a, tau, psi):
    """The unique theta_k in (psi, pi) with a sin theta = tau sin(theta - psi)."""
    y = np.cos(psi) / np.sin(psi) - a / (tau * np.sin(psi))
    return np.pi / 2 - np.arctan(y)

def angle_sum(a, tau, psi):
    return sum(ft_angle(ak, tau, psi) for ak in a)

def branch_tau(a, r, l, theta):
    """Solve angle_sum(a, tau, theta) = r theta + l pi for tau > 0, or None."""
    target = r * theta + l * np.pi
    f = lambda t: angle_sum(a, t, theta) - target
    lo, hi = 1e-12, 1.0
    while f(hi) > 0:
        hi *= 2.0
        if hi > 1e12:
            return None
    if f(lo) < 0:
        return None
    return brentq(f, lo, hi, xtol=1e-15, rtol=1e-15)

def pencil_roots(a, c, r, z):
    Q = np.array([c])
    for ak in a:
        Q = np.polynomial.polynomial.polymul(Q, np.array([ak, -1.0]))
    P = np.zeros(max(len(a), r) + 1)
    P[: len(a) + 1] += Q
    P[r] += z
    while len(P) > 1 and abs(P[-1]) < 1e-13:
        P = P[:-1]
    return np.polynomial.polynomial.polyroots(P)

def branch_z(a, c, r, l, theta, tau):
    n = len(a)
    t0 = tau * np.exp(-1j * theta)
    prod = np.prod([abs(ak - t0) for ak in a])
    return (-1.0) ** (n + l + 1) * c * prod / tau ** r

FAIL = []
def check(cond, msg):
    if not cond:
        FAIL.append(msg)

rng = np.random.default_rng(20260825)
cases = [(3, 1, np.array([1.0, 2.0, 3.0]), 1.0),      # the brief's instantiation
         (2, 2, np.array([1.0, 2.0]), 1.0),           # the brief's second
         (2, 2, np.array([0.25, 7.0]), 2.5),
         (1, 2, np.array([1.5]), 1.0),                # n < r, where l = 0 is legal
         (1, 3, np.array([0.4]), 0.7)]
for n in range(2, 8):
    for r in range(1, 6):
        if n == 2 and r == 1:
            continue                                  # the excluded (deg Q, r) = (2,1)
        for _ in range(6):
            cases.append((n, r, np.sort(rng.uniform(0.2, 6.0, size=n)), rng.uniform(0.3, 3.0)))

n_target, n_quant, n_cone, l_seen = 0, 0, 0, set()
for (n, r, a, c) in cases:
    for lb in range(0, n):                            # every index, not only n - 1
        if lb != n - 1 and not (n * 1.0 < r + lb * np.pi):
            pass                                      # branch_tau reports unsolvable
        for frac in (0.05, 0.2, 0.4, 0.6, 0.8, 0.95):
            theta = frac * np.pi / r
            tau = branch_tau(a, r, lb, theta)
            if tau is None:
                continue
            z = branch_z(a, c, r, lb, theta, tau)
            t0 = tau * np.exp(-1j * theta)
            resid = c * np.prod([ak - t0 for ak in a]) + z * t0 ** r
            scale = c * np.prod([abs(ak) + tau for ak in a]) + abs(z) * tau ** r
            check(abs(resid) < 1e-8 * scale, f"branch point not a root n={n} r={r} l={lb}")

            roots = pencil_roots(a, c, r, z)
            for w in roots:
                if abs(w) < 1e-12:
                    continue
                phi = -np.angle(w)
                if not (1e-9 < phi < np.pi / r - 1e-9):
                    continue
                # (2) the quantization, at this root
                n_quant += 1
                S = angle_sum(a, abs(w), phi)
                lval = (S - r * phi) / np.pi
                lint = int(round(lval))
                l_seen.add((n, r, lint))
                check(abs(lval - lint) < 1e-7,
                      f"(2) angle sum not quantized: l={lval:.9f} n={n} r={r}")
                check(0 <= lint < n, f"(2) index out of range l={lint} n={n}")
                check(lint >= 1 or n < r, f"(2) l=0 with n>=r, n={n} r={r}")
                check((-1.0) ** (n + lint + 1) * z > 0,
                      f"(2) sign wrong l={lint} n={n} z={z}")

            if lb != n - 1:
                continue
            # (1) the target statement and (3) the cone, at the principal index
            for w in roots:
                if abs(abs(w) - tau) < 1e-7 and abs(abs(w.imag) - tau * np.sin(theta)) < 1e-6:
                    continue
                n_target += 1
                check(abs(w) > tau * (1 + 1e-9),
                      f"(1) inner zero |w|={abs(w):.8f} <= tau={tau:.8f} n={n} r={r}")
            for w in roots:
                if abs(w) <= tau * (1 + 1e-9):
                    n_cone += 1
                    check(0 < abs(np.angle(w)) < np.pi / r + 1e-9,
                          f"(3) cone violated arg={np.angle(w)} n={n} r={r}")

# (6) `ftTau_principal_le` and the bracket `ftProp1_closing_principal` runs the
# intermediate value theorem over: tau(psi; n-1) <= tau(psi; l) for every l <= n-1
# whose branch exists at psi.  This is the lower end of the bracket, and it is what
# lets the squeeze run on the principal branch instead of on the index-l one.
n_bracket = 0
for (n, r, a, c) in cases:
    for lb in range(0, n):
        for frac in (0.05, 0.3, 0.6, 0.9):
            psi = frac * np.pi / r
            tl = branch_tau(a, r, lb, psi)
            tp = branch_tau(a, r, n - 1, psi)
            if tl is None or tp is None:
                continue
            n_bracket += 1
            check(tp <= tl * (1 + 1e-9),
                  f"(6) tau(n-1) > tau(l) at n={n} r={r} l={lb} psi={psi:.4f}")

# (5) `not_arc_wide_of_two_mul_lt`: at 2r < n the index l = 1 admits no branch at
# psi = pi/(n-r), and that angle is inside the arc.  Sharpness of n <= 2 r.
n_refute = 0
for n in range(2, 10):
    for r in range(1, 6):
        a = np.sort(rng.uniform(0.2, 6.0, size=n))
        psi = np.pi / (n - r) if n > r else None
        if 2 * r < n:
            check(psi < np.pi / r, f"(5) psi outside the arc n={n} r={r}")
            check(branch_tau(a, r, 1, psi) is None,
                  f"(5) index-1 branch exists at psi=pi/(n-r), n={n} r={r}")
            n_refute += 1
        elif n <= 2 * r:
            # the discharged range: index 1 must exist at every angle of the arc
            for frac in (0.05, 0.5, 0.95):
                check(branch_tau(a, r, 1, frac * np.pi / r) is not None,
                      f"(5) index-1 branch missing in the n<=2r range n={n} r={r}")
# the concrete triple the Lean docstring names
a413 = np.array([1.0, 2.0, 3.0, 4.0])
check(branch_tau(a413, 1, 1, np.pi / 3 + 1e-6) is None, "(5) (4,1,1) above pi/3 should fail")
check(branch_tau(a413, 1, 1, np.pi / 3 - 1e-3) is not None, "(5) (4,1,1) below pi/3 should hold")

# (7) `negDivPow_ftTau_lt_ftBranchZ` and the hypothesis it is fed with:
#     -Q(tau)/tau^r < z(theta), and E < 0 on (0, tau).  Also records that the
#     cheap route is unavailable: tau <= min a_k is FALSE.
n_mag, n_En, n_taumin_false = 0, 0, 0
for (n, r, a, c) in cases:
    for frac in (0.02, 0.2, 0.5, 0.8, 0.98):
        theta = frac * np.pi / r
        tau = branch_tau(a, r, n - 1, theta)
        if tau is None:
            continue
        z = branch_z(a, c, r, n - 1, theta, tau)
        Qtau = c * np.prod([ak - tau for ak in a])
        n_mag += 1
        check(-Qtau / tau ** r < z, f"(7) -Q(tau)/tau^r >= z at n={n} r={r}")
        if tau > min(a) * (1 + 1e-9):
            n_taumin_false += 1
        for u in np.linspace(tau * 1e-5, tau * (1 - 1e-6), 400):
            Q = c * np.prod([ak - u for ak in a])
            Qp = c * sum(-np.prod([a[j] - u for j in range(n) if j != k]) for k in range(n))
            n_En += 1
            check(u * Qp - r * Q < 0, f"(7) E >= 0 below tau at n={n} r={r} u={u:.4f}")

# (8) `ftCritical_ne_zero_below_ftTau` and `negDivPow_ge_of_neg`, the two real
#     statements that close `hcone` at r = 1.  Both are checked with a SIMPLE
#     smallest zero, which is the hypothesis the Lean proof carries.
def _E(a, c, r, t):
    n = len(a)
    Q = c * np.prod([ak - t for ak in a])
    Qp = c * sum(-np.prod([a[j] - t for j in range(n) if j != k]) for k in range(n))
    return t * Qp - r * Q

n_first, n_lem5 = 0, 0
for (n, r, a, c) in cases:
    if n < 3 or len(set(np.round(a, 12))) < n or abs(a[1] - a[0]) < 1e-9:
        continue                                   # smallest zero must be simple
    for frac in (0.05, 0.3, 0.6, 0.9):
        tau = branch_tau(a, r, n - 1, frac * np.pi / r)
        if tau is None:
            continue
        for u in np.linspace(tau * 1e-4, tau * (1 - 1e-6), 300):
            n_first += 1
            check(_E(a, c, r, u) != 0 and _E(a, c, r, u) < 0,
                  f"(8) E vanishes below tau at n={n} r={r} u={u:.5f}")
    if r == 1:
        # Lemma 5: the negative axis is bounded below by its critical value
        sig = lambda t: sum(t / (ak - t) for ak in a) + 1
        lo, hi = 1e-8, 1.0
        while sig(-hi) > 0:
            hi *= 2
        L = brentq(lambda u: sig(-u), lo, hi, xtol=1e-15, rtol=8.9e-16)
        b = -c * np.prod([ak + L for ak in a]) / (-L)
        for u in np.geomspace(1e-6, 1e6, 500):
            n_lem5 += 1
            check(-c * np.prod([ak + u for ak in a]) / (-u) >= b * (1 - 1e-12),
                  f"(8) negative axis falls below b at n={n} u={u:.4e}")

# (9) `ftTau_le_of_repeated_min`: at a REPEATED smallest zero the branch radius
#     stays under that zero across the whole arc, which is what replaces the
#     first-gap bracket there.  Checked including theta -> 0+, where the margin
#     is smallest; the mpmath spot-checks in the report cover the digits float64
#     cannot resolve.
n_rep = 0
rep_cases = [(3, 1, np.array([1.0, 1.0, 5.0])), (3, 1, np.array([1.0, 1.0, 1.0])),
             (4, 1, np.array([2.0, 2.0, 2.0, 9.0])), (4, 1, np.array([1.0]*4)),
             (5, 1, np.array([0.5, 0.5, 3.0, 7.0, 20.0])), (4, 2, np.array([1.0, 1.0, 4.0, 4.0])),
             (5, 3, np.array([1.0, 1.0, 1.0, 2.0, 2.0])),
             (6, 1, np.array([1e-3, 1e-3, 1.0, 1.0, 1.0, 50.0]))]
for (n, r, a) in rep_cases:
    x1 = min(a)
    for frac in (1e-9, 1e-6, 1e-3, 0.01, 0.1, 0.3, 0.5, 0.7, 0.9, 0.999):
        tau = branch_tau(a, r, n - 1, frac * np.pi / r)
        if tau is None:
            continue
        n_rep += 1
        check(tau <= x1 * (1 + 1e-9),
              f"(9) tau exceeds the repeated smallest zero: n={n} r={r} frac={frac}")

# (4) the triples `ftBranchAt_arc_of_le_two_mul` cannot reach.
idx_gap = [(n, r, lp) for n in range(2, 9) for r in range(1, 6) for lp in range(1, n)
           if (n + lp + 1) % 2 == 0 and n > (lp + 1) * r]
check(min(idx_gap) == (4, 1, 1), f"(4) smallest unreachable triple is {min(idx_gap)}")

print(f"(1) target comparisons:              {n_target}")
print(f"(2) quantization checks:             {n_quant}  over indices {sorted(l_seen)[:10]}...")
print(f"(3) cone checks on closed-disk zeros:{n_cone}")
print(f"(4) triples with n > (l+1)r:         {len(idx_gap)}, smallest {min(idx_gap)}")
print(f"(6) index-monotonicity brackets:     {n_bracket}")
print(f"(9) repeated-min bracket tau <= x1:  {n_rep} samples")
print(f"(8) E != 0 below tau: {n_first} samples;  Lemma 5 negative axis: {n_lem5} samples")
print(f"(7) -Q(tau)/tau^r < z checks:        {n_mag};  E < 0 below tau: {n_En} samples")
print(f"    tau > min(a_k) (cheap route dead): {n_taumin_false} of {n_mag} branch points")
print(f"(5) index-1 branch absent at 2r < n: {n_refute} (n,r) pairs")
for m in FAIL[:20]:
    print("FAIL:", m)
assert not FAIL, f"{len(FAIL)} failures"
print("ALL PASS")
