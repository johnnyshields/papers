"""eq:principal-finite-endpoint-regularity at the lower endpoint (lem:principal-endpoint-regularity).

The manuscript states the principal branch enters a finite endpoint linearly,
gamma(th) = t_e + gamma_e th + O(th^2) with gamma_e != 0, but leaves gamma_e
implicit.  This pins it at the lower endpoint th -> 0+, where t_e = t_a:

  tau'(0+) = -t_a cot(pi/k),      gamma_e = t_a (i - cot(pi/k))
                                          = -t_a exp(-i pi/k) / sin(pi/k),

with k = max(rho, 2) the multiplicity of the endpoint collision and rho the
multiplicity of the smallest zero of Q.  In particular

  * |gamma_e| = t_a / sin(pi/k) > 0, so gamma_e != 0 is automatic;
  * Im gamma_e = t_a, so gamma_e is never real -- the manuscript's ground for
    the branch being nonreal on the interior side;
  * rho <= 2 gives k = 2 and tau'(0+) = 0, so the radius meets the endpoint
    quadratically there and only the angle contributes to gamma_e.

The last point is what a formalization is most likely to get wrong: tau'(0+) is
zero at a simple or double smallest zero and nonzero from rho = 3 on, so a
development that reads "tau'(0+) = 0" off the rho = 1 picture is refuted at
Q(t) = (1-t)^3, the pencil the rest of this tree is built on.

The check also reproduces the same coefficients from the cluster expansion of
`Forgacs2017RationalDenominator` Prop. 3, zeta_j = 1 + (cos(pi/k) - w_j)/sin(pi/k) th,
so the two routes to gamma_e agree.

mpmath only.  Every assertion fails loudly.
"""

import mpmath as mp

mp.mp.dps = 60

TOL = mp.mpf('1e-6')          # the O(th) truncation of a one-sided slope at th = 1e-8


def ft_angle(a, tau, th):
    return mp.arg(tau * mp.exp(1j * th) - a)


def angle_sum(a, tau, th):
    return mp.fsum([ft_angle(ak, tau, th) for ak in a])


def branch_tau(a, r, th):
    """The principal branch radius: sum_k theta_k(tau) = r th + (n-1) pi."""
    n = len(a)
    target = r * th + (n - 1) * mp.pi
    lo, hi = mp.mpf('1e-30'), mp.mpf(1)
    while angle_sum(a, hi, th) > target:
        hi *= 2
        assert hi < mp.mpf(10) ** 12, "branch radius did not bracket"
    while angle_sum(a, lo, th) < target:
        lo /= 2
        assert lo > mp.mpf(10) ** (-40), "branch radius did not bracket"
    for _ in range(600):
        mid = (lo + hi) / 2
        if angle_sum(a, mid, th) > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def endpoint_ta(a, r):
    """t_a: the smallest zero when it is repeated, else the first positive zero of Sigma."""
    x1 = min(a)
    if sum(1 for x in a if x == x1) >= 2:
        return x1
    sigma = lambda s: mp.fsum([s / (ak - s) for ak in a]) + r
    lo = x1 * (1 + mp.mpf('1e-12'))
    hi = min([x for x in a if x > x1]) * (1 - mp.mpf('1e-12'))
    assert sigma(lo) > 0 > sigma(hi) or sigma(lo) < 0 < sigma(hi), "no sign change in the first gap"
    return mp.findroot(sigma, (lo, hi), solver='bisect', tol=mp.mpf(10) ** (-50))


CASES = [
    ([1, 3, 7], 1), ([1, 3, 7], 3), ([1, 2, 2, 2], 1), ([1, 5, 6, 11], 2),
    ([1, 1, 5], 1), ([2, 2, 9], 2), ([1, 1, 4, 4], 1),
    ([1, 1, 1], 1), ([1, 1, 1, 4, 9], 3),
    ([1, 1, 1, 1], 1), ([1, 1, 1, 1], 2),
    ([2, 2, 2, 2, 2], 1),
]

TH = mp.mpf('1e-8')
seen_k = set()

for a, r in CASES:
    a = [mp.mpf(x) for x in a]
    x1 = min(a)
    rho = sum(1 for x in a if x == x1)
    k = max(rho, 2)
    seen_k.add(k)
    ta = endpoint_ta(a, r)

    # tau -> t_a
    tau = branch_tau(a, r, TH)
    assert abs(tau - ta) < mp.mpf('1e-6') * ta, f"tau did not approach t_a: {tau} vs {ta}"

    # the slope, against -cot(pi/k)
    slope = (tau - ta) / TH
    pred = -ta * mp.cot(mp.pi / k)
    assert abs(slope - pred) < TOL * max(1, abs(ta)), (
        f"tau'(0+) = {slope}, expected {pred}  (a={a}, r={r}, k={k})")

    # gamma_e, from the branch and from the closed form
    gamma = tau * mp.exp(1j * TH)
    gslope = (gamma - ta) / TH
    gpred = ta * (1j - mp.cot(mp.pi / k))
    assert abs(gslope - gpred) < TOL * max(1, abs(ta)), (
        f"gamma_e = {gslope}, expected {gpred}")

    # the two closed forms for gamma_e agree, and it is nonreal of the stated modulus
    alt = -ta * mp.exp(-1j * mp.pi / k) / mp.sin(mp.pi / k)
    assert abs(gpred - alt) < mp.mpf('1e-40') * ta, "the two closed forms disagree"
    assert abs(mp.im(gpred) - ta) < mp.mpf('1e-40') * ta, "Im gamma_e is not t_a"
    assert abs(abs(gpred) - ta / mp.sin(mp.pi / k)) < mp.mpf('1e-40') * ta, "modulus wrong"
    assert abs(gpred) > 0, "gamma_e vanished"

    # the same coefficient from the cluster expansion of Prop. 3
    w = mp.exp(-1j * mp.pi / k)
    zeta1 = 1 + (mp.cos(mp.pi / k) - w) / mp.sin(mp.pi / k) * TH
    assert abs((tau * zeta1 - ta) / TH - gpred) < TOL * max(1, abs(ta)), (
        "the cluster expansion and the branch slope disagree")

assert {2, 3, 4, 5} <= seen_k, f"multiplicities exercised: {sorted(seen_k)}"

# rho <= 2 really is the degenerate case, and rho >= 3 really is not
for a, r, zero in [([1, 3, 7], 1, True), ([1, 1, 5], 1, True), ([1, 1, 1], 1, False),
                   ([1, 1, 1, 1], 1, False)]:
    a = [mp.mpf(x) for x in a]
    ta = endpoint_ta(a, r)
    slope = (branch_tau(a, r, TH) - ta) / TH
    if zero:
        assert abs(slope) < TOL, f"tau'(0+) should vanish here, got {slope}"
    else:
        assert abs(slope) > mp.mpf('0.5'), f"tau'(0+) should not vanish here, got {slope}"

# The endpoint collision is NEVER simple: k = 1 does not occur at a finite endpoint.
# t_a is a critical point of g in every case -- the zero of Sigma when the smallest zero of
# Q is simple, and the smallest zero itself when it is repeated -- so D(.,z_e) = Q + z_e t^r
# vanishes to order at least two there.  A development that discharges the endpoint binder
# only at k = 1 therefore discharges it nowhere.
def deriv_at(a, r, c, ze, t, m):
    """m-th derivative of D(.,ze) = c prod(a_k - t) + ze t^r, by Cauchy's formula."""
    f = lambda s: c * mp.fprod([ak - s for ak in a]) + ze * s ** r
    return mp.diff(f, t, m)


for a, r in CASES:
    a = [mp.mpf(x) for x in a]
    c = mp.mpf(1)
    ta = endpoint_ta(a, r)
    x1 = min(a)
    rho = sum(1 for x in a if x == x1)
    k = max(rho, 2)
    ze = -c * mp.fprod([ak - ta for ak in a]) / ta ** r
    scale = max(1, abs(deriv_at(a, r, c, ze, ta * mp.mpf('1.3'), 0)))
    for m in range(k):
        assert abs(deriv_at(a, r, c, ze, ta, m)) < mp.mpf('1e-25') * scale, (
            f"D^({m})(t_a) should vanish: a={a}, r={r}, k={k}")
    assert abs(deriv_at(a, r, c, ze, ta, k)) > mp.mpf('1e-8') * scale, (
        f"the collision at t_a is not exactly of order {k}: a={a}, r={r}")
    assert k >= 2, "a simple endpoint collision was produced"

# rho = 1: where the cluster formula degenerates and the k-formula does not.
# clusterAlpha divides by sin(pi/rho), which is sin(pi) = 0 at rho = 1 -- so a datum read off
# clusterAlpha uniformly in rho is 0 there, against a consumer asking for gamma_e != 0.  The
# collision multiplicity is k = max(rho, 2), and at rho = 1 that is 2, giving gamma_e = i*t_e
# with t_e = t_a strictly inside the first gap (x1, x2), NOT x1.
assert abs(mp.sin(mp.pi / 1)) < mp.mpf('1e-40'), "sin(pi/rho) does not vanish at rho = 1"

rho1_cases = 0
for a, r in CASES:
    a = [mp.mpf(x) for x in a]
    x1 = min(a)
    rho = sum(1 for x in a if x == x1)
    if rho != 1:
        continue
    rho1_cases += 1
    ta = endpoint_ta(a, r)
    # the endpoint limit is NOT the smallest zero: it sits strictly inside the first gap
    x2 = min([x for x in a if x > x1])
    assert x1 < ta < x2, f"t_a = {ta} not strictly inside ({x1}, {x2})"
    assert abs(ta - x1) > mp.mpf('1e-6') * x1, "t_a coincides with x1 at rho = 1"
    # the datum is i*t_a: the radius meets the endpoint quadratically, only the angle contributes
    tau = branch_tau(a, r, TH)
    gslope = (tau * mp.exp(1j * TH) - ta) / TH
    assert abs(gslope - 1j * ta) < TOL * max(1, ta), f"gamma_e = {gslope}, expected i*{ta}"
    assert abs(mp.re(gslope)) < TOL * max(1, ta), "tau'(0+) does not vanish at rho = 1"
    assert abs(gslope) > 0, "gamma_e vanished at rho = 1"
    # and it is the k = 2 instance of the same formula
    assert abs(gslope - ta * (1j - mp.cot(mp.pi / 2))) < TOL * max(1, ta), "k-formula disagrees"

assert rho1_cases >= 3, f"too few rho = 1 cases: {rho1_cases}"

# The measured gamma_e against the tree's own name for it.  `Cluster.clusterAlpha` is
#
#     alpha_j = -x1 * omega_j / sin(pi/rho),    omega_j = exp((2j-1) pi i/rho),
#
# and its docstring names j = 0 the principal upper branch, omega_+ = exp(-i pi/rho).  So the
# endpoint slope measured above should BE clusterAlpha x1 rho 0.  The two are defined for
# different purposes -- one is the cluster expansion of `eq:lower-cluster-expansion`, the other
# the branch derivative `eq:principal-finite-endpoint-regularity` asks for -- and nothing has
# compared them.
def cluster_alpha(x1, rho, j):
    omega = mp.exp((2 * mp.mpf(j) - 1) * mp.pi * 1j / rho)
    return -x1 * omega / mp.sin(mp.pi / rho)


for a, r in CASES:
    a = [mp.mpf(x) for x in a]
    x1 = min(a)
    rho = sum(1 for x in a if x == x1)
    if rho < 2:
        continue
    alpha = cluster_alpha(x1, rho, 0)
    # the closed form derived from the blow-up
    assert abs(alpha - x1 * (1j - mp.cot(mp.pi / rho))) < mp.mpf('1e-40') * x1, (
        f"clusterAlpha is not x1(i - cot(pi/rho)) at rho={rho}")
    # and the slope measured off the branch itself
    tau = branch_tau(a, r, TH)
    gslope = (tau * mp.exp(1j * TH) - x1) / TH
    assert abs(gslope - alpha) < TOL * max(1, x1), (
        f"gamma_e = {gslope} but clusterAlpha x1 {rho} 0 = {alpha}")
    assert abs(mp.im(alpha) - x1) < mp.mpf('1e-40') * x1, "Im clusterAlpha is not x1"

# The blow-up substitution tau = x1 - s*th, which is what makes the angle-sum equation
# regular at th = 0 when the smallest zero is repeated (rho >= 2).  Writing
# theta_k = arg(tau e^{i th} - a_k) and letting th -> 0 with s fixed, the rho copies of x1
# contribute arg(-s + i x1) each and the other n - rho contribute pi each, so
#
#     rho * arg(-s + i x1) + (n - rho) pi = (n - 1) pi,     i.e.  arg(-s + i x1) = pi - pi/rho,
#
# whose unique root is s = x1 cot(pi/rho) -- the measured slope above -- and whose derivative
# there is  rho * x1/(s^2 + x1^2) = rho sin^2(pi/rho)/x1 != 0 for every rho >= 2.  That is the
# nondegeneracy an implicit-function step in the blown-up variable would consume, and it does
# not vanish at any rho, so the route does not degenerate anywhere in the repeated case.
def limit_eq(s, x1, rho, n):
    return rho * mp.arg(mp.mpc(-s, x1)) + (n - rho) * mp.pi - (n - 1) * mp.pi


rho_cases = 0
for a, r in CASES:
    a = [mp.mpf(x) for x in a]
    x1 = min(a)
    rho = sum(1 for x in a if x == x1)
    n = len(a)
    if rho < 2:
        continue
    rho_cases += 1
    s0 = x1 * mp.cot(mp.pi / rho)

    # s0 solves the limit equation, and it is the only positive root
    assert abs(limit_eq(s0, x1, rho, n)) < mp.mpf('1e-40'), f"s0 not a root: rho={rho}"
    for s in [s0 + mp.mpf(d) for d in ('-0.9', '-0.3', '0.3', '0.9', '3.0')]:
        if s == s0 or s < -x1:
            continue
        assert abs(limit_eq(s, x1, rho, n)) > mp.mpf('1e-12'), f"a second root near {s}"

    # the derivative there, in closed form and by finite difference
    dpred = rho * mp.sin(mp.pi / rho) ** 2 / x1
    assert abs(dpred - rho * x1 / (s0 ** 2 + x1 ** 2)) < mp.mpf('1e-40'), "closed forms disagree"
    h = mp.mpf('1e-20')
    dnum = (limit_eq(s0 + h, x1, rho, n) - limit_eq(s0 - h, x1, rho, n)) / (2 * h)
    assert abs(dnum - dpred) < mp.mpf('1e-12') * dpred, f"derivative {dnum} vs {dpred}"
    assert dpred > 0, "the blow-up equation is degenerate in s"

    # and the branch's own s(th) converges to s0
    s_meas = (x1 - branch_tau(a, r, TH)) / TH
    assert abs(s_meas - s0) < TOL * max(1, x1), f"s(th) = {s_meas}, expected {s0}"

assert rho_cases >= 5, f"too few repeated-zero cases: {rho_cases}"

print(f"endpoint slopes checked at collision multiplicities {sorted(seen_k)}; "
      f"rho = 1 cases {rho1_cases}; "
      f"blow-up nondegeneracy checked at {rho_cases} repeated-zero pencils")
print("ALL PASS")
