r"""Paper section `sec:dominance` (The weighted dominance bound).

The lower endpoint at a **simple** smallest zero, which is the multiplicity
`check_endpoint_tau2_limit.py` does not cover.

There the branch does not run into a zero of the pencil: the endpoint `L` is the
first positive critical point of `g`, strictly inside `(x_1, x_2)`, so **every**
chord `D_k = a_k^2 - 2a_k\tau\cos\theta + \tau^2` stays off zero and all `n`
angle partials extend continuously to `\theta = 0`.  That is what replaces the
repeated case's cluster identity, and it is also why the repeated case's system
is degenerate here -- `\sin(\beta-\theta) \to 0`, `\sigma \to 0`, and the
determinant vanishes to first order.

FIRST ORDER (formalized in `../lean/ForgacsTran/EndpointTauDeriv2Simple.lean`):

  `\partial_\tau\Sigma/\theta \to -A`,  `A = \sum_k a_k/(a_k - L)^2 > 0`
  `(\partial_\theta\Sigma - r)/\theta \to 0`
  `\tau' = -(\partial_\theta\Sigma - r)/\partial_\tau\Sigma \to 0`

with the endpoint value of `\partial_\theta\Sigma` supplied by `E(L) = 0` read
logarithmically, `\sum_k L/(L - a_k) = r`.

SECOND ORDER (not formalized; this script is what prices the route).  Writing
`M = \sum_k \partial^2_{\theta\tau}\theta_k`, `N = \sum_k \partial^2_{\theta\theta}\theta_k`
and `P = \sum_k \partial^2_{\tau\tau}\theta_k`, the quotient rule collapses to

  `\tau'' = -(2M\tau' + N + P\tau'^2)/\partial_\tau\Sigma`,

which is CIRCULAR read directly: `M \to -A`, `\partial_\tau\Sigma \sim -A\theta`,
so the first term is `-2\tau'/\theta` and reproduces the unknown.  Rearranged it
is a linear ODE for `y = \tau'`,

  `y' + 2y/\theta = C(\theta)`,   `C = -N/\partial_\tau\Sigma - P\tau'^2/\partial_\tau\Sigma`,

whose integrating factor `\theta^2` gives `\theta^2\tau'(\theta) = \int_0^\theta t^2C(t)dt`
-- the boundary term vanishing because `\tau' \to 0`, which is the first-order
result above.  Then `\tau'/\theta \to C_0/3` and `\tau''(0^+) = C_0/3`, with

  `C_0 = N_1/A`,   `N_1 = \sum_k a_k L(a_k + L)/(a_k - L)^3`.

What is checked here:

* S1  `L` is a root of `E` in the first gap, and `\sum_k L/(L - a_k) = r`;
* S2  the two first-order slopes, and `\tau' \to 0`;
* S3  the collapsed identity for `\tau''` holds on the arc;
* S4  `\tau'' + 2\tau'/\theta \to C_0`, and both `\tau''` and `\tau'/\theta`
      settle on `C_0/3` -- the relation the integrating-factor route turns on;
* S5  `\tau''` by a central second difference of `\tau`, which touches no partial
      derivative, against the same `C_0/3`.

mpmath only.
"""

from mpmath import mp, mpf, pi, atan, sin, cos, fabs, findroot, mpmathify

mp.dps = 60
TOL = mpf(10) ** -25


def ft_arccot(x):
    return pi / 2 - atan(x)


def ft_angle(a, tau, s):
    return ft_arccot(cos(s) / sin(s) - a / (tau * sin(s)))


def ft_tau(A, r, s):
    l = len(A) - 1
    target = r * s + l * pi
    lo, hi = mpf(10) ** -25, mpf(10) ** 25
    for _ in range(500):
        mid = (lo + hi) / 2
        if sum(ft_angle(a, mid, s) for a in A) > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


# the tree's own forms
def d_tau(a, tau, s):
    return -(sin(ft_angle(a, tau, s)) ** 2 * a / (tau ** 2 * sin(s)))


def d_ang(a, tau, s):
    y = ft_angle(a, tau, s)
    return sin(y) * cos(y - s) / sin(s)


def d2_tau(a, tau, s):
    y = ft_angle(a, tau, s)
    return a * sin(y) ** 2 * (2 * tau * sin(s) + 2 * a * sin(y) * cos(y)) \
        / (tau ** 4 * sin(s) ** 2)


def d2_ang_tau(a, tau, s):
    y = ft_angle(a, tau, s)
    return -(sin(y) ** 2 * a / (tau ** 2 * sin(s))) * cos(2 * y - s) / sin(s)


def d2_ang(a, tau, s):
    y = ft_angle(a, tau, s)
    return ((cos(y) * (sin(y) * cos(y - s) / sin(s)) * cos(y - s)
             + sin(y) * (-sin(y - s) * (sin(y) * cos(y - s) / sin(s) - 1))) * sin(s)
            - sin(y) * cos(y - s) * cos(s)) / sin(s) ** 2


def d2_tau_ang(a, tau, s):
    y = ft_angle(a, tau, s)
    return -(a / tau ** 2) * (
        (2 * sin(y) * cos(y) * (sin(y) * cos(y - s) / sin(s)) * sin(s)
         - sin(y) ** 2 * cos(s)) / sin(s) ** 2)


def sums(A, r, s):
    tau = ft_tau(A, r, s)
    St = sum(d_tau(a, tau, s) for a in A)
    Sa = sum(d_ang(a, tau, s) for a in A)
    t1 = -(Sa - r) / St
    M = sum(d2_ang_tau(a, tau, s) for a in A)
    N = sum(d2_ang(a, tau, s) for a in A)
    P = sum(d2_tau(a, tau, s) for a in A)
    dSa = M * t1 + N
    dSt = P * t1 + sum(d2_tau_ang(a, tau, s) for a in A)
    t2 = (-dSa * St - -(Sa - r) * dSt) / St ** 2
    return dict(tau=tau, St=St, Sa=Sa, t1=t1, t2=t2, M=M, N=N, P=P)


def crit_eval(A, r, t):
    Q = mpf(1)
    for a in A:
        Q *= (t - a)
    dQ = mpf(0)
    for i in range(len(A)):
        term = mpf(1)
        for j in range(len(A)):
            if j != i:
                term *= (t - A[j])
        dQ += term
    return t * dQ - r * Q


def endpoint(A, r):
    """The first positive critical point, bracketed inside the first gap."""
    B = sorted(A)
    return findroot(lambda t: crit_eval(A, r, t), (B[0] + B[1]) / 2)


def constants(A, r, L):
    Aconst = sum(a / (a - L) ** 2 for a in A)
    N1 = sum(a * L * (a + L) / (a - L) ** 3 for a in A)
    return Aconst, N1, N1 / Aconst


# simple smallest zero: the minimum is attained once
PENCILS = [(["1", "2", "4"], 1), (["1", "2", "4"], 2), (["1", "3", "5", "9"], 1),
           (["0.5", "2", "6"], 3), (["1", "2"], 3), (["2", "3", "11"], 1)]
PEN = [([mpmathify(x) for x in A], r) for A, r in PENCILS]

print("S1  the endpoint is a root of E in the first gap, and E(L)=0 reads logarithmically")
for A, r in PEN:
    L = endpoint(A, r)
    B = sorted(A)
    assert B[0] < L < B[1], f"the endpoint is not in the first gap at {A}, r={r}"
    lhs = sum(L / (L - a) for a in A)
    assert fabs(lhs - r) < TOL, f"sum L/(L-a_k) is {lhs}, not {r}, at {A}"
    print(f"    {[mp.nstr(a, 6) for a in A]} r={r}: L = {mp.nstr(L, 12)}, "
          f"|sum L/(L-a_k) - r| = {mp.nstr(fabs(lhs - r), 3)}")

print("S2  the two first-order slopes, and tau' -> 0")
for A, r in PEN:
    L = endpoint(A, r)
    Aconst, _, _ = constants(A, r, L)
    prev = None
    for k in [8, 12, 16, 20]:
        s = (pi / r) / mpf(2) ** k
        p = sums(A, r, s)
        gaps = (fabs(p["St"] / s + Aconst), fabs((p["Sa"] - r) / s), fabs(p["t1"]))
        if prev is not None:
            for g, q in zip(gaps, prev):
                assert g < q * mpf("0.7"), f"a slope is not settling at {A}, r={r}"
        prev = gaps
    print(f"    {[mp.nstr(a, 6) for a in A]} r={r}: |dSt/th + A| = {mp.nstr(gaps[0], 3)}, "
          f"|(dSa - r)/th| = {mp.nstr(gaps[1], 3)}, |tau'| = {mp.nstr(gaps[2], 3)}")

print("S3  the collapsed identity for tau'' holds on the arc")
worst = mpf(0)
for A, r in PEN:
    for k in [4, 8, 12, 16]:
        s = (pi / r) / mpf(2) ** k
        p = sums(A, r, s)
        rhs = -(2 * p["M"] * p["t1"] + p["N"] + p["P"] * p["t1"] ** 2) / p["St"]
        d = fabs(rhs - p["t2"]) / max(mpf(1), fabs(p["t2"]))
        assert d < TOL, f"the collapsed identity fails at {A}, r={r}, s={s}: {d}"
        worst = max(worst, d)
print(f"    largest relative disagreement: {mp.nstr(worst, 5)}")

print("S4  tau'' + 2 tau'/th -> C0, and tau'' -> C0/3")
for A, r in PEN:
    L = endpoint(A, r)
    _, _, C0 = constants(A, r, L)
    prev = None
    for k in [8, 12, 16, 20]:
        s = (pi / r) / mpf(2) ** k
        p = sums(A, r, s)
        gaps = (fabs(p["t2"] + 2 * p["t1"] / s - C0), fabs(p["t2"] - C0 / 3),
                fabs(p["t1"] / s - C0 / 3))
        if prev is not None:
            for g, q in zip(gaps, prev):
                assert g < q * mpf("0.7"), \
                    f"the ODE relation is not settling at {A}, r={r}: {prev} -> {gaps}"
        prev = gaps
    print(f"    {[mp.nstr(a, 6) for a in A]} r={r}: C0 = {mp.nstr(C0, 12)}, "
          f"tau''(0+) = C0/3 = {mp.nstr(C0 / 3, 12)}, "
          f"|tau'' - C0/3| = {mp.nstr(gaps[1], 3)}")

print("S5  tau'' by a central second difference, which touches no partial derivative")
for A, r in PEN[:3]:
    L = endpoint(A, r)
    _, _, C0 = constants(A, r, L)
    prev = None
    for k in [6, 10, 14]:
        s = (pi / r) / mpf(2) ** k
        h = s / 8
        v = (ft_tau(A, r, s + h) - 2 * ft_tau(A, r, s) + ft_tau(A, r, s - h)) / h ** 2
        gap = fabs(v - C0 / 3)
        if prev is not None:
            assert gap < prev / 4, f"the central difference is not settling at {A}, r={r}"
        prev = gap
    print(f"    {[mp.nstr(a, 6) for a in A]} r={r}: C0/3 = {mp.nstr(C0 / 3, 12)}, "
          f"|central difference - C0/3| = {mp.nstr(gap, 3)}")

print()
print("check_endpoint_tau2_simple.py: PASS")
