r"""Paper section `sec:dominance` (The weighted dominance bound).

`\tau''` **converges** at the lower endpoint of the viewing arc, at every
admissible pencil whose smallest zero is repeated.

`check_tau_second_derivative_limit.py` measured whether the limit exists and
found that it does; this script checks the ROUTE, which is what the
formalization follows.  The route is elementary -- no Puiseux parameter, no
implicit function theorem, no analyticity at the endpoint.

Write `x_1` for the smallest zero, `\rho \ge 2` for its multiplicity, `C` for the
indices carrying it and `F` for the rest, and `\beta = \theta_k` for the common
branch angle at a `C` index.  Two identities hold on the whole arc:

  (A)  `x_1\sin\beta = \tau\sin(\beta - \theta)`      (`ftAngle_spec`)
  (B)  `\rho b + \sigma\tau' + A_F = r`,  `b = \beta'`  (the branch equation,
       differentiated, with the `C` terms collected)

where `\sigma = \sum_F \partial_\tau\theta_j` and `A_F = \sum_F
\partial_\theta\theta_j`.  Differentiating (A) once and (B) as it stands gives a
linear system for `(\tau', b)`; differentiating each once more gives a system for
`(\tau'', \beta'')` with the SAME matrix

  `M = [[\sin(\beta-\theta), \Delta], [\sigma, \rho]]`,
  `\Delta = \tau\cos(\beta-\theta) - x_1\cos\beta`.

Every entry of `M` and of both right-hand sides converges as `\theta \downarrow 0`,
and `\det M \to \rho\sin(\pi/\rho) \ne 0`.  So Cramer's rule gives the limits.
That is the whole proof: the individual partials at a `C` index blow up like
`1/\theta` and their combination `b` does not, which is why (A) is carried
separately instead of being folded into the angle sum.

What is checked here:

* X1  the four partials in the tree's own form equal the manifestly continuous
      rational form over `D = \tau^2 - 2a\tau\cos\theta + a^2`;
* X2  the two first-order equations hold on the arc;
* X3  the two second-order equations hold on the arc;
* X4  every entry converges, with the predicted limits;
* X5  `\tau''` from Cramer agrees with `\tau''` measured directly, and both
      settle on the closed form
        `D_2 = x_1(1 - 2b_0) - 2x_1\cos^2(\pi/\rho)(b_0-1)/\sin^2(\pi/\rho)`,
        `b_0 = (r + \sum_F x_1/(a_j - x_1))/\rho`;
* X6  `D_2 = 7/9` at the witness cubic `a = (1,1,1)`, `r = 1`, which is the
      value the cluster expansion gives independently, and is NOT
      `ftTauDeriv2(0) = 0` (`banked.txt` BANK-79);
* X7  a second route to `D_2` sharing no instrument with the first: a central
      second difference of `\tau` itself, which touches no partial derivative.

Precision is set from the smallest angle: the angle sum subtracts terms of size
`1/\theta`, so a second derivative near the endpoint costs several times
`-\log_{10}\theta` digits.

mpmath only.
"""

from mpmath import mp, mpf, pi, atan, sin, cos, sqrt, fabs, mpmathify

mp.dps = 80

TOL = mpf(10) ** -30
# a quantity that is exactly its own limit on the arc -- `b` and `sigma` at a
# pencil with no far zeros -- leaves a gap that is already at the working
# precision, and a ratio test on it measures rounding rather than convergence
FLOOR = mpf(10) ** -60


# ---------------------------------------------------------------- the branch

def ft_arccot(x):
    return pi / 2 - atan(x)


def ft_angle(a, tau, s):
    return ft_arccot(cos(s) / sin(s) - a / (tau * sin(s)))


def ft_angle_sum(A, tau, s):
    return sum(ft_angle(a, tau, s) for a in A)


def ft_tau(A, r, s):
    """The branch radius, by bisection on the strictly decreasing angle sum."""
    l = len(A) - 1
    target = r * s + l * pi
    lo, hi = mpf(10) ** -20, mpf(10) ** 20
    assert ft_angle_sum(A, lo, s) > target > ft_angle_sum(A, hi, s), \
        f"the branch is not bracketed at theta = {s}"
    for _ in range(400):
        mid = (lo + hi) / 2
        if ft_angle_sum(A, mid, s) > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


# ------------------------------------------- the partials, the tree's own form

def d_tau(a, tau, s):
    """`ftAngleDerivTau`, as `FTBranchTauDeriv` writes it."""
    return -(sin(ft_angle(a, tau, s)) ** 2 * a / (tau ** 2 * sin(s)))


def d_ang(a, tau, s):
    """`ftAngleDerivAngle`, as `FTBranchTauDeriv` writes it."""
    y = ft_angle(a, tau, s)
    return sin(y) * cos(y - s) / sin(s)


def d2_tau(a, tau, s):
    """`ftAngleDeriv2Tau`."""
    y = ft_angle(a, tau, s)
    return a * sin(y) ** 2 * (2 * tau * sin(s) + 2 * a * sin(y) * cos(y)) \
        / (tau ** 4 * sin(s) ** 2)


def d2_ang_tau(a, tau, s):
    """`ftAngleDeriv2AngleTau`."""
    y = ft_angle(a, tau, s)
    return -(sin(y) ** 2 * a / (tau ** 2 * sin(s))) * cos(2 * y - s) / sin(s)


def d2_tau_ang(a, tau, s):
    """`ftAngleDeriv2TauAngle`."""
    y = ft_angle(a, tau, s)
    return -(a / tau ** 2) * (
        (2 * sin(y) * cos(y) * (sin(y) * cos(y - s) / sin(s)) * sin(s)
         - sin(y) ** 2 * cos(s)) / sin(s) ** 2)


def d2_ang(a, tau, s):
    """`ftAngleDeriv2Angle`."""
    y = ft_angle(a, tau, s)
    return ((cos(y) * (sin(y) * cos(y - s) / sin(s)) * cos(y - s)
             + sin(y) * (-sin(y - s) * (sin(y) * cos(y - s) / sin(s) - 1))) * sin(s)
            - sin(y) * cos(y - s) * cos(s)) / sin(s) ** 2


# --------------------------------------- the same four, in rational chart form

def bigD(a, tau, s):
    return tau ** 2 - 2 * a * tau * cos(s) + a ** 2


def r_tau(a, tau, s):
    return -a * sin(s) / bigD(a, tau, s)


def r_ang(a, tau, s):
    return tau * (tau - a * cos(s)) / bigD(a, tau, s)


def r2_tau(a, tau, s):
    return 2 * a * sin(s) * (tau - a * cos(s)) / bigD(a, tau, s) ** 2


def r2_mixed(a, tau, s):
    D = bigD(a, tau, s)
    return -a * (cos(s) * D - 2 * a * tau * sin(s) ** 2) / D ** 2


def r2_mixed_other(a, tau, s):
    D = bigD(a, tau, s)
    return ((2 * tau - a * cos(s)) * D
            - tau * (tau - a * cos(s)) * (2 * tau - 2 * a * cos(s))) / D ** 2


def r2_ang(a, tau, s):
    D = bigD(a, tau, s)
    return a * tau * sin(s) * (D - 2 * tau * (tau - a * cos(s))) / D ** 2


# ------------------------------------------------------ derivatives of the arc

def tau_deriv(A, r, s):
    """`ftTauDeriv`, from the tree's quotient."""
    tau = ft_tau(A, r, s)
    St = sum(d_tau(a, tau, s) for a in A)
    Sa = sum(d_ang(a, tau, s) for a in A)
    return -(Sa - r) / St


def tau_deriv2(A, r, s):
    """`ftTauDeriv2`, from the tree's quotient rule."""
    tau = ft_tau(A, r, s)
    t1 = tau_deriv(A, r, s)
    St = sum(d_tau(a, tau, s) for a in A)
    Sa = sum(d_ang(a, tau, s) for a in A)
    dSa = sum(d2_ang_tau(a, tau, s) for a in A) * t1 \
        + sum(d2_ang(a, tau, s) for a in A)
    dSt = sum(d2_tau(a, tau, s) for a in A) * t1 \
        + sum(d2_tau_ang(a, tau, s) for a in A)
    return (-dSa * St - -(Sa - r) * dSt) / St ** 2


# ------------------------------------------------------------------- the split

def pieces(A, r, s):
    """Every quantity the two systems are built from, at one angle."""
    x1 = min(A)
    rho = sum(1 for a in A if a == x1)
    far = [a for a in A if a != x1]
    tau = ft_tau(A, r, s)
    t1 = tau_deriv(A, r, s)
    t2 = tau_deriv2(A, r, s)
    beta = ft_angle(x1, tau, s)
    b = d_tau(x1, tau, s) * t1 + d_ang(x1, tau, s)
    c = (d2_tau(x1, tau, s) * t1 + d2_tau_ang(x1, tau, s)) * t1 \
        + d_tau(x1, tau, s) * t2 \
        + (d2_ang_tau(x1, tau, s) * t1 + d2_ang(x1, tau, s))
    sig = sum((d_tau(a, tau, s) for a in far), mpf(0))
    AF = sum((d_ang(a, tau, s) for a in far), mpf(0))
    dsig = sum((d2_tau(a, tau, s) for a in far), mpf(0)) * t1 \
        + sum((d2_tau_ang(a, tau, s) for a in far), mpf(0))
    dAF = sum((d2_ang_tau(a, tau, s) for a in far), mpf(0)) * t1 \
        + sum((d2_ang(a, tau, s) for a in far), mpf(0))
    sn = sin(beta - s)
    cs = cos(beta - s)
    Delta = tau * cs - x1 * cos(beta)
    R1 = -x1 * sin(beta) * b ** 2 - 2 * t1 * cs * (b - 1) + tau * sn * (b - 1) ** 2
    R2 = -(dsig * t1 + dAF)
    det = sn * mpf(rho) - Delta * sig
    return dict(x1=x1, rho=rho, far=far, tau=tau, t1=t1, t2=t2, beta=beta, b=b,
                c=c, sig=sig, AF=AF, dsig=dsig, dAF=dAF, sn=sn, cs=cs,
                Delta=Delta, R1=R1, R2=R2, det=det)


def predicted(A, r):
    """The closed-form limits the route predicts."""
    x1 = min(A)
    rho = sum(1 for a in A if a == x1)
    far = [a for a in A if a != x1]
    W = sum((x1 / (a - x1) for a in far), mpf(0))
    b0 = (mpf(r) + W) / mpf(rho)
    K = cos(pi / rho)
    S = sin(pi / rho)
    return dict(tau0=x1, t1_0=-x1 * K / S, b0=b0,
                det0=mpf(rho) * S,
                D2=x1 * (1 - 2 * b0) - 2 * x1 * K ** 2 * (b0 - 1) / S ** 2)


# ------------------------------------------------------------------- the pencils

# `(zeros, r, depth)`.  `depth` shifts the angle ladder down: a far zero at
# distance `d` from `x_1` contributes `\sigma \sim a_j\theta/d^2`, so the limit
# only bites at `\theta \ll d^2`.  That is a property of the pencil rather than
# of the route -- the convergence is not uniform in the gap -- and the
# next-to-last pencil is here to exhibit it, not to be avoided.
PENCILS = [
    (["1", "1", "1"], 1, 0),
    (["1", "1", "1"], 2, 0),
    (["1", "1"], 1, 0),
    (["1", "1"], 3, 0),
    (["1", "1", "3"], 1, 0),
    (["1", "1", "3", "7"], 2, 0),
    (["2", "2", "2", "5"], 1, 0),
    (["1", "1", "1", "1"], 1, 0),
    (["1", "1", "1", "1", "4"], 3, 0),
    (["0.5", "0.5", "1.25", "9"], 1, 0),
    (["1", "1", "1.0001"], 1, 28),
    (["3", "3", "3", "3", "3", "10"], 4, 0),
]

PEN = [([mpmathify(a) for a in A], r, d) for A, r, d in PENCILS]


def arc_points(A, r, ks, depth=0):
    """Angles inside `(0, pi/r)`, geometrically approaching the endpoint."""
    top = pi / r
    return [top / mpf(2) ** (k + depth) for k in ks]


# ================================================================= X1
print("X1  the four partials, tree form against the rational chart form")
worst = mpf(0)
for A, r, dep in PEN:
    for s in arc_points(A, r, [1, 2, 4, 7, 11], dep):
        tau = ft_tau(A, r, s)
        for a in set(A):
            for f, g, name in [(d_tau, r_tau, "d_tau"),
                               (d_ang, r_ang, "d_ang"),
                               (d2_tau, r2_tau, "d2_tau"),
                               (d2_ang_tau, r2_mixed, "d2_ang_tau"),
                               (d2_tau_ang, r2_mixed, "d2_tau_ang"),
                               (d2_ang, r2_ang, "d2_ang")]:
                u, v = f(a, tau, s), g(a, tau, s)
                d = fabs(u - v) / max(mpf(1), fabs(v))
                assert d < TOL, f"{name} disagrees at a={a}, tau={tau}, s={s}: {u} vs {v}"
                worst = max(worst, d)
        # the two mixed partials are one function
        for a in set(A):
            d = fabs(d2_ang_tau(a, tau, s) - d2_tau_ang(a, tau, s))
            assert d < TOL * max(mpf(1), fabs(d2_ang_tau(a, tau, s))), \
                f"mixed partials differ at a={a}, s={s}"
print(f"    largest relative disagreement over 12 pencils: {mp.nstr(worst, 5)}")

# ================================================================= X2
print("X2  the two first-order equations, on the arc")
worst = mpf(0)
for A, r, dep in PEN:
    for s in arc_points(A, r, [1, 2, 3, 5, 8], dep):
        p = pieces(A, r, s)
        eA = p["t1"] * p["sn"] + p["b"] * p["Delta"] - p["tau"] * p["cs"]
        eB = p["rho"] * p["b"] + p["sig"] * p["t1"] + p["AF"] - r
        scale = max(mpf(1), fabs(p["t1"]), fabs(p["b"]))
        assert fabs(eA) < TOL * scale, f"(A') fails at {A}, r={r}, s={s}: {eA}"
        assert fabs(eB) < TOL * scale, f"(B') fails at {A}, r={r}, s={s}: {eB}"
        worst = max(worst, fabs(eA) / scale, fabs(eB) / scale)
print(f"    largest residual: {mp.nstr(worst, 5)}")

# ================================================================= X3
print("X3  the two second-order equations, same matrix")
worst = mpf(0)
for A, r, dep in PEN:
    for s in arc_points(A, r, [1, 2, 3, 5, 8], dep):
        p = pieces(A, r, s)
        eA = p["t2"] * p["sn"] + p["c"] * p["Delta"] - p["R1"]
        eB = p["t2"] * p["sig"] + p["rho"] * p["c"] - p["R2"]
        scale = max(mpf(1), fabs(p["t2"]), fabs(p["c"]))
        assert fabs(eA) < TOL * scale, f"(A'') fails at {A}, r={r}, s={s}: {eA}"
        assert fabs(eB) < TOL * scale, f"(B'') fails at {A}, r={r}, s={s}: {eB}"
        worst = max(worst, fabs(eA) / scale, fabs(eB) / scale)
print(f"    largest residual: {mp.nstr(worst, 5)}")

# ================================================================= X4
print("X4  every entry converges, and the determinant stays off zero")
for A, r, dep in PEN:
    pr = predicted(A, r)
    prev = None
    for k in [6, 10, 14, 18]:
        s = (pi / r) / mpf(2) ** (k + dep)
        p = pieces(A, r, s)
        gaps = dict(tau=fabs(p["tau"] - pr["tau0"]),
                    det=fabs(p["det"] - pr["det0"]),
                    t1=fabs(p["t1"] - pr["t1_0"]),
                    b=fabs(p["b"] - pr["b0"]),
                    Delta=fabs(p["Delta"]),
                    sig=fabs(p["sig"]))
        if prev is not None:
            for key, g in gaps.items():
                assert g < prev[key] * mpf("0.7") or g < FLOOR, \
                    f"{key} is not settling at {A}, r={r}: {prev[key]} -> {g}"
        prev = gaps
    assert p["det"] > pr["det0"] / 2 > 0, f"determinant near zero at {A}, r={r}"
    print(f"    {[mp.nstr(a, 8) for a in A]} r={r} rho={p['rho']}: "
          f"|det - {mp.nstr(pr['det0'], 6)}| = {mp.nstr(gaps['det'], 3)}, "
          f"|tau' - {mp.nstr(pr['t1_0'], 6)}| = {mp.nstr(gaps['t1'], 3)}")

# ================================================================= X5
print("X5  tau'' by Cramer, against tau'' measured, against the closed form")
for A, r, dep in PEN:
    pr = predicted(A, r)
    prev = None
    for k in [6, 10, 14, 18]:
        s = (pi / r) / mpf(2) ** (k + dep)
        p = pieces(A, r, s)
        cramer = (p["rho"] * p["R1"] - p["Delta"] * p["R2"]) / p["det"]
        assert fabs(cramer - p["t2"]) < TOL * max(mpf(1), fabs(p["t2"])), \
            f"Cramer disagrees with ftTauDeriv2 at {A}, r={r}, s={s}"
        gap = fabs(p["t2"] - pr["D2"])
        if prev is not None:
            assert gap < prev * mpf("0.7") or gap < FLOOR, \
                f"tau'' is not settling on D2 at {A}, r={r}: {prev} -> {gap}"
        prev = gap
    print(f"    {[mp.nstr(a, 8) for a in A]} r={r}: D2 = {mp.nstr(pr['D2'], 12)}, "
          f"|tau'' - D2| = {mp.nstr(gap, 3)}")

# ================================================================= X6
print("X6  the witness cubic")
A, r = [mpf(1), mpf(1), mpf(1)], 1
pr = predicted(A, r)
assert fabs(pr["D2"] - mpf(7) / 9) < TOL, f"the cubic's D2 is not 7/9: {pr['D2']}"
s = (pi / r) / mpf(2) ** 18
meas = tau_deriv2(A, r, s)
assert fabs(meas - mpf(7) / 9) < mpf(10) ** -4, \
    f"the measured tau'' at theta = pi/2^18 is {meas}, not near 7/9"
# and it is NOT the junk value the definition takes at theta = 0 exactly
assert fabs(mpf(7) / 9) > mpf("0.7"), "7/9 is not near zero"
print(f"    D2 = {mp.nstr(pr['D2'], 20)} = 7/9; measured at pi/2^18: {mp.nstr(meas, 12)}")
print(f"    tau'(0+) = {mp.nstr(pr['t1_0'], 12)} = -cot(pi/3) = {mp.nstr(-cos(pi/3)/sin(pi/3), 12)}")


# ================================================================= X7
print("X7  a route that shares no instrument with the other six")
# X5 compares Cramer against `ftTauDeriv2`, and both are built from the same four
# angle partials -- agreement there tests the algebra, not the answer.  A central
# second difference of `\tau` itself shares nothing with them: it reads the branch
# off the bisection and never touches a partial derivative.
def tau_second_difference(A, r, s, h):
    return (ft_tau(A, r, s + h) - 2 * ft_tau(A, r, s) + ft_tau(A, r, s - h)) / h ** 2


for A, r, dep in PEN[:1] + PEN[4:5] + PEN[7:8]:
    pr = predicted(A, r)
    gaps = []
    for k in [8, 12, 16]:
        s = (pi / r) / mpf(2) ** (k + dep)
        gaps.append(fabs(tau_second_difference(A, r, s, s / 8) - pr["D2"]))
    assert gaps[-1] < gaps[0] / 10, \
        f"the central difference is not settling on D2 at {A}, r={r}: {gaps}"
    print(f"    {[mp.nstr(a, 8) for a in A]} r={r}: D2 = {mp.nstr(pr['D2'], 12)}, "
          f"|central difference - D2| = {[mp.nstr(g, 3) for g in gaps]}")

print()
print("check_endpoint_tau2_limit.py: PASS")
