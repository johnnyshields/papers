r"""Paper section `sec:dominance` (The weighted dominance bound).

Whether `\tau''(0^+)` exists at the lower endpoint -- the one hypothesis the
collar route's stronger form still carries -- and what the angle-collapse rate
behind it is.

`\gamma'' = e^{i\theta}(\tau'' + 2i\tau' - \tau)`, so a one-sided limit for
`\gamma''` at the endpoint is a one-sided limit for `\tau''`.  Only its
EXISTENCE is wanted; the value appears in no conclusion.

`check_tau_one_sided_derivative.py` established that `\tau - t_a` is quadratic
with `(\tau - t_a)/\theta^2` settling.  That is weaker than what is needed:
a function can have a quadratic expansion without its second derivative
converging.  So `\tau''` is measured DIRECTLY here and compared against twice
the second-order coefficient, which is what a genuine limit forces.

Also measured is the sub-statement the collar route would start from: the
angle-collapse rate `\theta_k(\tau,\theta)/\theta` as `\theta \downarrow 0`,
where `\theta_k = \operatorname{arccot}(\cot\theta - a_k/(\tau\sin\theta))`.
Every term of `\tau''`'s implicit formula carries `1/\sin\theta` or
`1/\sin^2\theta` and diverges on its own; the limit survives only through the
joint rate, so whether that rate exists is the question underneath.

Precision is set from the smallest angle: the angle sum subtracts two terms of
size `1/\theta`, losing about `-\log_{10}\theta` digits, and a second
derivative costs more again.

mpmath only.
"""

from mpmath import mp, mpf, pi, atan, sin, cos, fabs, diff, log

mp.dps = 120
LOWEST = mpf(2) ** -12


def ft_arccot(x):
    return pi / 2 - atan(x)


def ft_angle(a, tau, s):
    return ft_arccot(cos(s) / sin(s) - a / (tau * sin(s)))


def ft_angle_sum(A, tau, s):
    return sum(ft_angle(a, tau, s) for a in A)


def ft_tau(A, r, s):
    l = len(A) - 1
    target = r * s + l * pi

    def h(x):
        return ft_angle_sum(A, x, s) - target

    lo, hi = mpf(10) ** -10, mpf(10) ** 10
    assert h(lo) > 0 > h(hi), f"the branch is not bracketed at theta = {s}"
    for _ in range(500):
        mid = (lo + hi) / 2
        if h(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def sigma(A, r, s):
    return sum(s / (a - s) for a in A) + r


def t_a_of(A, r):
    xs = sorted(set(A))
    assert sum(1 for a in A if a == xs[0]) == 1, "this pencil is not simple"
    lo = xs[0] + (xs[1] - xs[0]) * mpf(10) ** -40
    hi = xs[1] - (xs[1] - xs[0]) * mpf(10) ** -40
    assert sigma(A, r, lo) < 0 < sigma(A, r, hi), "the endpoint is not bracketed"
    for _ in range(500):
        mid = (lo + hi) / 2
        if sigma(A, r, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


PENCILS = [
    ("a = (1,2,5), r = 1", [mpf(1), mpf(2), mpf(5)], 1),
    ("a = (1,3,3,8), r = 1", [mpf(1), mpf(3), mpf(3), mpf(8)], 1),
    ("a = (1,2,5), r = 2", [mpf(1), mpf(2), mpf(5)], 2),
    ("a = (1,4,9,16), r = 2", [mpf(1), mpf(4), mpf(9), mpf(16)], 2),
]

print("PASS  tau'' measured directly against twice the quadratic coefficient:")
worst_rel = mpf(0)
worst_agree = mpf(0)
for name, A, r in PENCILS:
    ta = t_a_of(A, r)
    vals = []
    for j in range(5):
        s = LOWEST * mpf(2) ** j
        # An explicit central second difference, NOT mpmath's `diff`.  The
        # branch radius is produced by bisection, so it is a step function at
        # bisection resolution; `diff` picks a step far below that and returns
        # noise -- measured, on the first run of this script, as a relative
        # drift of 1e+239.  Bisection to 500 steps over [1e-10, 1e10] is good
        # to about 1e-141 absolute, so a step of theta/8 leaves the difference
        # dominated by the truncation error rather than by the root-finder.
        h = s / 8
        d2 = (ft_tau(A, r, s + h) - 2 * ft_tau(A, r, s)
              + ft_tau(A, r, s - h)) / h ** 2
        vals.append((s, d2))
    # a genuine one-sided limit settles; relative drift is the scale-free test,
    # since tau'' does NOT tend to zero here.
    rel = fabs((vals[0][1] - vals[2][1]) / vals[0][1])
    worst_rel = max(worst_rel, rel)
    assert rel < mpf(1) / 100, f"tau'' has not settled on {name}: {rel}"
    # and it agrees with 2 * lim (tau - t_a)/theta^2
    s0 = LOWEST
    c2 = (ft_tau(A, r, s0) - ta) / s0 ** 2
    agree = fabs((vals[0][1] - 2 * c2) / (2 * c2))
    worst_agree = max(worst_agree, agree)
    assert agree < mpf(1) / 100, (
        f"tau''({s0}) = {vals[0][1]} against 2*(tau-t_a)/theta^2 = {2 * c2} "
        f"on {name} -- the quadratic coefficient does not match the second "
        f"derivative, so the expansion is not a Taylor expansion")
    # the step must not be doing the work: halve it and the answer must not move
    hA = LOWEST / 8
    hB = LOWEST / 16
    dA = (ft_tau(A, r, LOWEST + hA) - 2 * ft_tau(A, r, LOWEST)
          + ft_tau(A, r, LOWEST - hA)) / hA ** 2
    dB = (ft_tau(A, r, LOWEST + hB) - 2 * ft_tau(A, r, LOWEST)
          + ft_tau(A, r, LOWEST - hB)) / hB ** 2
    assert fabs((dA - dB) / dA) < mpf(1) / 1000, (
        f"halving the difference step moves tau'' by {(dA - dB) / dA} on "
        f"{name} -- the step, not the function, is being measured")
    print(f"        {name:<22} tau''(0+) = {mp.nstr(vals[0][1], 10):<16} "
          f"2*(tau-t_a)/theta^2 = {mp.nstr(2 * c2, 10)}")

print(f"PASS  tau''(0+) EXISTS at every pencil -- relative drift over the last "
      f"three ladder steps at most {mp.nstr(worst_rel, 4)}, and it agrees with "
      f"twice the quadratic coefficient to {mp.nstr(worst_agree, 4)}.  The "
      f"second-order expansion is a Taylor expansion, which the earlier "
      f"quadratic fit alone did not establish")

# --- the angle-collapse rate, the sub-statement underneath -----------------
# The rate SPLITS by position, and there is a closed form for it.  For small
# `theta`, `cot(theta) - a_k/(tau sin theta) ~ (1 - a_k/tau)/theta`, so the
# arccot argument runs to `+infinity` when `a_k < tau` and to `-infinity` when
# `a_k > tau`.  Hence
#
#     a_k < t_a :  theta_k / theta       ->  t_a / (t_a - a_k)
#     a_k > t_a :  (pi - theta_k)/theta  ->  t_a / (a_k - t_a)
#
# and at the lower endpoint `x_1 < t_a < x_2`, so BOTH cases are always
# present.  Measuring one form across all indices reports "not settled" and
# hides the structure -- and getting the direction backwards reports the same
# thing, which is how this block was first written.  Asserting the closed form
# rather than a drift is what distinguishes those two failures.
print("PASS  the angle-collapse rate, split at t_a, against its closed form:")
worst_rate = mpf(0)
for name, A, r in PENCILS:
    ta = t_a_of(A, r)
    s = LOWEST
    tau = ft_tau(A, r, s)
    rows = []
    for a in A:
        th = ft_angle(a, tau, s)
        meas = (th if a < ta else (pi - th)) / s
        pred = ta / fabs(ta - a)
        assert meas > 0, f"a rate is not positive on {name}"
        rel = fabs((meas - pred) / pred)
        worst_rate = max(worst_rate, rel)
        assert rel < mpf(1) / 100, (
            f"rate {meas} against closed form {pred} for a_k = {a} on {name}")
        rows.append(pred)
    below = sum(1 for a in A if a < ta)
    print(f"        {name:<22} {below} index(es) below t_a; limits "
          f"{[mp.nstr(x, 7) for x in rows]}")

print(f"PASS  every rate matches t_a/|t_a - a_k| to within "
      f"{mp.nstr(worst_rate, 4)} -- so the joint rate the divergent terms of "
      f"tau'' survive through is explicit, not merely existent, and it is "
      f"the sub-statement to build the collar's stronger form from")
# --- scope: every pencil above has a SIMPLE smallest zero -----------------
# The closed form `theta_k/theta -> t_a/(t_a - a_k)` divides by `t_a - a_k`,
# and at a REPEATED minimum the collision members have `a_k = t_a` exactly --
# so the denominator is zero on precisely the members whose angle does NOT
# collapse (it tends to pi/2, not to 0 or pi).  Lean's `x/0 = 0` would return
# a finite, plausible rate for each of them.  The scope is asserted rather
# than described, so a later edit that adds a repeated pencil fails here
# instead of reporting a wrong rate.
for name, A, r in PENCILS:
    rho = sum(1 for x in A if x == min(A))
    assert rho == 1, (
        f"{name} has a repeated smallest zero -- the collapse rate's "
        f"denominator vanishes on the collision members and the angles there "
        f"do not collapse; that regime needs its own measurement")
print(f"PASS  scope: all {len(PENCILS)} pencils have a simple smallest zero, "
      f"asserted -- the closed form does not survive a repeated minimum, where "
      f"t_a - a_k is exactly zero on the members that do not collapse")
print("INFO  the SCOPE is the collapse rate's, not the result's: whether "
      "tau''(0+) exists at a repeated minimum is settled elsewhere and "
      "affirmatively -- check_angle_partial_tau_vanishes.py evaluates "
      "ftTauDeriv2 from its four second partials in closed form and finds it "
      "converges at rho = 2 and rho = 3 as well.  That matters because the "
      "tree's own unconditional witness sits at rho = 3, so a rho = 1 family "
      "is the wrong regime for the formalized results and the right one for "
      "the closed form below")

print("ALL PASS")
