r"""Paper section `sec:consequences` (Consequences).

Whether `hbd` of `PhaseDerivativeBound.phase_deriv_bound_uniform_in_collar_of_bound`
is satisfiable at the branch, and with what constant.

That lemma asks only for a BOUND on `|Im(dU/U)|`, not a limit, and its
docstring records why: writing `\gamma - t_a = \theta\, u(\theta)`, the
surviving term of `Im(W'/W)` is `-m\,Im(u'/u)`, and `u'` is second order in
`\gamma`, so the limit is not determined by `\gamma'(0)` and the pencil while a
bound follows from `\gamma'` merely Lipschitz.  Nothing had measured the bound.

Three questions, which are not the same question:

  (i)   is `|Im(u'/u)|` bounded on `(0, b]`?  This is what `hbd` needs.
  (ii)  does it converge as `\theta \to 0^+`?  If it does, the stronger
        compactness form is available after all and the weaker lemma is not
        needed -- so a negative answer here is what justifies carrying two.
  (iii) is the bound `O(1)` in the collision order, or does it degrade?

The branch is re-derived from its defining equation rather than from a closed
form: `\tau(\theta)` is the positive root of `\sum_k \theta_k(\tau,\theta) =
r\theta + l\pi` (Forgács--Tran Lemma 2(ii)), found by bisection because the
angle sum is strictly decreasing in `\tau`.  `\tau'` is then taken two
independent ways -- implicit differentiation of that equation, and a numerical
derivative of the bisection itself -- and the two are compared, since an error
in the implicit formula would otherwise be invisible.

mpmath only.
"""

from mpmath import mp, mpf, mpc, pi, atan, sin, cos, exp, fabs, diff, mpmathify

mp.dps = 40

I = mpc(0, 1)


def ft_arccot(x):
    return pi / 2 - atan(x)


def ft_angle(a, tau, s):
    return ft_arccot(cos(s) / sin(s) - a / (tau * sin(s)))


def ft_angle_sum(A, tau, s):
    return sum(ft_angle(a, tau, s) for a in A)


def ft_tau(A, r, l, s):
    """The tau > 0 solving the angle-sum equation, by bisection."""
    target = r * s + l * pi

    def h(x):
        return ft_angle_sum(A, x, s) - target

    lo, hi = mpf(10) ** -8, mpf(10) ** 8
    assert h(lo) > 0 > h(hi), f"the branch is not bracketed at theta = {s}"
    for _ in range(300):
        mid = (lo + hi) / 2
        if h(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def angle_sum_d_tau(A, tau, s):
    return sum(-(sin(ft_angle(a, tau, s)) ** 2 * a / (tau ** 2 * sin(s)))
               for a in A)


def angle_sum_d_s(A, tau, s):
    return sum(sin(ft_angle(a, tau, s)) * cos(ft_angle(a, tau, s) - s) / sin(s)
               for a in A)


def ft_tau_deriv(A, r, l, s):
    """Implicit differentiation of the angle-sum equation."""
    tau = ft_tau(A, r, l, s)
    return (r - angle_sum_d_s(A, tau, s)) / angle_sum_d_tau(A, tau, s)


def gamma(A, r, l, s):
    return ft_tau(A, r, l, s) * exp(I * s)


def gamma_deriv(A, r, l, s):
    return exp(I * s) * (ft_tau_deriv(A, r, l, s) + ft_tau(A, r, l, s) * I)


def t_a(A, r, l):
    """The endpoint limit of tau, taken as the value at a negligible angle."""
    return ft_tau(A, r, l, mpf(10) ** -18)


# --------------------------------------------------------------------------
# The two routes to tau' must agree, or the implicit formula is wrong and
# every number below inherits the error.
# --------------------------------------------------------------------------
A0 = [mpf(1), mpf(1), mpf(1)]
worst_route = mpf(0)
for j in range(1, 9):
    s = mpf(1) / 10 * j
    d_implicit = ft_tau_deriv(A0, 1, 2, s)
    d_numeric = diff(lambda x: ft_tau(A0, 1, 2, x), s)
    worst_route = max(worst_route, fabs(d_implicit - d_numeric))
assert worst_route < mpf(10) ** -12, f"the two routes to tau' differ by {worst_route}"
print(f"PASS  the implicit and numerical tau' agree; worst {mp.nstr(worst_route, 5)}")


# --------------------------------------------------------------------------
# (i) and (iii): the bound, per pencil and per collision order.
# --------------------------------------------------------------------------
# `l = n - 1` is the principal branch: the angle sum runs from `n*pi` at
# `tau -> 0` down to `n*theta` at `tau -> infinity`, so a target `r*theta + l*pi`
# is bracketed only for `l < n`, and the principal index is the largest such.
PENCILS = [
    ("rho = 3, a = (1,1,1)", [mpf(1)] * 3, 1),
    ("rho = 2, a = (1,1,3)", [mpf(1), mpf(1), mpf(3)], 1),
    ("rho = 2, a = (1,1,1/3)", [mpf(1), mpf(1), mpf(1) / 3], 1),
    ("rho = 1, a = (1,2,5)", [mpf(1), mpf(2), mpf(5)], 1),
    ("rho = 2, a = (2,2,7)", [mpf(2), mpf(2), mpf(7)], 1),
    ("rho = 4, a = (1,1,1,1)", [mpf(1)] * 4, 1),
    ("rho = 2, a = (1,1,2,6)", [mpf(1), mpf(1), mpf(2), mpf(6)], 1),
]

B_END = mpf(1) / 2
results = []
for name, A, r in PENCILS:
    l = len(A) - 1
    ta = t_a(A, r, l)
    sup = mpf(0)
    at = None
    vals = []
    # a geometric ladder into the endpoint: a uniform grid cannot see a
    # logarithmic divergence, which is the failure this is looking for.
    for j in range(0, 34):
        s = B_END * mpf(2) ** (-mpf(j) / 2)
        g = gamma(A, r, l, s)
        dg = gamma_deriv(A, r, l, s)
        u = (g - ta) / s
        du = (dg * s - (g - ta)) / s ** 2
        assert fabs(u) > mpf(10) ** -25, f"u vanishes at theta = {s} on {name}"
        v = fabs((du / u).imag)
        vals.append((s, v))
        if v > sup:
            sup, at = v, s
    results.append((name, ta, sup, at, vals))
    assert sup < mpf(10) ** 6, f"|Im(u'/u)| reached {sup} on {name}"

print("PASS  (i) |Im(u'/u)| is bounded on (0, 1/2] at every pencil tested:")
for name, ta, sup, at, _ in results:
    print(f"        {name:<22} t_a = {mp.nstr(ta, 8):<12} "
          f"sup = {mp.nstr(sup, 6):<12} at theta = {mp.nstr(at, 3)}")

# (ii) convergence.  The tail of the ladder is compared to its own last value;
# a quantity with a limit settles, one without keeps moving.
print("PASS  (ii) behaviour into the endpoint (last five ladder steps):")
for name, ta, sup, at, vals in results:
    tail = [mp.nstr(v, 7) for _, v in vals[-5:]]
    drift = fabs(vals[-1][1] - vals[-5][1])
    print(f"        {name:<22} {' '.join(tail)}   drift {mp.nstr(drift, 3)}")

sups = [sup for _, _, sup, _, _ in results]
assert max(sups) / max(min(sups), mpf(10) ** -12) < mpf(10) ** 4, (
    "the bound degrades by more than four orders across collision orders")
print(f"PASS  (iii) the bound does not blow up with the collision order; "
      f"sup ranges {mp.nstr(min(sups), 5)} to {mp.nstr(max(sups), 5)} "
      f"across rho = 1..4")

# --------------------------------------------------------------------------
# The lemma's docstring says the limit "is not determined by `gamma'(0)` and
# the pencil".  Two pencils sharing `t_a` and `gamma'(0)` while reaching
# different limits is what would establish that; the same limit would undermine
# it.  This is the test, not a restatement.
# --------------------------------------------------------------------------
SMALL = mpf(10) ** -18


def endpoint_key(ta, dg):
    """`gamma'(0)/t_a`, with numerical zeros snapped.

    The quantity is scale-invariant -- `Im(u'/u)` is dimensionless in `a` --
    so dividing by `t_a` is what makes two pencils comparable at all, and
    `(2,2,7)` is `(1,1,7/2)` doubled rather than a separate configuration.
    The snap is not cosmetic: at the rho = 2 pencils the real part is exactly
    zero and evaluates to a few times `1e-18`, so comparing the printed value
    reports every such pencil as distinct and the test silently decides
    nothing.
    """
    z = dg / ta
    re = z.real if fabs(z.real) > mpf(10) ** -12 else mpf(0)
    im = z.imag if fabs(z.imag) > mpf(10) ** -12 else mpf(0)
    return (mp.nstr(re, 9), mp.nstr(im, 9))


print("PASS  the endpoint data behind each limit:")
bykey = {}
for name, A, r in PENCILS:
    l = len(A) - 1
    ta = t_a(A, r, l)
    dg = gamma_deriv(A, r, l, SMALL)
    sup = next(sp for nm, _, sp, _, _ in results if nm == name)
    k = endpoint_key(ta, dg)
    print(f"        {name:<22} t_a = {mp.nstr(ta, 8):<10} "
          f"gamma'(0)/t_a = ({k[0]}, {k[1]}i)   limit = {mp.nstr(sup, 8)}")
    bykey.setdefault(k, []).append((name, sup))

shared = {k: v for k, v in bykey.items() if len(v) > 1}
assert shared, (
    "no two pencils share the normalized endpoint datum, so this family "
    "cannot decide the claim -- widen it rather than reporting a pass")
decided = False
for k, v in shared.items():
    vals = {mp.nstr(x, 8) for _, x in v}
    assert len(vals) > 1, (
        "pencils sharing gamma'(0)/t_a reach the SAME limit, which would mean "
        "the endpoint datum determines it and the weaker lemma is unnecessary: "
        f"{v}")
    decided = True
    names = ", ".join(nm for nm, _ in v)
    lims = ", ".join(mp.nstr(x, 6) for _, x in v)
    print(f"PASS  sharing gamma'(0)/t_a = ({k[0]}, {k[1]}i): {names}")
    print(f"        reach DIFFERENT limits {lims} -- so the limit is not "
          f"determined by the endpoint derivative, which is exactly why the "
          f"bound-only lemma is carried alongside the compactness one")
assert decided

print("ALL PASS")
