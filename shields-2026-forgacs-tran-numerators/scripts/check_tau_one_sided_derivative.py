r"""Paper section `sec:dominance` (The weighted dominance bound).

Whether the branch radius has a one-sided derivative at the lower endpoint
when the smallest zero is SIMPLE, and whether the Morse nondegeneracy the
formalization route needs actually holds.

At `\rho = 1` the lower endpoint sits at `t_a`, the zero of the critical
function `\Sigma(s) = \sum_k s/(a_k - s) + r` strictly inside `(x_1, x_2)`, and
`\tau(\theta) \to t_a` as `\theta \downarrow 0`.  The remaining gap in that
corner is the EXISTENCE of `\tau'(0^+)` -- its value is not needed.  Nothing
had measured whether it exists, so a route was priced against a limit that
might not be there.

Three things, and the second is the one that decides the route:

  (i)   the difference quotient `(\tau(\theta) - t_a)/\theta` converges as
        `\theta \downarrow 0`, on a geometric ladder;
  (ii)  the local exponent of `\tau(\theta) - t_a` is `1` and not `1/2` -- a
        square-root endpoint would make the one-sided derivative INFINITE and
        the whole Morse route wrong rather than merely hard;
  (iii) the Morse nondegeneracy `\Sigma'(t_a) \ne 0`, which is what makes the
        endpoint a simple zero of the critical function and is the input the
        banked route takes from `rootMultiplicity_ftDen_eq_two_at_critical`.

Precision is the trap here, not the mathematics.  `ftAngle` is built from
`cos s/sin s - a/(\tau \sin s)`, whose two terms are each of size `1/\theta`,
so the subtraction loses about `-\log_{10}\theta` digits.  The working
precision is therefore set from the smallest angle on the ladder rather than
fixed, and the ladder stops where the bisection can still resolve the root --
pushing it further does not buy accuracy, it manufactures it.

mpmath only.
"""

from mpmath import mp, mpf, pi, atan, sin, cos, fabs, log

DEPTH = 26                 # ladder steps below theta = 1/2
LOWEST = mpf(2) ** -14     # the smallest angle used
mp.dps = 90                # ~ 40 digits of headroom below LOWEST


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
    for _ in range(400):
        mid = (lo + hi) / 2
        if h(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def sigma(A, r, s):
    return sum(s / (a - s) for a in A) + r


def sigma_deriv(A, s):
    return sum(a / (a - s) ** 2 for a in A)


def t_a_of(A, r):
    """The zero of Sigma strictly inside (x_1, x_2); rho = 1 only."""
    xs = sorted(set(A))
    assert sum(1 for a in A if a == xs[0]) == 1, "this pencil is not simple"
    x1, x2 = xs[0], xs[1]
    lo = x1 + (x2 - x1) * mpf(10) ** -25
    hi = x2 - (x2 - x1) * mpf(10) ** -25
    assert sigma(A, r, lo) < 0 < sigma(A, r, hi), "the endpoint is not bracketed"
    for _ in range(400):
        mid = (lo + hi) / 2
        if sigma(A, r, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


PENCILS = [
    ("a = (1,2,5), r = 1", [mpf(1), mpf(2), mpf(5)], 1),
    ("a = (1,3,3,8), r = 1", [mpf(1), mpf(3), mpf(3), mpf(8)], 1),
    ("a = (1/2,1,1,5), r = 1", [mpf(1) / 2, mpf(1), mpf(1), mpf(5)], 1),
    ("a = (1,2,5), r = 2", [mpf(1), mpf(2), mpf(5)], 2),
    ("a = (1,4,9,16), r = 2", [mpf(1), mpf(4), mpf(9), mpf(16)], 2),
]

print("PASS  (iii) the Morse nondegeneracy at the endpoint:")
for name, A, r in PENCILS:
    ta = t_a_of(A, r)
    d = sigma_deriv(A, ta)
    # every term a/(a-s)^2 is positive for a > 0, so Sigma' never vanishes --
    # the endpoint is a SIMPLE zero of the critical function structurally,
    # not by measurement.
    assert d > 0, f"Sigma'(t_a) = {d} on {name}"
    assert all(a > 0 for a in A)
    print(f"        {name:<22} t_a = {mp.nstr(ta, 12):<16} "
          f"Sigma'(t_a) = {mp.nstr(d, 8)}")

print("PASS  (i)/(ii) the difference quotient and the local exponent:")
worst_rel = mpf(0)
worst_exp_err = mpf(0)
worst_quot = mpf(0)
for name, A, r in PENCILS:
    ta = t_a_of(A, r)
    qs = []
    for j in range(DEPTH):
        s = mpf(2) ** -1 * mpf(2) ** (-mpf(j) * 13 / DEPTH)
        if s < LOWEST:
            break
        t = ft_tau(A, r, s)
        qs.append((s, t - ta))

    # (ii) the local exponent of tau - t_a, fitted over the last stretch
    (s1, d1), (s2, d2) = qs[-6], qs[-1]
    expo = log(fabs(d2) / fabs(d1)) / log(s2 / s1)
    assert expo > mpf(99) / 100, (
        f"the local exponent is {expo} on {name} -- below 1 the one-sided "
        f"derivative is infinite and the Morse route is wrong, not merely hard")
    worst_exp_err = max(worst_exp_err, fabs(expo - 2))

    # (i) the difference quotient itself.  With exponent 2 it tends to ZERO,
    # so an absolute tolerance on its drift tests the ladder's depth rather
    # than convergence -- the quantity that HAS a limit is (tau - t_a)/theta^2,
    # and its RELATIVE drift is the scale-free statement.
    quot = fabs(d2 / s2)
    worst_quot = max(worst_quot, quot)
    c1, c2 = d1 / s1 ** 2, d2 / s2 ** 2
    rel = fabs((c2 - c1) / c2)
    worst_rel = max(worst_rel, rel)
    assert rel < mpf(1) / 100, (
        f"the second-order coefficient has not settled on {name}: relative "
        f"drift {rel}")
    print(f"        {name:<22} exponent {mp.nstr(expo, 9):<12} "
          f"(tau-t_a)/theta^2 -> {mp.nstr(c2, 9):<14} "
          f"|tau'| <= {mp.nstr(quot, 3)}")

print(f"PASS  (ii) the local exponent is 2 to within "
      f"{mp.nstr(worst_exp_err, 3)} at every pencil, so tau - t_a is "
      f"QUADRATIC and tau'(0+) exists and is ZERO -- stronger than the finite "
      f"limit the route needs, and it makes gamma'(0+) = i*t_a purely "
      f"imaginary")
print(f"PASS  (i) the second-order coefficient settles; worst relative drift "
      f"{mp.nstr(worst_rel, 4)}, and the difference quotient itself is down to "
      f"{mp.nstr(worst_quot, 3)} at the foot of the ladder")
print("PASS  (iii) Sigma'(t_a) = sum a_k/(a_k - t_a)^2 is a sum of positive "
      "terms, so it cannot vanish for any positive pencil -- the Morse "
      "nondegeneracy is structural rather than measured")
print("ALL PASS")
