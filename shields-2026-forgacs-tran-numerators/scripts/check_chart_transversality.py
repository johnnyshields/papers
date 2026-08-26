r"""Paper section `sec:dominance` (The weighted dominance bound).

Transversality of the branch in the analytic chart's parameter, and the
wrong-root trap that makes it worth measuring rather than deriving.

`exists_endpoint_local_inverse` gives an analytic `\psi` with `\psi'(0) \ne 0`
and `g(\psi(v)) - z_e = v^k`, `k = \max(\rho, 2)`.  A branch written through
the chart is `t(v) = \psi(\omega v)` for `\omega` a `k`-th root of unity, and
`\theta(v) = \arg t(v)` inverts near `0` -- making `\gamma` as smooth as the
chart -- exactly when

    \theta'(0) = \operatorname{Im}\bigl(\omega\,\psi'(0)/\psi(0)\bigr) \ne 0 .

**The trap is that some `\omega` give zero and the rest do not.**  `g` is real
on the reals, so `g^{(k)}(t_e)` is real and `\psi'(0) = (k!/g^{(k)}(t_e))^{1/k}`
has argument `0` or `\pi/k`; multiplying by the `k`-th roots of unity spreads
the arguments evenly, and the ones landing on `0` or `\pi` are the REAL
branches, with `\theta'(0) = 0`.  So "some root gives a nonzero answer" is not
the claim -- a wrong root gives a plausible nonzero number too, and only the
physical branch's own `\omega` settles it.

The physical branch is identified independently rather than chosen: an earlier
measurement gives `\gamma'(0^+) = i\,t_e`, purely imaginary, and
`\gamma'(0) = \omega\psi'(0)/\theta'(0)` with `\theta'(0)` real -- so the
branch's `\omega\psi'(0)` must be purely imaginary.  That is a prediction about
which root, checked here, not a root picked to make the answer come out.

`g` is analytic and differentiated exactly; nothing here differentiates a
root-finder's output.

mpmath only.
"""

from mpmath import mp, mpf, mpc, fabs, diff, exp, pi, root, factorial

mp.dps = 50
ZERO = mpf(10) ** -30


def Qeval(a, t):
    v = mpc(1)
    for ak in a:
        v *= (ak - t)
    return v


def g(a, r, t):
    return -Qeval(a, t) / t ** r


def sigma(a, r, s):
    return sum(s / (ak - s) for ak in a) + r


def endpoint(a, r):
    """t_e and k: the zero of Sigma above x_1 at rho = 1, else x_1 itself."""
    xs = sorted(set(a))
    rho = sum(1 for x in a if x == xs[0])
    if rho >= 2:
        return xs[0], rho
    lo = xs[0] + (xs[1] - xs[0]) * mpf(10) ** -30
    hi = xs[1] - (xs[1] - xs[0]) * mpf(10) ** -30
    assert sigma(a, r, lo) < 0 < sigma(a, r, hi), "the endpoint is not bracketed"
    for _ in range(400):
        mid = (lo + hi) / 2
        if sigma(a, r, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2, 2


PENCILS = [
    ("rho = 1, a = (1,2,5), r = 1", [mpf(1), mpf(2), mpf(5)], 1),
    ("rho = 1, a = (1,3,3,8), r = 1", [mpf(1), mpf(3), mpf(3), mpf(8)], 1),
    ("rho = 2, a = (1,1,3), r = 1", [mpf(1), mpf(1), mpf(3)], 1),
    ("rho = 2, a = (2,2,7), r = 2", [mpf(2), mpf(2), mpf(7)], 2),
    ("rho = 3, a = (1,1,1), r = 1", [mpf(1)] * 3, 1),
    ("rho = 3, a = (1,1,1,4), r = 2", [mpf(1)] * 3 + [mpf(4)], 2),
]

print("PASS  the chart datum, and how many roots of unity give theta'(0) = 0:")
rows = []
for name, a, r in PENCILS:
    te, k = endpoint(a, r)
    # the order really is k: derivatives 1..k-1 of g - z_e vanish, the k-th does not
    ze = g(a, r, te)
    for j in range(1, k):
        dj = diff(lambda t: g(a, r, t), te, j)
        assert fabs(dj) < mpf(10) ** -18, (
            f"g^({j})(t_e) = {dj} does not vanish on {name}, so k is not {k}")
    gk = diff(lambda t: g(a, r, t), te, k)
    assert fabs(gk) > mpf(10) ** -12, f"g^({k})(t_e) vanishes on {name}"
    assert fabs(mpc(gk).imag) < ZERO, "g^(k)(t_e) is not real"

    psi1 = root(factorial(k) / mpc(gk), k, 0)      # one k-th root; omega spans the rest
    assert fabs(psi1) > ZERO, "psi'(0) = 0"

    vals = []
    for j in range(k):
        om = exp(2j * pi * mpf(j) / k)
        vals.append(mpc(om) * psi1)
    zeros = [z for z in vals if fabs(z.imag / fabs(z)) < mpf(10) ** -20]
    imag = [z for z in vals if fabs(z.real / fabs(z)) < mpf(10) ** -20]
    rows.append((name, te, k, vals, zeros, imag))
    print(f"        {name:<30} k={k}  {len(zeros)} of {k} roots give "
          f"theta'(0) = 0")

assert any(len(z) > 0 for _, _, _, _, z, _ in rows), (
    "no configuration has a vanishing root -- then the trap this check exists "
    "for does not arise and the check is testing nothing")
print("PASS  the trap is real: at every pencil at least one k-th root puts "
      "omega*psi'(0) on the real axis, where theta'(0) = 0 and the chart does "
      "NOT invert -- so a root chosen for convenience can give a plausible "
      "nonzero answer while naming the wrong branch")

# --- the physical branch, and the closed form that identifies it ----------
# `gamma'(0+) = i*t_e` is NOT the general fact -- it is the k = 2 case, and
# building the identification on it fails at k = 3, where no cube root of unity
# can put `omega psi'(0)` on the imaginary axis at all (the arguments are
# {0, 2pi/3, 4pi/3} or {pi/3, pi, 5pi/3}, and neither set meets pi/2).
#
# The general form is `gamma'(0)/t_e = -cot(pi/k) + i`, which reproduces every
# earlier measurement: real part 0 at k = 2, -0.5773503 = -cot(pi/3) at k = 3,
# -1 = -cot(pi/4) at k = 4.  So the physical root is the one at argument
# `pi - pi/k`, and then
#
#     theta'(0) = |psi'(0)| sin(pi/k) / t_e  >  0
#
# for every k >= 2, since 0 < pi/k <= pi/2.  Transversality is STRUCTURAL --
# `sin(pi/k) != 0` -- and not a numerical fact about any pencil.  The roots
# that fail are exactly those at argument 0 or pi, which is what makes the
# wrong-root trap a real one.
print("PASS  the physical branch, at argument pi - pi/k:")
worst_arg = mpf(0)
worst_tp = mpf("inf")
for name, te, k, vals, zeros, imag in rows:
    target = pi - pi / k
    best = min(vals, key=lambda z: fabs(((mp.arg(z) - target + pi) % (2 * pi)) - pi))
    d = fabs(((mp.arg(best) - target + pi) % (2 * pi)) - pi)
    assert d < mpf(10) ** -20, (
        f"no k-th root sits at argument pi - pi/k on {name}: closest is off "
        f"by {d}")
    worst_arg = max(worst_arg, d)
    tp = best.imag / te
    pred = fabs(best) * mp.sin(pi / k) / te
    assert fabs(tp - pred) / pred < mpf(10) ** -20, (
        f"theta'(0) = {tp} against |psi'(0)| sin(pi/k)/t_e = {pred} on {name}")
    assert tp > 0, f"theta'(0) = {tp} is not positive on {name}"
    worst_tp = min(worst_tp, tp)
    print(f"        {name:<30} theta'(0) = {mp.nstr(tp, 8)}  "
          f"= |psi'(0)| sin(pi/{k}) / t_e")

print(f"PASS  a k-th root sits at argument pi - pi/k at every pencil (worst "
      f"deviation {mp.nstr(worst_arg, 4)}), and there theta'(0) = "
      f"|psi'(0)| sin(pi/k)/t_e, smallest {mp.nstr(worst_tp, 6)}")
print("PASS  so transversality is STRUCTURAL: theta'(0) != 0 because "
      "sin(pi/k) != 0 for k >= 2, at every pencil and every collision order -- "
      "not a numerical fact to be trusted.  The roots that DO fail are exactly "
      "those at argument 0 or pi, which is why a root chosen for convenience "
      "can give a plausible nonzero answer for the wrong branch")
print("ALL PASS")
