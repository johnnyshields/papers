"""The upper cluster needs r >= 3, and Q = 1 - t with r = 3 is a witness.

`weighted_dominance_of_branch`'s upper-endpoint cluster binders -- hexp1, homega-ne1,
homega-ne'1, hratio1 -- quantify over `Fin n1`, where n1 is the retained set at the
upper endpoint with the principal pair removed.  The upper cluster tends to the
r-th roots of -1 and the principal pair is exp(+-i pi/r), so

    r = 1:  roots {-1},               principal none,     n1 = 0
    r = 2:  roots {+i, -i},           principal both,     n1 = 0
    r = 3:  roots {e^{+-i pi/3}, -1},  principal the pair, n1 = 1

r = 3 is the SMALLEST r whose upper cluster has a nonprincipal member -- exactly as
rho = 3 is the smallest lower cluster with one, and for the same reason.  At r <= 2
every upper cluster binder holds vacuously, which is the position `CubicWitness`'s
header warns about for the quadratic pencil: a witness there would certify nothing
about precisely the binders that were empty.  The cubic witness has r = 1, so the
upper block has never been instantiated non-vacuously anywhere in the tree.

This checks the candidate pencil BEFORE any Lean is written, because at r = 3 the
pencil is chosen rather than inherited and no `hgcard` clause forces n1 from the
outside.
"""
import cmath
import math

import mpmath as mpm
import sympy as sp

t = sp.Symbol("t")
x = sp.Symbol("x", positive=True)

r = 3
Q = 1 - t                      # deg Q = 1, Q(0) = 1 != 0, single positive zero at t = 1
b = math.pi / r                # the upper endpoint of the viewing arc

print(f"pencil Q(t) = 1 - t, r = {r}; upper endpoint b = pi/{r} = {b:.6f}")
print(f"D(t,z) = Q(t) + z t^{r} has degree {sp.Poly(sp.expand(Q + sp.Symbol('z') * t**r), t).degree()}"
      " in t, so the retained set has at most three members.")
print()


def branch(theta):
    """tau on the Forgacs-Tran branch at this angle: the largest positive root of
    Im(-Q(t)/t^r) = 0 along t = tau e^{i theta}."""
    tt = x * (sp.cos(theta) + sp.I * sp.sin(theta))
    g = sp.simplify(sp.im(sp.expand(-Q.subs(t, tt) / tt**r)) * x**r)
    rts = [float(sp.re(s)) for s in sp.nroots(sp.Poly(g, x))
           if abs(sp.im(s)) < 1e-9 and sp.re(s) > 0]
    assert rts, f"theta={theta}: no positive tau"
    return max(rts)


def _order(ws):
    """Sort by real part descending, then by imaginary part -- the conjugate pair
    ties on the real part, so a real-only key orders them arbitrarily."""
    return sorted(ws, key=lambda w: (-round(w.real, 9), w.imag))


cube_roots = _order([cmath.exp(1j * math.pi * (2 * k + 1) / 3) for k in range(3)])
print("cube roots of -1: " + "  ".join(f"{w.real:+.4f}{w.imag:+.4f}j" for w in cube_roots))
print()
print("   eta       tau         z          normalized cluster (roots / tau)"
      "            (|g|/tau - 1)/eta")

slopes = []
for eta in [0.3, 0.2, 0.1, 0.05, 0.02, 0.01]:
    theta = b - eta
    tau = branch(theta)
    tp = tau * cmath.exp(1j * theta)
    z = float(((-(1 - tp)) / tp**r).real)

    roots = [complex(w) for w in sp.nroots(sp.Poly(sp.expand(Q + z * t**r), t))]
    assert len(roots) == 3, f"eta={eta}: {len(roots)} roots"
    assert min(abs(w - tp) for w in roots) < 1e-6, f"eta={eta}: t_+ is not a root"
    assert abs(min(abs(w) for w in roots) - tau) < 1e-6, \
        f"eta={eta}: tau is not the minimum modulus"

    pair = [w for w in roots if abs(w.imag) > 1e-9]
    rest = [w for w in roots if abs(w.imag) <= 1e-9]
    assert len(pair) == 2 and len(rest) == 1, f"eta={eta}: {len(pair)}/{len(rest)}"

    g = rest[0]
    ratio = abs(g) / tau
    slopes.append((eta, (ratio - 1) / eta))
    norm = _order([w / tau for w in roots])
    print(f"  {eta:<9} {tau:.6f}   {z:10.3f}   "
          + "  ".join(f"{w.real:+.4f}{w.imag:+.4f}j" for w in norm)
          + f"   {(ratio - 1) / eta:.6f}")

# n1 = 3 - 2 = 1 at every sampled angle
print()
print("n1 = 3 - 2 = 1 at every sampled eta: three zeros, the principal pair is two,")
print("and the third is real and distinct -- so the upper cluster binders are NOT")
print("vacuous at this pencil.")

# the normalized cluster converges to the cube roots of -1
theta = b - 0.01
tau = branch(theta)
tp = tau * cmath.exp(1j * theta)
z = float(((-(1 - tp)) / tp**r).real)
norm = _order([complex(w) / tau
               for w in sp.nroots(sp.Poly(sp.expand(Q + z * t**r), t))])
for got, want in zip(norm, cube_roots):
    assert abs(got - want) < 0.02, f"normalized cluster {got} != cube root {want}"
print("and the normalized cluster is the cube roots of -1 to within 0.02 at eta = 0.01,")
print("with the nonprincipal member at -1, which is REAL -- so the expansion stays real")
print("exactly as it does at the lower endpoint.")

# the linear coefficient, same formula as the lower endpoint at rho = r = 3
c_pred = (math.cos(math.pi / 3) - (-1.0)) / math.sin(math.pi / 3)
errs = [abs(s - c_pred) for _, s in slopes]
assert errs == sorted(errs, reverse=True), f"slope error not decreasing: {errs}"
assert errs[-1] < 0.01, f"slope {slopes[-1][1]:.6f} not near predicted {c_pred:.6f}"
print()
print(f"(|g|/tau - 1)/eta -> {c_pred:.6f} = (cos(pi/3) - Re(-1))/sin(pi/3) monotonically,")
print("the same coefficient as the lower endpoint because rho = r = 3 there too.")

# ---------------------------------------------------------------------------
# The closed forms, and the factorization that anchors the retained set.
#
# Vieta on 1 - t + z t^3, which has no t^2 term:
#     t+ + t- + t3 = 0        =>  t3 = -2 tau cos(theta)
#     t+ t- t3     = -1/z     =>  z  = 1/(2 tau^3 cos(theta))
# and sin(3th) = sin(th)(4cos^2(th) - 1) against sin(2th) = 2 sin(th) cos(th)
# clears the sine from tau, leaving everything polynomial in cos(theta):
#     tau = (4 cos^2(th) - 1)/(2 cos(th)),   t3 = 1 - 4 cos^2(th)
#
# `upperRootSet` is a DEFINITION in Lean.  What ties it to the pencil is the
# identity below -- without it the four folded binders are met by any
# three-element set of the right shape, and the witness would certify nothing
# about this pencil's own zeros.
#
# mpmath, not float64, and the reason is measured: tau -> 0 as theta -> pi/3, so
# z = 1/(2 tau^3 cos) blows up (about 2.4e7 one milliradian from the endpoint)
# and a float64 residual reads 1e-7 where the identity is exact.  At 40 digits
# the same point returns 1e-36.
mpm.mp.dps = 40


def tau_cos(th):
    return (4 * mpm.cos(th) ** 2 - 1) / (2 * mpm.cos(th))


def third(th):
    return 1 - 4 * mpm.cos(th) ** 2


def zed(th):
    return 1 / (2 * tau_cos(th) ** 3 * mpm.cos(th))


def den(th, w):
    return 1 - w + zed(th) * w ** 3


print()
print("closed forms and the factorization (mpmath, 40 digits)")
print(f"{'theta':>9} {'tau_sin-tau_cos':>17} {'|D(t+)|':>10} {'|D(t3)|':>10}"
      f" {'factor resid':>13} {'min|D-prime|':>13}")

TOL = mpm.mpf('1e-25')
for th_f in (0.05, 0.3, 0.6, 0.9, b - 0.001):
    th = mpm.mpf(repr(th_f))
    tau_c = tau_cos(th)
    tau_sin = mpm.sin(3 * th) / mpm.sin(2 * th)
    assert abs(tau_c - tau_sin) < TOL, f"closed form disagrees at {th_f}"
    assert abs(tau_c - branch(th_f)) < 1e-9, f"closed form disagrees with branch at {th_f}"
    tp = tau_c * mpm.exp(1j * th)
    tb = tau_c * mpm.exp(-1j * th)
    t3 = mpm.mpc(third(th))
    # every retained member is a zero
    for w in (tp, tb, t3):
        assert abs(den(th, w)) < TOL, f"D({w}) != 0 at theta = {th_f}"
    # the factorization, at points that are not zeros
    resid = max(abs(den(th, w) - zed(th) * (w - tp) * (w - tb) * (w - t3))
                for w in (mpm.mpc('0.3', '0.7'), mpm.mpc('-1.2', '0.4'),
                          mpm.mpc('2.1', '-1.5')))
    assert resid < TOL, f"factorization residual {resid} at theta = {th_f}"
    # simplicity: D'(a) = z (a - b)(a - c) at each zero
    dmin = min(abs(zed(th) * (a - u) * (a - v))
               for a, u, v in ((tp, tb, t3), (tb, tp, t3), (t3, tp, tb)))
    assert dmin > mpm.mpf('1e-9'), f"a retained zero is not simple at theta = {th_f}"
    # the radius bound the Lean lemma asserts
    assert max(abs(tp), abs(tb), abs(t3)) < 3, f"a zero escapes radius 3 at {th_f}"
    print(f"{th_f:>9.4f} {float(abs(tau_c - tau_sin)):>17.2e}"
          f" {float(abs(den(th, tp))):>10.2e} {float(abs(den(th, t3))):>10.2e}"
          f" {float(resid):>13.2e} {float(dmin):>13.6f}")

print()
print("tau = (4cos^2 - 1)/(2cos) agrees with sin(3th)/sin(2th), the three closed-form")
print("zeros satisfy D = 0, and 1 - t + z t^3 = z(t - t+)(t - t-)(t - t3) identically.")
print("Every zero is simple and every one has modulus < 3, so the retained set is the")
print("pencil's own -- hroot1, huniq1, hsimple1 and haR1, not just a set of the right")
print("shape.")

print()
print('ALL PASS: check_upper_cluster_witness')
