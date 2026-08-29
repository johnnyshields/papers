r"""Paper section `sec:geometry` (Forgács--Tran geometry of the viewing arc).

The Lean tree's `PhaseTangency` route leaves one hypothesis on the arc, the
non-vanishing of

    K(theta) = tau^2 + 2 tau'^2 - tau tau''.

`K` cannot be signed pointwise, so the question is what it reduces to.  This
script settles two algebraic reductions symbolically, both identities in the
jet variables rather than facts about any one pencil, so a counterexample here
would be an error in the reduction and not in the geometry.

(1)  With `v = 1/tau`,          K = (v'' + v) / v^3.
     So `K != 0` on the arc is exactly `v'' + v != 0`: the reciprocal radius
     never solves the harmonic equation.  It is NOT a convexity condition on
     `1/tau` -- `(1/tau)''` alone is the wrong expression, and the `tau^2` term
     is what separates them.

(2)  Along the branch, `x1/tau = cos theta - sin theta * cot beta(theta)`
     (`FTBranchLimitPoint.lean:50`, as `cot theta_k = (cos theta - a/tau)/sin theta`).
     Writing `c = cot beta`, this gives

         v'' + v = -(c'' sin theta + 2 c' cos theta) / x1
                 = -(c' sin^2 theta)' / (x1 sin theta).

     So on `(0, pi)`, where `sin theta != 0`, the hypothesis is equivalent to

         (c' sin^2 theta)'  !=  0,

     i.e. `c' sin^2 theta` has no critical point on the arc.  A first-order
     condition on one explicit expression, in place of a second-order sign chase.

Consequence recorded here because it is the reason the hypothesis is not
vacuous: if `beta` were CONSTANT then `c' = 0`, so `v'' + v = 0` identically and
`K` vanishes on the whole arc.  The hypothesis is therefore precisely a
statement that `beta` varies, and any proof of it must consume the structure
that makes `beta` vary -- which is `Im(Q/t^r) = 0`, the arc's own defining
equation.  No pointwise argument can reach it.

Uses sympy only; every claim is an `assert` on a `simplify(...) == 0`.
"""

import sympy as sp

theta, x1 = sp.symbols("theta x1", positive=True)
tau = sp.Function("tau")(theta)
c = sp.Function("c")(theta)

# ---------------------------------------------------------------- reduction 1
K = tau**2 + 2 * sp.diff(tau, theta) ** 2 - tau * sp.diff(tau, theta, 2)

v = 1 / tau
lhs = sp.simplify(K - (sp.diff(v, theta, 2) + v) / v**3)
assert sp.simplify(lhs) == 0, lhs
print("PASS  (1) tau^2 + 2 tau'^2 - tau tau''  =  (v'' + v)/v^3   for v = 1/tau")

# the wrong expression, recorded so the distinction is not re-lost:
# (1/tau)'' alone is NOT proportional to K.
wrong = sp.simplify(K - sp.diff(v, theta, 2) / v**3)
assert sp.simplify(wrong) != 0, "the tau^2 term must separate K from (1/tau)''"
print("PASS  (1a) K is NOT a convexity condition on 1/tau -- the tau^2 term separates them")

# ---------------------------------------------------------------- reduction 2
# v = 1/tau with x1/tau = cos - sin*c, i.e. v = (cos theta - sin theta * c)/x1
v2 = (sp.cos(theta) - sp.sin(theta) * c) / x1

harm = sp.simplify(sp.diff(v2, theta, 2) + v2)
target = -(sp.diff(c, theta, 2) * sp.sin(theta)
           + 2 * sp.diff(c, theta) * sp.cos(theta)) / x1
assert sp.simplify(harm - target) == 0, sp.simplify(harm - target)
print("PASS  (2) v'' + v  =  -(c'' sin + 2 c' cos)/x1   along the branch")

# and that this is one derivative of c' sin^2
divform = -sp.diff(sp.diff(c, theta) * sp.sin(theta) ** 2, theta) / (x1 * sp.sin(theta))
assert sp.simplify(harm - divform) == 0, sp.simplify(harm - divform)
print("PASS  (2a) v'' + v  =  -(c' sin^2 theta)' / (x1 sin theta)")

# ---------------------------------------------------------- non-vacuity check
# beta constant => c' = 0 => K vanishes identically.  This is what makes the
# hypothesis a statement about beta varying.
const_case = sp.simplify(harm.subs(c, sp.Symbol("c0")).doit())
assert const_case == 0, const_case
print("PASS  (3) beta constant  =>  v'' + v = 0 identically, so K vanishes on the whole arc")

print()
print("ALL PASS  check_curvature_reduction")
