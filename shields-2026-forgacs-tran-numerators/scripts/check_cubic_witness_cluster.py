"""The cubic witness's nonprincipal cluster: nonempty, and `hexp0`'s coefficient.

`hexp0` quantifies over `Fin n_0`, where `n_0` is the size of the retained set with
the principal pair removed.  If `n_0 = 0` the binder is vacuously true and
discharging it certifies nothing.  So this is checked before any reindexing is
built, and then the binder's actual content is checked too.

Pencil: Q(t) = (1-t)^3, r = 1, so D(t,z) = (1-t)^3 + z t.  At the lower endpoint
z = 0 the denominator is (1-t)^3, a triple root at t_a = 1; off the endpoint it
splits into rho = 3 simple roots.

BRANCH SELECTION IS NOT AUTOMATIC.  Writing t = tau e^{i theta}, z is real
exactly when 2 tau^3 cos(theta) = 3 tau^2 - 1, and for small theta that cubic has
TWO positive roots -- one below 1 and one above.  Only the tau < 1 root is the
Forgacs-Tran branch: on it z > 0 and tau IS the minimum modulus, while on the
tau > 1 root z < 0 and the third (real) zero is smaller than the pair, so the
minimum-modulus clause of thm:FT-geometry fails.  Sampling z directly rather than
following the branch picks the wrong one about half the time.

ONE PENCIL, SO ONE rho.  The coefficient checked below is
(cos(pi/rho) - Re omega)/sin(pi/rho), which is rho-dependent, and this witness is
deliberately a single pencil at rho = 3.  Agreement here cannot see a rho-dependence
that happens to evaluate correctly at 3 -- it confirms the supply and `hexp0` agree
at the witness, not that the general coefficient is right.
"""
import math
import sympy as sp

t, x = sp.symbols("t x")


def branch_tau(theta):
    """The Forgacs-Tran root of 2 tau^3 cos(theta) = 3 tau^2 - 1: the one below 1."""
    c = math.cos(theta)
    roots = sp.nroots(sp.Poly(2 * x**3 * c - 3 * x**2 + 1, x))
    pos = [float(sp.re(w)) for w in roots
           if abs(sp.im(w)) < 1e-12 and sp.re(w) > 0]
    below = [w for w in pos if w < 1.0]
    assert below, f"theta={theta}: no branch root below 1 among {pos}"
    return max(below)


# rho = 3, so the cluster directions are omega_j = exp((2j-1) i pi / 3); the
# principal pair is j = 1, 3 and the nonprincipal member is j = 2, omega = -1.
rho = 3
c_pred = (math.cos(math.pi / rho) - (-1.0)) / math.sin(math.pi / rho)
print(f"predicted eq:endpoint-linear-gap coefficient  c = "
      f"(cos(pi/{rho}) - Re omega_2)/sin(pi/{rho}) = {c_pred:.6f}")
print()

print(" delta      tau        z         nonprincipal   |g|/tau    (|g|/tau - 1)/delta")
measured = []
for delta in [0.2, 0.1, 0.05, 0.02, 0.01, 0.005]:
    tau = branch_tau(delta)
    z = 3 - tau**2 - 2 * math.cos(delta) / tau
    roots = [complex(w) for w in sp.nroots(sp.Poly((1 - t) ** 3 + z * t, t))]
    assert len(roots) == 3

    tp = complex(tau * math.cos(delta), tau * math.sin(delta))
    assert min(abs(w - tp) for w in roots) < 1e-6, "t_+ is not a zero"

    pair = [w for w in roots if abs(w.imag) > 1e-9]
    rest = [w for w in roots if abs(w.imag) <= 1e-9]
    assert len(pair) == 2 and len(rest) == 1, f"delta={delta}: {len(pair)}/{len(rest)}"

    # the principal pair must be the minimum-modulus zeros -- thm:FT-geometry
    assert abs(min(abs(w) for w in roots) - tau) < 1e-6, \
        f"delta={delta}: tau={tau:.4f} is not the minimum modulus"

    g = rest[0]
    ratio = abs(g) / tau
    slope = (ratio - 1.0) / delta
    measured.append((delta, slope))
    print(f" {delta:<9} {tau:.6f}  {z:9.6f}   {g.real:9.6f}    {ratio:.6f}   {slope:.6f}")

# n_0 = 1: three zeros, the principal pair is two, one remains
print()
print("n_0 = 3 - 2 = 1 at every sampled delta, and the remaining zero is real,")
print("distinct from the pair, and of LARGER modulus -- so `hexp0` is not vacuous.")

# the slope converges to the predicted coefficient
slopes = [s for _, s in measured]
assert abs(slopes[-1] - c_pred) < 0.02, \
    f"slope {slopes[-1]:.6f} does not approach predicted {c_pred:.6f}"
errs = [abs(s - c_pred) for s in slopes]
assert errs == sorted(errs, reverse=True), f"slope error not decreasing: {errs}"
print(f"and (|g|/tau - 1)/delta -> {c_pred:.6f} monotonically, which is `hexp0`'s")
print("linear term at this pencil.")

print()
print('ALL PASS: check_cubic_witness_cluster')
