r"""Paper section `sec:dominance` (`eq:W-on-g`, the fixed factor of the amplitude).

`cor:linear-phase-variation` bounds the summed phase variation by
`kappa_0 + kappa_1 deg B`, and `thm:main` clause 3 is uniform in the numerator
precisely because NEITHER constant sees `B`.  `kappa_0` is the total variation
of the fixed factor's own angle, and the fixed factor

    V(theta) = -lc(B) / S(theta),        S = cofactor evaluated at the branch,

carries `lc(B)` explicitly.  So `V` depends on `B` and `kappa_0` must not.  This
script settles that the dependence cancels before the variation is taken, which
is the step the Lean tree does NOT currently formalize.

Two claims, both symbolic identities rather than samples:

(1)  dV/V = -S'/S,  identically in `lc(B)`.

     The numerator constant divides out of the logarithmic derivative.  Since
     `psi_0` is a branch of `arg V`, its derivative is `Im(dV/V) = Im(-S'/S)`,
     which contains no `B`.

(2)  Writing `lc(B) = R e^{i phi}` with `R > 0`, any branch of `arg V` differs
     from the corresponding branch of `arg(-1/S)` by the CONSTANT `phi`.
     `eVariationOn` is offset-invariant, so the two have equal total variation.

Together: `kappa_0` may be chosen `B`-free.  The danger this guards is silent --
a supplier who states the `kappa_0` bound with a `B`-dependent constant still
type-checks against `exists_ftPhaseSupply_of_dominance`, and the uniformity of
`thm:main` clause 3 is lost with no elaborator complaint and no failing build.

Uses sympy only; every claim is an `assert` on a `simplify(...) == 0`.
"""

import sympy as sp

theta = sp.symbols("theta", real=True)
R, phi = sp.symbols("R phi", real=True, positive=True)

S = sp.Function("S")(theta)
lc = sp.Symbol("lc")  # leading coefficient of B, an arbitrary nonzero constant

# ------------------------------------------------------------------ claim (1)
V = -lc / S
logderiv = sp.simplify(sp.diff(V, theta) / V)
target = sp.simplify(-sp.diff(S, theta) / S)
assert sp.simplify(logderiv - target) == 0, sp.simplify(logderiv - target)
print("PASS  (1) dV/V = -S'/S   -- the numerator constant divides out")

# it must be free of lc: differentiate the identity w.r.t. lc and get 0
assert sp.simplify(sp.diff(logderiv, lc)) == 0, "dV/V still depends on lc"
print("PASS  (1a) dV/V carries no lc(B), so Im(dV/V) is B-free")

# ------------------------------------------------------------------ claim (2)
# The statement is about CONTINUOUS branches of the argument, so it must not be
# tested with sympy's `arg`, which is the principal branch and jumps.  The
# derivative of any continuous branch of `arg f` is `Im(f'/f)`, so the branch
# question reduces to the log-derivative -- the same reason the tree's
# `PhaseBranchSplit` goes through derivatives rather than a second polar
# decomposition.  Compare `V = -lc/S` against the B-free `V0 = -1/S`.
V0 = -1 / S
d_argV = sp.simplify(sp.im(sp.diff(V, theta) / V))
d_argV0 = sp.simplify(sp.im(sp.diff(V0, theta) / V0))
assert sp.simplify(d_argV - d_argV0) == 0, sp.simplify(d_argV - d_argV0)
print("PASS  (2) any continuous branch of arg V and of arg(-1/S) have the SAME")
print("          derivative, so they differ by a constant and their total")
print("          variations are equal -- kappa_0 may be chosen B-free")

# Numerically, on a concrete nonvanishing S, with the branch UNWRAPPED rather
# than taken principal, at two very different leading coefficients.
import mpmath as mp
mp.mp.dps = 30

def Sf(t):
    return mp.mpf(2) + mp.cos(t) + 1j * (3 + mp.sin(t))

def unwrapped_arg(f, n=4000, T=mp.pi):
    """Continuous branch of arg f on [0, T], by accumulating principal steps."""
    vals, prev, acc = [], None, mp.mpf(0)
    for k in range(n + 1):
        t = T * k / n
        a = mp.arg(f(t))
        if prev is not None:
            d = a - prev
            while d > mp.pi:
                d -= 2 * mp.pi
            while d < -mp.pi:
                d += 2 * mp.pi
            acc += d
        else:
            acc = a
        prev = a
        vals.append(acc)
    return vals

def total_variation(vals):
    return sum(abs(vals[i + 1] - vals[i]) for i in range(len(vals) - 1))

base = unwrapped_arg(lambda t: -1 / Sf(t))
tv_base = total_variation(base)
for lcval in [mp.mpf(1), mp.mpf(10) ** 7, -mp.mpf(3) - 4j, mp.mpf(10) ** -6 * 1j]:
    v = unwrapped_arg(lambda t: -lcval / Sf(t))
    tv = total_variation(v)
    assert abs(tv - tv_base) < mp.mpf(10) ** -20, (lcval, tv, tv_base)
    # and the difference is genuinely constant, not merely equal in variation
    diffs = [v[i] - base[i] for i in range(len(v))]
    assert max(diffs) - min(diffs) < mp.mpf(10) ** -20, (lcval, max(diffs) - min(diffs))
print("PASS  (2a) unwrapped branches at lc(B) spanning 13 orders of magnitude and")
print("          both signs: total variation identical to %.3e, difference constant" % float(tv_base))

# ------------------------------------------------------- the guard that bites
# If someone bounded the variation of |V| instead of its ANGLE, the
# B-dependence would NOT cancel: |V| = |lc|/|S| scales with |lc|.
absV = sp.Abs(-sp.Symbol("R", positive=True) / S)
assert sp.simplify(sp.diff(absV, sp.Symbol("R", positive=True))) != 0
print("PASS  (3) the cancellation is specific to the ANGLE -- |V| scales with")
print("          |lc(B)|, so a modulus-based kappa_0 would NOT be B-free")

print()
print("ALL PASS  check_fixed_factor_b_free")
