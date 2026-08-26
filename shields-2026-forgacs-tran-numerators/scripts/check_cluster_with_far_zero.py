#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `thm:FT-geometry` Prop. 3 Case 2;
`sec:dominance`, `thm:weighted-dominance`, `eq:lower-cluster-expansion`.

`check_lower_cluster_expansion.py` tests the lower cluster at `Q = (1-t)^3`,
where the smallest zero has multiplicity 3 and there is nothing else -- the
cluster IS the whole root set.  That is the case where the endpoint block's
`huniq_0` ("every zero in the disk is in the retained set") is trivially true,
because there are no other zeros to account for.

This tests the case the general theorem actually has to handle: a repeated
smallest zero WITH a far zero present, so the cluster is a proper subset and
the local statement (no zero near `x_1` outside the members) and the global one
(no zero in the disk outside the retained set) are genuinely different.

Pencil: `a = (1,1,1,2)`, `c = 1`, `r = 1`, i.e. `Q(t) = (1-t)^3 (1 - t/2)`.
So `x_1 = 1` with `rho = 3`, and a far zero at `t = 2`.

Asserted, each as a failing test:

  (E1) The branch is real and `tau` is the MINIMUM modulus -- the property that
       defines it, and the one a naive root-finder gets wrong.
  (E2) The cluster is a PROPER SUBSET: exactly `rho = 3` roots tend to `x_1 = 1`
       while exactly one stays near `2`.  Without this the pencil would not be
       testing anything the pure-triple case does not.
  (E3) `eq:lower-cluster-expansion` still holds with the far zero present:
       `zeta_j = 1 + [(cos(pi/rho) - omega_j)/sin(pi/rho)] delta + O(delta^2)`,
       residual over `delta^2` bounded.  The far factor perturbs the constant in
       `z(delta) = c delta^rho` but must NOT perturb this coefficient.
  (E4) The local/global separation `huniq_0` needs: the far root's modulus stays
       above `tau` by a ratio bounded away from 1, uniformly as `delta -> 0`, so
       a disk radius exists that contains the cluster and the principal pair and
       excludes it.
  (E5) Teeth: dropping `omega_j` from the coefficient -- keeping only
       `cos(pi/rho)/sin(pi/rho)` -- must break (E3).

`mpmath` throughout: the cluster members separate like `delta` while their
distance from `x_1` is also `O(delta)`, so at `delta = 1e-6` the quantities
being compared agree to six digits before they differ, and float64 would be
reporting cancellation.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 60

I = mp.mpc(0, 1)
A = [mp.mpf(1), mp.mpf(1), mp.mpf(1), mp.mpf(2)]
RHO = 3
X1 = mp.mpf(1)
FAR = mp.mpf(2)


def Qpoly(t):
    out = mp.mpf(1)
    for ak in A:
        out = out * (1 - t / ak)
    return out


def zof(t):
    """`z = -Q(t)/t^r` with `r = 1`."""
    return -Qpoly(t) / t


def branch_tau(theta):
    """Smallest `tau > 0` with `Im z(tau e^{i theta}) = 0`, by bracketed bisection."""
    f = lambda s: mp.im(zof(s * mp.exp(I * theta)))
    lo = mp.mpf(10) ** (-9)
    prev = f(lo)
    steps = 4000
    hi_cap = mp.mpf(4)
    for k in range(1, steps + 1):
        s = lo + (hi_cap - lo) * k / steps
        cur = f(s)
        if prev == 0:
            return lo
        if mp.sign(cur) != mp.sign(prev):
            a, b = lo + (hi_cap - lo) * (k - 1) / steps, s
            for _ in range(250):
                m = (a + b) / 2
                if mp.sign(f(m)) == mp.sign(f(a)):
                    a = m
                else:
                    b = m
            return (a + b) / 2
        prev = cur
        lo = lo  # keep lo fixed; scan is absolute
    raise AssertionError(f"no branch radius found at theta={theta}")


def roots_at(theta):
    tau = branch_tau(theta)
    z = mp.re(zof(tau * mp.exp(I * theta)))
    # D(t,z) = Q(t) + z t ; Q = (1-t)^3 (1 - t/2)
    # expand: (1-t)^3 = 1 -3t +3t^2 - t^3 ; times (1 - t/2)
    q = [mp.mpf(1), mp.mpf(-3), mp.mpf(3), mp.mpf(-1)]
    d = [mp.mpf(0)] * 5
    for i, qi in enumerate(q):
        d[i] += qi
        d[i + 1] += -qi / 2
    d[1] += z
    return tau, z, mp.polyroots(list(reversed(d)), maxsteps=300, extraprec=600)


# ---------------------------------------------------------------------------
# (E1) the branch is real and tau is the minimum modulus
# ---------------------------------------------------------------------------
for th in (mp.mpf(1) / 4, mp.mpf(3) / 4, mp.mpf(6) / 5):
    tau, z, rts = roots_at(th)
    assert mp.fabs(mp.im(zof(tau * mp.exp(I * th)))) < mp.mpf(10) ** (-40), \
        f"z not real at theta={th}"
    mods = sorted(abs(rt) for rt in rts)
    assert mp.fabs(mods[0] - tau) < mp.mpf(10) ** (-30), \
        f"tau={mp.nstr(tau,12)} is not the minimum modulus (min {mp.nstr(mods[0],12)})"
print("PASS  (E1) the branch is real and tau is the minimum modulus at three angles")

# ---------------------------------------------------------------------------
# (E2) the cluster is a proper subset
# ---------------------------------------------------------------------------
for d in (mp.mpf(10) ** (-3), mp.mpf(10) ** (-4), mp.mpf(10) ** (-5)):
    tau, z, rts = roots_at(d)
    near = [rt for rt in rts if abs(rt - X1) < mp.mpf(1) / 10]
    far = [rt for rt in rts if abs(rt - FAR) < mp.mpf(1) / 10]
    assert len(near) == RHO, f"at delta={d}: {len(near)} roots near x_1, expected {RHO}"
    assert len(far) == 1, f"at delta={d}: {len(far)} roots near the far zero, expected 1"
print(f"PASS  (E2) the cluster is a proper subset: exactly {RHO} roots near x_1 = 1 "
      f"and exactly 1 near the far zero t = 2, at delta = 1e-3, 1e-4, 1e-5")


def cluster_omega(j):
    return mp.exp((2 * mp.mpf(j) - 1) * mp.pi / RHO * I)


def predicted_c(j):
    return (mp.cos(mp.pi / RHO) - cluster_omega(j)) / mp.sin(mp.pi / RHO)


def normalized(d):
    tau, z, rts = roots_at(d)
    near = [rt for rt in rts if abs(rt - X1) < mp.mpf(1) / 5]
    return tau, sorted(near, key=lambda w: mp.arg(w)), z


# ---------------------------------------------------------------------------
# (E3) the expansion coefficient survives the far zero
# ---------------------------------------------------------------------------
resid = []
for d in (mp.mpf(10) ** (-3), mp.mpf(10) ** (-4)):
    tau, near, z = normalized(d)
    zetas = sorted((w / tau for w in near), key=lambda w: mp.arg(w))
    cs = sorted((predicted_c(j) for j in range(RHO)), key=lambda w: mp.arg(1 + w * d))
    worst = max(abs((zeta - (1 + c * d))) / d ** 2 for zeta, c in zip(zetas, cs))
    resid.append(worst)
assert max(resid) < 200, (
    f"the O(delta^2) residual is not bounded with a far zero present: "
    f"{[mp.nstr(v,6) for v in resid]}")
assert resid[1] < resid[0] * 20, (
    f"the residual grows faster than delta^2: {[mp.nstr(v,6) for v in resid]}")
print(f"PASS  (E3) eq:lower-cluster-expansion holds with the far zero present; "
      f"|zeta - (1 + c delta)|/delta^2 = {[mp.nstr(v, 5) for v in resid]} at "
      f"delta = 1e-3, 1e-4")

# ---------------------------------------------------------------------------
# (E4) the far root stays separated -- what huniq_0 needs
# ---------------------------------------------------------------------------
ratios = []
for d in (mp.mpf(10) ** (-2), mp.mpf(10) ** (-3), mp.mpf(10) ** (-4), mp.mpf(10) ** (-5)):
    tau, z, rts = roots_at(d)
    far = [rt for rt in rts if abs(rt - FAR) < mp.mpf(1) / 10][0]
    ratios.append(abs(far) / tau)
assert min(ratios) > mp.mpf(3) / 2, (
    f"the far root is not uniformly separated from the branch: {[mp.nstr(v,6) for v in ratios]}")
print(f"PASS  (E4) the far root's modulus ratio to tau stays at "
      f"{[mp.nstr(v, 5) for v in ratios]} as delta -> 0, bounded away from 1, so a "
      f"disk radius separating it from the cluster and the principal pair exists")

# ---------------------------------------------------------------------------
# (E5) teeth -- omega_j is load-bearing in the coefficient
# ---------------------------------------------------------------------------
d = mp.mpf(10) ** (-3)
tau, near, z = normalized(d)
zetas = sorted((w / tau for w in near), key=lambda w: mp.arg(w))
naive = mp.cos(mp.pi / RHO) / mp.sin(mp.pi / RHO)
bad = max(abs(zeta - (1 + naive * d)) / d ** 2 for zeta in zetas)
good = max(abs(zeta - (1 + c * d)) / d ** 2
           for zeta, c in zip(zetas, sorted((predicted_c(j) for j in range(RHO)),
                                            key=lambda w: mp.arg(1 + w * d))))
assert bad > good * 50, (
    f"dropping omega_j barely changes the residual ({mp.nstr(bad,6)} vs "
    f"{mp.nstr(good,6)}); the check cannot see a wrong coefficient")
print(f"PASS  (E5) dropping omega_j takes the residual from {mp.nstr(good, 5)} to "
      f"{mp.nstr(bad, 5)}, so a wrong coefficient fails this")

print("ALL PASS  check_cluster_with_far_zero")
