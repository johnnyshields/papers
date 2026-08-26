#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:FT-geometry`; `eq:lower-cluster-expansion`.

The lower-endpoint cluster is reached in Lean by a Rouche argument against the
MODEL

    M(t) = q(x1) (t - x1)^rho + z0 x1^r delta^rho,     Q = (t - x1)^rho q(t),

whose roots are t = x1 + u with q(x1) u^rho + z0 x1^r delta^rho = 0.  The whole
construction is worth nothing unless those model roots are the cluster
directions of `eq:lower-cluster-expansion`, i.e. unless

    (M1)   q(x1) alpha_j^rho + z0 x1^r = 0,   alpha_j = -x1 omega_j / sin(pi/rho),

at the value of z0 the branch actually has.  That is one scalar identity, it is
the single hypothesis the Lean family lemma names, and it is a SIGN question --
q(x1) carries a factor (-1)^rho from turning prod(a_k - t) into (t - x1)^rho q(t),
and alpha_j^rho carries another from -x1, so the two (-1)^rho have to cancel
against omega_j^rho = -1 and not reinforce.  Nothing in the tree checks it.

Pencil: a = (1,1,1,3), c = 1, r = 1.  So Q(t) = (1-t)^3 (3-t), the smallest zero
x1 = 1 has multiplicity rho = 3, and q(t) = -(3-t) = t - 3 with q(1) = -2.

  (M1) The identity above holds at every j, at
       z0 = c (x1/sin(pi/rho))^rho prod_{k not in S}(a_k - x1) / x1^r.
  (M2) It is not an accident of one pencil: (M1) is re-run over a sweep of
       (rho, r, outside zeros, c).
  (M3) z0 is the branch's own rate, not a constant chosen to make (M1) work:
       the minimum-modulus root of Q + z t^r is followed as z decreases, its
       angle theta read off, and z/theta^rho checked against z0.
  (M4) The Rouche radius keeps the directions apart: with kappa 4 rho <= 1 the
       disks of radius kappa |alpha| delta about x1 + alpha_j delta are pairwise
       disjoint, which is what makes the rho roots produced distinct.
"""

import mpmath as mp

mp.mp.dps = 40


def model_constants(x1, rho, r, outside, c):
    """z0 and q(x1) for Q = c prod(a_k - t), a = x1 (rho times) + outside."""
    sin_r = mp.sin(mp.pi / rho)
    prod_out = mp.mpf(1)
    for a in outside:
        prod_out *= (mp.mpf(a) - x1)
    z0 = c * (x1 / sin_r) ** rho * prod_out / x1 ** r
    # Q = c prod(a_k - t) = (t - x1)^rho * q(t)  ==>  q(t) = (-1)^rho c prod_{out}(a_k - t)
    q_at_x1 = (-1) ** rho * c * prod_out
    return z0, q_at_x1


def alpha(x1, rho, j):
    omega = mp.exp((2 * j - 1) * mp.pi * 1j / rho)
    return -x1 * omega / mp.sin(mp.pi / rho)


# ---------------------------------------------------------------- (M1), (M2)

def check_identity(x1, rho, r, outside, c, tol=mp.mpf("1e-30")):
    z0, q_at_x1 = model_constants(x1, rho, r, outside, c)
    for j in range(1, rho + 1):
        resid = q_at_x1 * alpha(x1, rho, j) ** rho + z0 * x1 ** r
        assert abs(resid) < tol, (
            "(M1) the cluster directions are NOT the model's roots: "
            f"rho={rho} r={r} j={j} residual={resid}"
        )
    return z0, q_at_x1


z0, q1 = check_identity(mp.mpf(1), 3, 1, [3], mp.mpf(1))
print(f"(M1) q(x1) alpha_j^rho + z0 x1^r = 0 at every j; z0 = {mp.nstr(z0, 12)}, "
      f"q(x1) = {mp.nstr(q1, 12)}")

sweep = 0
for rho in (2, 3, 4, 5, 6):
    for r in (1, 2, 3):
        for outside in ([3], [2, 5], [1.5, 4, 9], []):
            for c in (mp.mpf(1), mp.mpf("0.25"), mp.mpf(7)):
                for x1 in (mp.mpf(1), mp.mpf("0.4"), mp.mpf("2.5")):
                    if any(a <= x1 for a in outside):
                        continue
                    check_identity(x1, rho, r, outside, c)
                    sweep += 1
print(f"(M2) the identity survives {sweep} configurations of (rho, r, outside, c, x1)")


# ---------------------------------------------------------------------- (M3)

def pencil_roots(x1, rho, outside, c, r, z):
    """Roots of Q(t) + z t^r with Q = c prod(a_k - t), coefficients high to low."""
    coeffs = [mp.mpf(c)]
    for a in [x1] * rho + list(outside):
        nxt = [mp.mpf(0)] * (len(coeffs) + 1)
        for i, p in enumerate(coeffs):
            nxt[i] += -p          # coefficient of t^(deg-i) * (-t)
            nxt[i + 1] += a * p   # coefficient of t^(deg-i) * a
        coeffs = nxt
    # add z t^r
    deg = len(coeffs) - 1
    coeffs[deg - r] += z
    return mp.polyroots(coeffs, maxsteps=200, extraprec=200)


x1, rho, r, outside, c = mp.mpf(1), 3, 1, [3], mp.mpf(1)
z0_ref, _ = model_constants(x1, rho, r, outside, c)

print("(M3) the branch's own rate, from the minimum-modulus root:")
prev = None
for k in range(1, 9):
    z = mp.mpf(2) ** (-6 * k)
    roots = pencil_roots(x1, rho, outside, c, r, z)
    # the branch point is the MINIMUM-modulus root, and the principal member is
    # the one with negative argument -- not the one of smallest argument.
    tmin = min(roots, key=lambda t: abs(t))
    same = [t for t in roots if abs(abs(t) - abs(tmin)) < mp.mpf("1e-12") * abs(tmin)]
    tp = min(same, key=lambda t: mp.im(t))
    theta = -mp.atan2(mp.im(tp), mp.re(tp))
    ratio = z / theta ** rho
    err = abs(ratio - z0_ref) / z0_ref
    print(f"     z = 2^-{6*k:<3d}  theta = {mp.nstr(theta, 8):<14s} "
          f"z/theta^rho = {mp.nstr(ratio, 12):<18s} rel.err = {mp.nstr(err, 4)}")
    if prev is not None:
        assert err < prev, "(M3) z/theta^rho is not converging to z0"
    prev = err
assert prev < mp.mpf("1e-6"), f"(M3) z/theta^rho did not reach z0: rel.err {prev}"
print(f"     z0 from the geometry = {mp.nstr(z0_ref, 12)} -- the branch rate agrees")


# ---------------------------------------------------------------------- (M4)

print("(M4) the Rouche disks stay apart at kappa 4 rho <= 1:")
for rho in range(2, 13):
    kappa = mp.mpf(1) / (4 * rho)
    x1 = mp.mpf(1)
    amod = x1 / mp.sin(mp.pi / rho)
    sep = min(abs(alpha(x1, rho, j) - alpha(x1, rho, k))
              for j in range(1, rho + 1) for k in range(1, rho + 1) if j != k)
    assert abs(sep - 2 * x1) < mp.mpf("1e-25"), (
        f"(M4) the separation is not 2 x1: rho={rho} sep={sep}")
    assert 2 * kappa * amod < sep, (
        f"(M4) the disks overlap at rho={rho}: 2 kappa |alpha| = {2*kappa*amod} "
        f"vs separation {sep}")
print("     separation is 2 x1 delta for every rho, and 2 kappa |alpha| stays below it")

print()
print("PASS check_cluster_model_roots.py")
