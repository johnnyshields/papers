#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; the `_1` retained
group, `eq:principal-pair`, `eq:ab-def`.

The `r = 1` upper retained set at `delta > 0`, which is a different statement from
the limit and is what the block's binders are quantified over.

`check_upper_endpoint_one_limit.py` settles the LIMITING pencil `D_b = Q + bX`:
`-L` has multiplicity exactly 2, and no other root of `D_b` has modulus `<= L`.
That is `theta = pi` and it is not repeated.  The binders `haR_1`, `huniq_1`,
`hroot_1`, `hsimple_1` and `hgcard_1` are `for all delta in (0, e_1]` statements
about the BRANCH pencil, and the facts they need are these:

  (R1) At every `delta` on the ladder the closed disk `|t| <= 2L` holds EXACTLY
       two roots, and they are the principal pair `t_+` and its conjugate.  This
       is `huniq_1` and `hgcard_1` -- the count `2` is what makes the erased set
       empty, i.e. `n_1 = r - 2 = 0`.
  (R2) The pair sits at modulus `tau(pi - delta)`, which stays under `3L/2` with
       margin.  That is the `tau_max_1` the block is stated at, and
       `tau_max_1 / R_1 = 3/4 < 1` is the `sigma_1` the contour argument needs.
  (R3) The third root stays far OUTSIDE `2L` -- not merely outside.  A third root
       drifting toward the circle would leave the count right and the separation
       useless.
  (R4) **The negative control, and the reason the window is punctured.** Both
       members are simple at every `delta > 0`, so `hsimple_1` holds -- but
       `|D'(t_+)|` vanishes LINEARLY as `delta -> 0`, because the pair collides at
       `-L` where `D_b` has its double root.  So the closed-window form of
       `hsimple_1`, at `delta = 0`, is FALSE.  A pass that strengthened the binder
       to the closed window would be proving something untrue, and the same
       collision is what makes `hamp_1`'s amplitude diverge.

mpmath only, 50 digits.  The branch comes from the MONOTONE angle-sum of
`Forgacs2017RationalDenominator` Lemma 2(ii) plus the minimum-modulus test.
"""
from mpmath import (mp, mpf, mpc, exp, pi, arg, findroot, polyroots, im, re,
                    fabs, log, conj)

mp.dps = 50


def qcoeffs(c, a):
    poly = [mpf(c)]
    for ak in a:
        nxt = [mpf(0)] * (len(poly) + 1)
        for i, co in enumerate(poly):
            nxt[i] += co * mpf(ak)
            nxt[i + 1] -= co
        poly = nxt
    return poly[::-1]


def peval(C, t):
    v = mpc(0)
    for co in C:
        v = v * t + co
    return v


def dcoeffs(Q, z, r):
    D = [mpf(0)] * max(0, r + 1 - len(Q)) + list(Q)
    D[len(D) - 1 - r] += z
    while len(D) > 1 and D[0] == 0:
        D = D[1:]
    return D


def deriv(C):
    d = len(C) - 1
    return [C[i] * (d - i) for i in range(d)] if d > 0 else [mpf(0)]


def angle_sum(a, r, theta, tau):
    w = mpc(tau) * exp(mpc(0, 1) * theta)
    return sum(arg(mpc(ak) - w) for ak in a) - r * theta


def branch(c, a, r, theta):
    """Branch radius: monotone angle-sum, then the minimum-modulus test."""
    Q = qcoeffs(c, a)
    lo, hi = mpf(10)**-14, mpf(max(a)) * 4
    Slo, Shi = angle_sum(a, r, theta, lo), angle_sum(a, r, theta, hi)
    cands = []
    for l in range(int(mp.floor(-Slo / pi)) - 1, int(mp.ceil(-Shi / pi)) + 2):
        target = -mpf(l) * pi
        if not (Shi < target < Slo):
            continue
        cands.append(mpf(re(findroot(
            lambda t: angle_sum(a, r, theta, t) - target, (lo, hi),
            solver='bisect', tol=mpf(10)**-40))))
    for tau in sorted(cands):
        w = mpc(tau) * exp(mpc(0, 1) * theta)
        zc = -peval(Q, w) / w**r
        if fabs(im(zc)) > mpf(10)**-25:
            continue
        z = mpf(re(zc))
        rts = polyroots(dcoeffs(Q, z, r), maxsteps=400, extraprec=800)
        if min(fabs(t - w) for t in rts) > mpf(10)**-22:
            continue
        if fabs(fabs(w) - min(fabs(t) for t in rts)) < mpf(10)**-22:
            return tau, z, Q
    raise AssertionError(f"no minimum-modulus branch at theta={theta}, r={r}")


def endpoint_L(a):
    """The `L > 0` of `sum_k L/(a_k+L) = 1`, which is `E(-L) = 0` at `r = 1`."""
    f = lambda L: sum(L / (mpf(ak) + L) for ak in a) - 1
    lo, hi = mpf(10)**-10, mpf(max(a)) * mpf(len(a)) * 8
    assert f(lo) < 0 < f(hi), "the deficit equation does not bracket a root"
    return mpf(re(findroot(f, (lo, hi), solver='bisect', tol=mpf(10)**-45)))


PENCILS = [([1.0, 1.0, 2.0], 1.0, "a=(1,1,2) c=1"),
           ([0.4, 0.4, 1.7], 2.5, "a=(0.4,0.4,1.7) c=2.5"),
           ([1.0, 2.0, 3.0], 1.0, "a=(1,2,3) c=1")]
DELTAS = [mpf(10)**-2, mpf(10)**-3, mpf(10)**-4, mpf(10)**-5]

print("the r = 1 upper retained set at delta > 0: n_1 = 0 on the circle 2L")
print()

counts, taus, thirds, sims = [], [], [], []

for a, c, lab in PENCILS:
    L = endpoint_L(a)
    Q = qcoeffs(c, a)
    R1 = 2 * L
    print(f"  {lab}: L {mp.nstr(L,10)}   R_1 = 2L {mp.nstr(R1,8)}   "
          f"tau_max_1 = 3L/2 {mp.nstr(3 * L / 2, 8)}")
    row_n, row_t, row_o, row_d = [], [], [], []
    for d in DELTAS:
        theta = pi - d
        tau, z, _ = branch(c, a, 1, theta)
        tp = mpc(tau) * exp(mpc(0, 1) * theta)
        Dz = dcoeffs(Q, z, 1)
        rts = polyroots(Dz, maxsteps=400, extraprec=800)
        inside = [t for t in rts if fabs(t) <= R1]
        outside = [t for t in rts if fabs(t) > R1]
        row_n.append(len(inside))
        row_t.append(tau)
        row_o.append(min(fabs(t) for t in outside) if outside else mpf(0))
        row_d.append(fabs(peval(deriv(Dz), tp)))
        # the two inside are the principal pair
        assert len(inside) == 2, f"{lab}: {len(inside)} roots inside 2L at delta={d}"
        near_p = min(fabs(t - tp) for t in inside)
        near_c = min(fabs(t - conj(tp)) for t in inside)
        assert near_p < mpf(10)**-20 and near_c < mpf(10)**-20, (
            f"{lab}: the two roots inside 2L are not the principal pair at delta={d}")
    counts.append((lab, row_n))
    taus.append((lab, L, row_t))
    thirds.append((lab, L, row_o))
    slope = (log(row_d[0]) - log(row_d[-1])) / (log(DELTAS[0]) - log(DELTAS[-1]))
    sims.append((lab, row_d, slope))
    print(f"      roots inside 2L {row_n}   tau {'  '.join(mp.nstr(v,7) for v in row_t)}")
    print(f"      nearest root OUTSIDE 2L {'  '.join(mp.nstr(v,7) for v in row_o)}   "
          f"(= {mp.nstr(row_o[-1] / L, 5)} L)")
    print(f"      |D'(t_+)| {'  '.join(mp.nstr(v,6) for v in row_d)}   "
          f"log-log slope in delta {mp.nstr(slope,8)}")
    print()

# (R1)
for lab, row in counts:
    assert all(n == 2 for n in row), f"{lab}: counts {row} are not all 2"
print(f"PASS  (R1) at all {len(counts)} pencils and every delta the closed disk "
      f"|t| <= 2L holds EXACTLY the principal pair -- so huniq_1 and hgcard_1 hold "
      f"with n_1 = 0, the retained cluster empty")

# (R2)
for lab, L, row in taus:
    assert all(t < 3 * L / 2 for t in row), f"{lab}: tau {row} reaches 3L/2"
    assert fabs(row[-1] - L) < mpf(10)**-8, (
        f"{lab}: tau(pi-1e-5) = {mp.nstr(row[-1],8)} has not reached L")
    assert (3 * L / 2) / (2 * L) < 1, f"{lab}: sigma_1 is not below 1"
print(f"PASS  (R2) tau stays under tau_max_1 = 3L/2 and tends to L, so "
      f"sigma_1 = tau_max_1/R_1 = 3/4 < 1 at every pencil")

# (R3)
for lab, L, row in thirds:
    assert all(v > 3 * L for v in row), (
        f"{lab}: a root sits at {mp.nstr(min(row),6)}, only {mp.nstr(min(row)/L,4)} L "
        f"-- the circle at 2L would have no room")
print(f"PASS  (R3) the third root stays FAR outside 2L at every delta -- not "
      f"merely outside, so the separation has room rather than sitting on the "
      f"circle")

# (R4) the negative control
for lab, row, slope in sims:
    assert all(v > 0 for v in row), f"{lab}: |D'(t_+)| vanishes at some delta > 0"
    assert fabs(slope - 1) < mpf(1) / 20, (
        f"{lab}: |D'(t_+)| has log-log slope {mp.nstr(slope,8)} in delta, expected 1")
    assert row[-1] < mpf(10)**-3, (
        f"{lab}: |D'(t_+)| = {mp.nstr(row[-1],6)} at delta = 1e-5 is not collapsing")
print(f"PASS  (R4) hsimple_1 holds at every delta > 0 -- |D'(t_+)| is nonzero "
      f"throughout -- but it vanishes LINEARLY as delta -> 0, slope 1 at all "
      f"{len(sims)} pencils.  So the CLOSED-window form of hsimple_1 is FALSE, "
      f"and the punctured window is not a convenience.  The same collision is "
      f"what makes hamp_1's amplitude diverge, which is why the two binders "
      f"cannot both be strengthened to delta = 0")

print("INFO  the LIMITING pencil at theta = pi -- multiplicity exactly 2 at -L, "
      "and no other root within L -- is check_upper_endpoint_one_limit.py and is "
      "not repeated")
print()
print("ALL PASS")
