#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; the `_1` retained
group at `r = 1` and `n >= 4`, `eq:principal-pair`, `eq:ab-def`.

`check_upper_retained_r_one.py` measures the `r = 1` upper retained set at three
`n = 3` pencils, where the pencil's remaining root can be located exactly.  The
retained set now holds at every `n >= 2`, over the separation
`2L < |w|` rather than over that location, and this script measures the same four
facts where the old route does not reach: `n = 4, 5, 6`.

  (R1) At every `delta` on the ladder the closed disk `|t| <= 2L` holds EXACTLY
       two roots of the branch pencil, and they are the principal pair.  That is
       `huniq_1` and `hgcard_1`, and it is where `n_1 = 0` is spent.
  (R2) The pair sits at modulus `tau(pi - delta)`, which stays under `3L/2` and
       tends to `L`.  `tau_max_1 / R_1 = 3/4` is `sigma_1`.
  (R3) Every OTHER root stays strictly outside `2L`.  The assertion is the
       theorem's own bound and nothing more: at `n = 3` the clearance is enormous
       because there is one remaining root at `prod a_k / L^2`, and reading that
       margin as a general fact is the error this script exists to avoid.  From
       `n = 4` the roots outside spread over orders of magnitude, so the MINIMUM
       is what is measured and the margin is reported rather than asserted.
  (R4) `|D'(t_+)|` is nonzero at every `delta > 0` and vanishes LINEARLY as
       `delta -> 0`.  So `hsimple_1` holds on the punctured window and its
       closed-window form is FALSE at every `n`, not only at `n = 3`.  Measured in
       the RATIO rather than against a cutoff: the `n = 3` script's absolute
       threshold is a calibration -- the leading constant runs from `0.28` to
       `1.42` across these four pencils and the `n = 6` one clears `1e-3` by less
       than a factor of two -- and a constant read off one `n` is exactly what
       this file exists to avoid carrying.

Every pencil carries its smallest zero with multiplicity `rho >= 2`, which is the
hypothesis class `ft_weighted_dominance_one` is stated on.
"""

from mpmath import (mp, mpf, mpc, exp, arg, re, im, fabs, pi, log, conj,
                    findroot, polyroots)

mp.dps = 60


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


PENCILS = [([1.0, 1.0, 2.0, 3.0], 1.0, "n=4 a=(1,1,2,3) c=1 rho=2"),
           ([0.5, 0.5, 0.5, 2.0], 2.0, "n=4 a=(0.5,0.5,0.5,2) c=2 rho=3"),
           ([1.0, 1.0, 1.5, 2.0, 4.0], 1.0, "n=5 a=(1,1,1.5,2,4) c=1 rho=2"),
           ([0.8, 0.8, 0.8, 1.6, 2.4, 5.0], 1.5,
            "n=6 a=(0.8,0.8,0.8,1.6,2.4,5) c=1.5 rho=3")]
DELTAS = [mpf(10)**-2, mpf(10)**-3, mpf(10)**-4, mpf(10)**-5]

print("the r = 1 upper retained set at n >= 4: n_1 = 0 on the circle 2L")
print()

counts, taus, others, sims, spreads = [], [], [], [], []

for a, c, lab in PENCILS:
    L = endpoint_L(a)
    Q = qcoeffs(c, a)
    R1 = 2 * L
    print(f"  {lab}")
    print(f"      L {mp.nstr(L,10)}   R_1 = 2L {mp.nstr(R1,8)}   "
          f"tau_max_1 = 3L/2 {mp.nstr(3 * L / 2, 8)}")
    row_n, row_t, row_o, row_d, row_s = [], [], [], [], []
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
        if outside:
            row_s.append(max(fabs(t) for t in outside) / min(fabs(t) for t in outside))
        assert len(inside) == 2, f"{lab}: {len(inside)} roots inside 2L at delta={d}"
        near_p = min(fabs(t - tp) for t in inside)
        near_c = min(fabs(t - conj(tp)) for t in inside)
        assert near_p < mpf(10)**-20 and near_c < mpf(10)**-20, (
            f"{lab}: the two roots inside 2L are not the principal pair at delta={d}")
    counts.append((lab, row_n))
    taus.append((lab, L, row_t))
    others.append((lab, L, row_o))
    spreads.append((lab, max(row_s)))
    slope = (log(row_d[0]) - log(row_d[-1])) / (log(DELTAS[0]) - log(DELTAS[-1]))
    sims.append((lab, row_d, slope))
    print(f"      roots inside 2L {row_n}   tau {'  '.join(mp.nstr(v,7) for v in row_t)}")
    print(f"      nearest root OUTSIDE 2L {'  '.join(mp.nstr(v,7) for v in row_o)}   "
          f"(= {mp.nstr(row_o[-1] / L, 5)} L)")
    print(f"      spread max/min over the {len(a) - 1} roots outside "
          f"{mp.nstr(max(row_s),5)}")
    print(f"      |D'(t_+)| {'  '.join(mp.nstr(v,6) for v in row_d)}   "
          f"log-log slope in delta {mp.nstr(slope,8)}")
    print()

# (R1)
for lab, row in counts:
    assert all(n == 2 for n in row), f"{lab}: counts {row} are not all 2"
print(f"PASS  (R1) at all {len(counts)} pencils with n >= 4 and every delta the "
      f"closed disk |t| <= 2L holds EXACTLY the principal pair -- so huniq_1 and "
      f"hgcard_1 hold with n_1 = 0 at every n, not only at n = 3")

# (R2)
for lab, L, row in taus:
    assert all(t < 3 * L / 2 for t in row), f"{lab}: tau {row} reaches 3L/2"
    assert fabs(row[-1] - L) < mpf(10)**-6, (
        f"{lab}: tau(pi-1e-5) = {mp.nstr(row[-1],8)} has not reached L")
print(f"PASS  (R2) tau stays under tau_max_1 = 3L/2 and tends to L at n >= 4 too, "
      f"so sigma_1 = 3/4 is an n-free constant -- the two block constants come "
      f"off the limit tau -> L, which has no n in it")

# (R3) -- asserted at the theorem's own bound, margin reported not asserted
for lab, L, row in others:
    assert all(v > 2 * L for v in row), (
        f"{lab}: a root sits at {mp.nstr(min(row),6)}, inside 2L")
marg = min(min(row) / L for _, L, row in others)
print(f"PASS  (R3) every root other than the pair stays strictly outside 2L at "
      f"every delta.  The assertion is the theorem's own bound and nothing more.  "
      f"On these pencils the minimum sits at {mp.nstr(marg,5)} L and the spread "
      f"max/min over the outside roots stays at {mp.nstr(max(s for _, s in spreads),5)}, "
      f"so they are not themselves near the circle -- but the spread is unbounded "
      f"over the simplex (check_upper_endpoint_general_n.py (G4)), which is why "
      f"nothing here is asserted at a margin")

# (R4) the negative control
for lab, row, slope in sims:
    assert all(v > 0 for v in row), f"{lab}: |D'(t_+)| vanishes at some delta > 0"
    assert fabs(slope - 1) < mpf(1) / 20, (
        f"{lab}: |D'(t_+)| has log-log slope {mp.nstr(slope,8)} in delta, expected 1")
    # scale-free: the ABSOLUTE size of |D'(t_+)| carries a pencil-dependent
    # constant -- 0.28 at the first pencil and 1.42 at the last -- so a fixed
    # cutoff is an n = 3 calibration rather than a property.  What is a property
    # is that it falls by the ratio of the deltas.
    assert row[-1] / row[0] < 2 * DELTAS[-1] / DELTAS[0], (
        f"{lab}: |D'(t_+)| fell only by {mp.nstr(row[0] / row[-1],6)} while delta "
        f"fell by {mp.nstr(DELTAS[0] / DELTAS[-1],6)}")
print(f"PASS  (R4) hsimple_1 holds at every delta > 0 and |D'(t_+)| vanishes "
      f"LINEARLY as delta -> 0, slope 1 at all {len(sims)} pencils, measured as a "
      f"ratio because the leading constant is pencil-dependent.  The closed-window "
      f"form is FALSE at n >= 4 for the same reason as at n = 3 -- the pair "
      f"collides at the limiting pencil's double root")

print()
print("ALL PASS")
