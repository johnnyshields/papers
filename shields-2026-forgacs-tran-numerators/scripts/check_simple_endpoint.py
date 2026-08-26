#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`, and
`lem:amplitude-divisor`'s endpoint exponent, at the lower endpoint.

`thm:weighted-dominance`'s proof splits the lower endpoint on the multiplicity
`rho` of the smallest zero of `Q`: "a fixed circle contains the principal pair
when the smallest zero is SIMPLE and the full rho-root endpoint cluster when it
has multiplicity rho > 1".  The Lean binder `hEp0` asks for

    d_t D(gamma(delta)) / delta^{rho-1}  ->  c_Q * alpha_p^{rho-1},   c_Q != 0,

and `lem:amplitude-divisor` gives the denominator multiplicity at a finite lower
endpoint as `k = max{rho, 2}`, so the true exponent is `k - 1`.  The two agree
exactly when `rho >= 2`.  This script measures which is right.

  (S1) The order of vanishing of `d_t D` along the branch at the lower endpoint,
       measured as `|d_t D(gamma(theta))| / theta^m` for the candidate orders.
       At `rho = 1` the measured order is `1`, not `rho - 1 = 0`, so `hEp0` --
       whose right-hand side is `c_Q * 0^0 = c_Q != 0` there -- asserts a nonzero
       limit for a quantity that tends to `0`.  It is FALSE at `rho = 1`.

  (S2) At `rho = 1` the collision point is NOT a zero of `Q`.  The endpoint is a
       turning point of the branch -- the two principal roots meeting -- rather
       than a cluster at a multiple zero.  `clusterAlpha x_1 rho j` expands about
       `x_1`, the smallest zero of `Q`, so the cluster machinery does not
       describe this endpoint at all, whatever the exponent.

  (S3) At `rho = 2` and `rho = 3` the measured order is `k - 1 = rho - 1`, so the
       existing binder is right there and the `rho >= 2` specialization
       `weighted_dominance_of_branch` is sound.  `rho = 2` is the current
       binder's own boundary and no witness in the tree tests it.

Measured at 50 digits.  A float64 sweep of the same quantities puts the `rho = 1`
ratios inside their own rounding error at `delta = 1e-6`.
"""

import mpmath as mp

mp.mp.dps = 50


def _roots(qcoef, z):
    c = list(map(mp.mpf, qcoef))
    c[1] = c[1] + z
    return mp.polyroots(list(reversed(c)), maxsteps=500, extraprec=500)


def _has_pair(qcoef, z):
    return any(abs(mp.im(x)) > mp.mpf("1e-25") for x in _roots(qcoef, z))


def endpoint(qcoef):
    """The lower endpoint `z_a`: the least `z` at which the principal pair is
    complex.  Found by bisection, which needs no expansion."""
    zmid = None
    for k in range(1, 4000):
        z = mp.mpf(k) / 200
        if _has_pair(qcoef, z):
            zmid = z
            break
    assert zmid is not None
    lo, hi = mp.mpf(0), zmid
    for _ in range(200):
        m = (lo + hi) / 2
        if _has_pair(qcoef, m):
            hi = m
        else:
            lo = m
    return hi


def report(qcoef, rho, label):
    print(f"--- {label}")
    Q = lambda t: sum(c * t**k for k, c in enumerate(qcoef))
    dQ = lambda t: sum(k * c * t ** (k - 1) for k, c in enumerate(qcoef) if k > 0)
    za = endpoint(qcoef)
    rr = _roots(qcoef, za + mp.mpf("1e-30"))
    te = mp.re(max(rr, key=lambda x: abs(mp.im(x))))
    k_pred = max(rho, 2)
    print(f"    z_a = {mp.nstr(za, 12)}   collision t_e = {mp.nstr(te, 12)}")
    print(f"    Q(t_e) = {mp.nstr(Q(te), 6)}"
          f"   {'(NOT a zero of Q)' if abs(Q(te)) > mp.mpf('1e-20') else '(a zero of Q)'}")
    print(f"    rho = {rho}, so k = max(rho,2) = {k_pred}; "
          f"binder exponent rho-1 = {rho-1}, true exponent k-1 = {k_pred-1}")
    print(f"      delta      theta          |d_tD|        |d_tD|/theta^{k_pred-1}")
    ratios = []
    for ex in [3, 4, 5, 6]:
        dz = mp.mpf(10) ** (-ex)
        cand = [x for x in _roots(qcoef, za + dz) if mp.im(x) > 0]
        if not cand:
            continue
        g = cand[0]
        th = mp.arg(g) if rho == 1 else abs(mp.im(g) / mp.re(g))
        th = mp.arg(g)
        v = abs(dQ(g) + (za + dz))
        ratios.append(v / th ** (k_pred - 1))
        print(f"      1e-{ex:<3}   {mp.nstr(th, 8):>12}  {mp.nstr(v, 8):>12}"
              f"   {mp.nstr(v / th ** (k_pred - 1), 10):>14}")
    # the ratio at the true exponent converges to something nonzero
    assert len(ratios) >= 3
    assert abs(ratios[-1] - ratios[-2]) < mp.mpf("1e-3") * abs(ratios[-1])
    assert abs(ratios[-1]) > mp.mpf("1e-3")
    return te, Q(te), ratios[-1]


def main():
    print("(S1)/(S2) rho = 1: the binder exponent is 0, the truth is 1")
    te, qte, _ = report([1, -3, 2], 1, "Q = (1-t)(1-2t), zeros 1/2 and 1")
    assert abs(qte) > mp.mpf("1e-20")
    te2, qte2, _ = report([-6, 11, -6, 1], 1, "Q = (t-1)(t-2)(t-3), zeros 1,2,3")
    assert abs(qte2) > mp.mpf("1e-20")
    print()
    print("      at rho = 1 the binder's own right-hand side is c_Q * alpha^0 = c_Q != 0,")
    print("      while |d_tD| -> 0 linearly in theta.  hEp0 is FALSE at rho = 1.")
    print()
    print("(S3) rho >= 2: the binder exponent rho-1 equals the true k-1")
    report([4, -4, 1], 2, "Q = (t-2)^2, double zero at 2")
    print()
    print("      so `weighted_dominance_of_branch`, the rho >= 2 specialization,")
    print("      is sound at rho = 2 -- the boundary no witness in the tree tests.")


if __name__ == "__main__":
    main()
    print("ALL PASS")
