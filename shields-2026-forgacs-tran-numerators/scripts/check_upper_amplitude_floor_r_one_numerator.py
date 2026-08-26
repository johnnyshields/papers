r"""Paper section `sec:dominance`, `thm:weighted-dominance`'s `hamp_1` at `r = 1`.

`check_upper_amplitude_floor.py` gives the exponent `p_1 = 1` at `2 <= r`, where the arc
ends at the ORIGIN: `tau -> 0`, the cofactor blows up, and the amplitude vanishes linearly.
`check_upper_amplitude_floor_r_one.py` gives exponent `-1` at `r = 1`, where the arc ends at
a FINITE point: the principal root and its conjugate both run into `-L` on the negative real
axis, `-L` is a double root of `D` in the limit, `D'(-L) = 0`, and the residue `-B(t)/D'(t)`
blows up.

**That second measurement fixes one numerator.**  The standing hypothesis of
`ft_weighted_dominance` is `B(0) != 0`, which says nothing about `B` at `-L`, and `-L` is
where the collision happens at `r = 1`.  So this script asks the question the exponent
actually depends on: does `|W|` still blow up when the numerator VANISHES at the collision
point, and to what order?

Writing `m` for the order of vanishing of `B` at `-L`, the residue is
`|W| ~ |t_+ + L|^m / |D'(t_+)|`.  Both factors are governed by the same separation:
`t_+ = tau(pi - eta) e^{i(pi - eta)}` has `Im t_+ ~ L*eta`, so `|t_+ + L|` is linear in
`eta`, and `D'` has a simple zero at `-L`, so `|D'(t_+)|` is linear too.  The prediction is
therefore an exponent of `m - 1`, NOT a constant `-1`:

    m = 0  (B(-L) != 0)  ->  -1   the amplitude blows up, a constant floor serves
    m = 1                ->   0   the amplitude tends to a nonzero constant
    m = 2                ->  +1   the amplitude vanishes linearly, as at r >= 2

Only the first is what a numerator with `B(0) != 0` alone guarantees, and the third has the
same shape as the `r >= 2` clause for a completely different reason.  A `hamp_1` written at
one fixed exponent is therefore wrong for some admissible `B`; `p_1 = m` is valid for every
`m` (it is above `m - 1` in each case) and is what a general statement must carry.

The branch is never solved for: at each `theta` the script finds `tau` by bisecting the
reality condition `Im(-Q(t)/t^r) = 0` along the ray, which is the branch's own definition.
mpmath at 40 digits.
"""

import mpmath as mp

mp.mp.dps = 40


def q_eval(c, a, t):
    v = mp.mpc(c)
    for ak in a:
        v = v * (mp.mpf(ak) - t)
    return v


def dq_eval(c, a, t):
    """Q'(t) for Q = c * prod (a_k - t), by the product rule."""
    total = mp.mpc(0)
    for j in range(len(a)):
        term = mp.mpc(c)
        for k, ak in enumerate(a):
            term = term * (mp.mpf(-1) if k == j else (mp.mpf(ak) - t))
        total = total + term
    return total


def im_z(c, a, r, tau, theta):
    t = mp.mpf(tau) * mp.exp(1j * mp.mpf(theta))
    return mp.im(-q_eval(c, a, t) / t ** r)


def branch_tau(c, a, r, theta, lo, hi):
    """The branch radius at `theta`: the ray where the spectral parameter is real."""
    flo, fhi = im_z(c, a, r, lo, theta), im_z(c, a, r, hi, theta)
    if flo * fhi > 0:
        return None
    for _ in range(400):
        mid = (lo + hi) / 2
        if flo * im_z(c, a, r, mid, theta) <= 0:
            hi = mid
        else:
            lo, flo = mid, im_z(c, a, r, mid, theta)
    return (lo + hi) / 2


def amp(c, a, r, theta, Lguess, m):
    """|W| at angle `theta`, with numerator B(t) = (t + L)^m."""
    tau = branch_tau(c, a, r, theta, mp.mpf("1e-8"), mp.mpf(max(a)) * 4)
    if tau is None:
        return None, None
    t = tau * mp.exp(1j * mp.mpf(theta))
    z = mp.re(-q_eval(c, a, t) / t ** r)
    dD = dq_eval(c, a, t) + z * r * t ** (r - 1)
    B = (t + Lguess) ** m
    if abs(dD) == 0:
        return None, None
    return abs(-B / dD), tau


PENCILS = [
    ("a=(1,1,2)      rho=2", 1.0, [1.0, 1.0, 2.0]),
    ("a=(1,1,1,2)    rho=3", 1.0, [1.0, 1.0, 1.0, 2.0]),
    ("a=(0.4,0.4,1.7) rho=2", 2.5, [0.4, 0.4, 1.7]),
]

if __name__ == "__main__":
    print("hamp_1 at r = 1: the exponent against the numerator's order at the")
    print("collision point -L.  B(t) = (t + L)^m.  Predicted exponent: m - 1.")
    print()
    failures = []
    for name, c, a in PENCILS:
        # the endpoint radius L, as the limit of the branch radius at theta -> pi
        L = branch_tau(c, a, 1, mp.pi - mp.mpf("1e-12"), mp.mpf("1e-8"), mp.mpf(max(a)) * 4)
        assert L is not None and L > 0, f"{name}: no branch radius at the endpoint"
        print(f"{name}   c = {c}   L = {mp.nstr(L, 8)}")
        for m in (0, 1, 2):
            etas = [mp.mpf(10) ** (-k) for k in (3, 4, 5)]
            vals = []
            for eta in etas:
                W, _ = amp(c, a, 1, mp.pi - eta, L, m)
                assert W is not None, f"{name}: no amplitude at eta={eta}, m={m}"
                vals.append(W)
            # exponent from the two decades
            e1 = mp.log(vals[1] / vals[0]) / mp.log(etas[1] / etas[0])
            e2 = mp.log(vals[2] / vals[1]) / mp.log(etas[2] / etas[1])
            pred = m - 1
            ok = abs(e2 - pred) < mp.mpf("0.01")
            print(f"    m = {m}:  |W| = {mp.nstr(vals[0], 7):>12s} -> "
                  f"{mp.nstr(vals[1], 7):>12s} -> {mp.nstr(vals[2], 7):>12s}"
                  f"   exponent {mp.nstr(e1, 6):>10s}, {mp.nstr(e2, 6):>10s}"
                  f"   predicted {pred}" + ("" if ok else "   <-- MISMATCH"))
            if not ok:
                failures.append((name, m, e2, pred))
        print()

    assert not failures, f"exponent did not match m - 1: {failures}"
    print("The exponent tracks the numerator's order at -L in every row: m - 1, not -1.")
    print("So `hamp_1` at r = 1 cannot be stated at one fixed exponent for every")
    print("admissible B.  `B(0) != 0` is the standing hypothesis and it does not")
    print("constrain B at -L; only m = 0 gives the blow-up that lets a constant floor")
    print("serve.  A general statement carries p_1 = m, which is >= m - 1 for all three.")
    print("\nALL PASS")
