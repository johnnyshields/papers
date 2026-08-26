#!/usr/bin/env python3
r"""Paper sections `sec:geometry`--`sec:dominance` at a `rho = 1` pencil:
`Q(t) = 1 - 4t + t^2`, `r = 1`, `B(t) = t^2 + 1`.

`thm:weighted-dominance` covers a simple smallest zero, and `SimpleEndpoint`
opened the Lean shape to it.  This is the pencil carried through.  `Q` has zeros
`2 +- sqrt 3`, positive and DISTINCT, so `rho = 1`; and `B` vanishes at `+-i`,
which lie ON the branch, so the witness tests `lem:amplitude-divisor` rather than
sidestepping it the way `B = 1` does.

  (W1) The branch is the unit semicircle: `tau == 1` and `gamma(theta) =
       e^{i theta}` solves `D(.,z) = 0` at `z(theta) = 4 - 2 cos theta`.

  (W2) The amplitude is `W = i cot(theta) e^{i theta}`, so `|W| = |cot theta|`:
       it vanishes on `(0,pi)` exactly at `theta = pi/2` and DIVERGES at both
       endpoints.  With `B = 1` one gets `1/(2 sin theta)` instead, which has no
       zero on the arc at all.

  (W3) Both endpoints are collisions of the principal pair -- `D(.,2) = (t-1)^2`
       and `D(.,6) = (t+1)^2` -- at points that are NOT zeros of `Q`
       (`Q(1) = -2`, `Q(-1) = 6`).  So `k = max{rho,2} = 2` while `rho - 1 = 0`,
       which is `SimpleEndpoint`'s exponent mismatch at this pencil.

  (W4) `D = Q + zt` is QUADRATIC, so the denominator is the principal pair and
       nothing else: `n_0 = n_1 = 0`, and the separating radius may be any
       `R > 1`.  Hence `sigma = tau_max/R = 1/R` does not move with the interior
       parameter -- the fixed-window obstruction of BANK-37 does not arise here,
       and the deleted window is exponentially small.

  (W5) `eq:dominance-bound` off a window of half-width `h/M`, swept to `M = 150`.

A METHOD NOTE, because it reversed a reading here.  `F_M` was first evaluated by
Horner on its coefficient list.  At `M = 60` those coefficients reach `9.2e39`
against an answer of size `1`, and at mpmath's default 40 digits the evaluation
is pure noise -- the sweep reported 2968 violations out of 3001, which looked
exactly like a real failure of the pencil.  Evaluating `F_M` by its own
recurrence at a numeric `z` has no cancellation and reports none.  The cubic
script's Horner route is safe only because it runs at 120 digits against the same
`1e39`; this one is not.  Below, `F_M` is always the recurrence.
"""

import mpmath as mp

mp.mp.dps = 40

Q = lambda t: 1 - 4 * t + t**2
dQ = lambda t: -4 + 2 * t
B = lambda t: t**2 + 1
z = lambda th: 4 - 2 * mp.cos(th)
gam = lambda th: mp.exp(1j * th)
dD = lambda t, zz: dQ(t) + zz


def F(m, zz):
    """`F_M` at a numeric `z`, by the recurrence `F_m = B_m - (z-4)F_{m-1} - F_{m-2}`."""
    bc = [1, 0, 1]
    out = []
    for k in range(m + 1):
        v = bc[k] if k < len(bc) else 0
        if k >= 1:
            v -= (zz - 4) * out[k - 1]
        if k >= 2:
            v -= out[k - 2]
        out.append(v)
    return out[m]


def check_W1():
    print("(W1) the branch: tau == 1, gamma = e^{i theta}, z = 4 - 2 cos theta")
    worst = mp.mpf(0)
    for k in range(1, 400):
        th = mp.pi * k / 400
        worst = max(worst, abs(Q(gam(th)) + z(th) * gam(th)), abs(abs(gam(th)) - 1))
    print(f"      max |D(gamma,z)| and | |gamma| - 1 | = {mp.nstr(worst, 6)}")
    assert worst < mp.mpf("1e-30")
    print(f"      zeros of Q: {mp.nstr(2 - mp.sqrt(3), 12)}, {mp.nstr(2 + mp.sqrt(3), 12)}"
          "  -- distinct and positive, so rho = 1")


def check_W2():
    print("(W2) |W| = |cot theta|, vanishing on the arc only at pi/2")
    worst = mp.mpf(0)
    for k in range(1, 400):
        th = mp.pi * k / 400
        if abs(th - mp.pi / 2) < mp.mpf("1e-9"):
            continue
        W = -B(gam(th)) / dD(gam(th), z(th))
        worst = max(worst, abs(abs(W) - abs(mp.cos(th) / mp.sin(th))))
    print(f"      max | |W| - |cot| | = {mp.nstr(worst, 6)}")
    assert worst < mp.mpf("1e-30")
    for t in ["0.3", "1.5707963267948966", "2.8"]:
        th = mp.mpf(t)
        W = -B(gam(th)) / dD(gam(th), z(th))
        print(f"      theta = {t[:8]:>9}   |W| = {mp.nstr(abs(W), 8)}")
    print("      with B = 1 the amplitude is 1/(2 sin theta) -- no zero on the arc")


def check_W3():
    print("(W3) both endpoints are double collisions, away from the zeros of Q")
    for nm, zz, te in [("lower z=2", mp.mpf(2), mp.mpf(1)),
                       ("upper z=6", mp.mpf(6), mp.mpf(-1))]:
        d0 = abs(Q(te) + zz * te)
        d1 = abs(dD(te, zz))
        print(f"      {nm}: D(t_e) = {mp.nstr(d0, 4)}, d_tD(t_e) = {mp.nstr(d1, 4)}"
              f"   Q(t_e) = {mp.nstr(Q(te), 6)}  (nonzero)")
        assert d0 < mp.mpf("1e-30") and d1 < mp.mpf("1e-30") and abs(Q(te)) > 1
    print("      so k = max{rho,2} = 2, while the binder exponent rho-1 = 0")


def check_W4():
    print("(W4) D is quadratic: the pair is everything, and sigma is constant in e")
    R = mp.mpf(2)
    worst = mp.mpf(0)
    for k in range(1, 400):
        th = mp.pi * k / 400
        for j in range(60):
            t = R * mp.exp(2j * mp.pi * j / 60)
            worst = max(worst, abs(B(t) / (Q(t) + z(th) * t)))
    print(f"      R = 2: max |B/D| on the circle = {mp.nstr(worst, 8)}  (a valid C_0)")
    print("      tau_max/R = 1/2 at every interior parameter e, so the deleted")
    print("      window e^{-(log 2)M/2} shrinks -- unlike cubicTheta's fixed width 1")
    assert worst < 6


def check_W5():
    print("(W5) eq:dominance-bound off a window of half-width h/M, h = 1")
    for m in [10, 20, 40, 60, 100, 150]:
        e = mp.mpf(1) / m
        bad = 0
        n = 3000
        for k in range(n + 1):
            th = e + (mp.pi - 2 * e) * k / n
            if abs(th - mp.pi / 2) < e:
                continue
            W = -B(gam(th)) / dD(gam(th), z(th))
            rem = abs(F(m, z(th)) - 2 * mp.re(W * mp.exp(-1j * (m + 1) * th)))
            if rem > abs(W) / 2:
                bad += 1
        print(f"      M = {m:>4}   h/M = {mp.nstr(e, 5):>9}   violations: {bad}/{n + 1}")
        assert bad == 0


def check_cancellation():
    print("(note) Horner on the coefficient list vs the recurrence, at 40 digits")
    for m in [20, 40, 60]:
        bc = [1, 0, 1]
        qc = [1, -4, 1]
        out = []
        for k in range(m + 1):
            acc = [mp.mpf(0)] * (k + 2)
            acc[0] += bc[k] if k < len(bc) else 0
            for i in range(k):
                j = k - i
                q = qc[j] if j < len(qc) else 0
                for p, c in enumerate(out[i]):
                    acc[p] -= q * c
                if j == 1:
                    for p, c in enumerate(out[i]):
                        acc[p + 1] -= c
            while len(acc) > 1 and acc[-1] == 0:
                acc.pop()
            out.append(acc)
        zz = z(mp.mpf(1))
        s = mp.mpf(0)
        for c in reversed(out[m]):
            s = s * zz + c
        mx = max(abs(c) for c in out[m])
        print(f"      M = {m:>3}  recurrence = {mp.nstr(F(m, zz), 10):>16}"
              f"   horner = {mp.nstr(s, 10):>16}   max|coeff| = {mp.nstr(mx, 4)}")
    print("      the M = 60 Horner value is noise; the sweep above uses the recurrence")
    # A tripwire, not decoration: this asserts the trap is REAL at the working
    # precision.  If someone raises `mp.mp.dps` the assertion fires, and they are
    # sent here to read why the live checks use the recurrence rather than Horner.
    m = 60
    zz = z(mp.mpf(1))
    bc, qc, out = [1, 0, 1], [1, -4, 1], []
    for k in range(m + 1):
        acc = [mp.mpf(0)] * (k + 2)
        acc[0] += bc[k] if k < len(bc) else 0
        for i in range(k):
            j = k - i
            q = qc[j] if j < len(qc) else 0
            for pp, c in enumerate(out[i]):
                acc[pp] -= q * c
            if j == 1:
                for pp, c in enumerate(out[i]):
                    acc[pp + 1] -= c
        while len(acc) > 1 and acc[-1] == 0:
            acc.pop()
        out.append(acc)
    hv = mp.mpf(0)
    for c in reversed(out[m]):
        hv = hv * zz + c
    assert abs(hv - F(m, zz)) > 1, (
        f"Horner and the recurrence now agree at M={m} and dps={mp.mp.dps}. "
        "The precision was raised; re-read this check and decide whether the "
        "live sweeps may use Horner again.")


if __name__ == "__main__":
    check_W1()
    check_W2()
    check_W3()
    check_W4()
    check_W5()
    check_cancellation()
    print("ALL PASS")
