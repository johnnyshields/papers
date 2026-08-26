#!/usr/bin/env python3
r"""Paper sections `sec:reduction` and `subsec:proof`, `thm:main` clauses 1--3,
at `Q(t) = (1-t)^3`, `r = 1`, `B(t) = 3t^2 + 1`.

The four numbers the Lean route to `thm:main` at this pencil rests on, checked
at the real coefficient sequence rather than assumed.  `F_M` is built from the
`prop:initial-data` recurrence

    F_M = B_M - (z-3) F_{M-1} - 3 F_{M-2} + F_{M-3},

which is `Q + zt` with `Q = (1-t)^3` written out.

  (D0) The working precision is adequate for the largest coefficient in play,
       and the two independent evaluation routes -- the defining recurrence and
       Horner on the coefficient list -- agree.  `F_M`'s coefficients reach
       `1.4e39` while its values are `O(1e15)`, so Horner burns about 25 of the
       120 working digits; at 40 digits it is pure noise, and the noise looks
       exactly like the pencil failing.  Every evaluation below uses the
       recurrence; Horner is kept only as the cross-check.

  (D1) `deg F_M = M`, with leading coefficient `(-1)^M`.  This is what makes an
       interior-zero count *mean* something: the count has to be compared with a
       degree that grows, and `Bridge.ftInputsWitness` -- whose `coeffPoly` is
       the constant `1` -- has no such comparison to make.

  (D2) All `M` zeros of `F_M` are real and lie in `I_{Q,1} = (0, 27/4)`, counted
       by sign changes at 120 digits.  A float64 `numpy.roots` on the same
       polynomials reports 15 of 40 and 18 of 80, which is the conditioning of a
       degree-80 polynomial and not the mathematics -- recorded here because it
       is exactly the kind of measurement that would have been believed.

  (D3) `eq:dominance-bound` holds on the WHOLE retained range of
       `eq:retained-range` when every deleted window -- the two endpoint windows
       and the amplitude window about `theta = pi/2` -- has half-width `h/M`
       with `h = 1`.  This is `CubicMain.CubicShrinkingWindow`, measured here
       before it was proved -- a hypothesis on a FALSE statement would have been
       worse than a named gap.  It is now the theorem
       `CubicMain.cubic_shrinkingWindow`, so this check is corroboration rather
       than the only evidence.

  (D4) The observed dominance window is far narrower than `h/M`: dominance
       already holds at `|theta - pi/2| = 5e-5` at every `M` sampled, which is
       the simple zero of the amplitude against a geometrically small remainder.
       The `1/M` rate of (D3) is therefore not tight -- it is the rate the paper
       uses, and any rate tending to `0` would do.

Two counts live in the Lean tree, and (D2) is the reason the weaker one is kept.
`cubic_interior_zero_count` runs off `cubicTheta`'s FIXED half-width `1`, where
the two retained components carry only `(pi-2)/pi` of the arc, so the count is
`~0.363 M`; it states the round `M/4` below that.  `cubic_bulk_count` runs off
the shrinking window of (D3) and gets `M - C`.  (D2) says the truth is `M`, so
both are honest lower bounds and neither is tight.
"""

import mpmath as mp

mp.mp.dps = 120


def f_coeffs(mmax):
    """`F_M` as coefficients in `z`, index = power, from the recurrence."""
    bcoef = [1, 0, 3]
    qcoef = [1, -3, 3, -1]
    out = []
    for m in range(mmax + 1):
        acc = [mp.mpf(0)] * (m + 2)
        acc[0] += bcoef[m] if m < len(bcoef) else 0
        for i in range(m):
            j = m - i
            q = qcoef[j] if j < len(qcoef) else 0
            for k, c in enumerate(out[i]):
                acc[k] -= q * c
            if j == 1:
                for k, c in enumerate(out[i]):
                    acc[k + 1] -= c
        while len(acc) > 1 and acc[-1] == 0:
            acc.pop()
        out.append(acc)
    return out


def tau(th):
    return 1 / (2 * mp.cos((mp.pi - th) / 3))


def gamma(th):
    return tau(th) * mp.exp(1j * th)


def amp(th):
    g = gamma(th)
    return g * (3 * g**2 + 1) / ((1 - g) ** 2 * (2 * g + 1))


def zof(th):
    t = tau(th)
    return 3 - t**2 - 2 * mp.cos(th) / t


def horner(coeffs, z):
    s = mp.mpf(0)
    for c in reversed(coeffs):
        s = s * z + c
    return s


def f_direct(m, zz):
    """`F_M` at a numeric `z`, by the defining recurrence

        F_m = B_m - (z-3) F_{m-1} - 3 F_{m-2} + F_{m-3},

    which is `Q + zt` with `Q = (1-t)^3` written out.  No cancellation: every
    intermediate is the size of the answer, not the size of a coefficient."""
    bcoef = [1, 0, 3]
    out = []
    for k in range(m + 1):
        v = mp.mpf(bcoef[k] if k < len(bcoef) else 0)
        if k >= 1:
            v -= (zz - 3) * out[k - 1]
        if k >= 2:
            v -= 3 * out[k - 2]
        if k >= 3:
            v += out[k - 3]
        out.append(v)
    return out[m]


FS = f_coeffs(80)

# Digits that must survive the worst cancellation a Horner pass can suffer.
# The loss is about `log10(max|coeff| / |answer|)`; the answers here are `O(1)`
# to `O(1e15)`, so `log10(max|coeff|)` is the conservative estimate.
PRECISION_MARGIN = 40


def precision_margin(coeffs):
    """Decimal digits left after that loss, at the current working precision."""
    mx = max(abs(c) for c in coeffs)
    return mp.mp.dps - (float(mp.log10(mx)) if mx > 0 else 0.0)


def check_precision():
    """**Why this check exists.**  `F_M`'s coefficients reach `1.4e39` at `M = 80`
    while its values on `I` are `O(1e15)`, so a Horner pass burns about 25 of the
    120 working digits.  At mpmath's default 40 digits the same evaluation is
    pure noise -- and it does not look like noise: on the sibling pencil of
    `check_simple_witness.py` it reported 2968 dominance violations out of 3001,
    which is indistinguishable from the pencil failing.

    So: every `F_M` here is evaluated by `f_direct`, which cannot cancel; the
    Horner route is kept and cross-checked against it; and the working precision
    is asserted adequate, so that adding a pencil with larger coefficients fails
    loudly instead of quietly."""
    print("(D0) precision is adequate, and the two evaluation routes agree")
    worst = None
    for m in [10, 20, 40, 80]:
        margin = precision_margin(FS[m])
        mx = max(abs(c) for c in FS[m])
        if worst is None or margin < worst[1]:
            worst = (m, margin)
        print(f"      M = {m:>3}   max|coeff| = {mp.nstr(mx, 4):>10}"
              f"   digits left = {margin:6.1f}  (need {PRECISION_MARGIN})")
        assert margin >= PRECISION_MARGIN, (
            f"working precision {mp.mp.dps} is inadequate at M={m}: "
            f"max|coeff| = {mp.nstr(mx, 4)} leaves only {margin:.1f} digits. "
            f"Raise mp.mp.dps or drop the Horner cross-check.")
    print(f"      tightest margin: M = {worst[0]} with {worst[1]:.1f} digits")
    # the two independent routes must converge
    worst_rel = mp.mpf(0)
    for m in [10, 20, 40, 80]:
        for k in range(1, 8):
            zz = mp.mpf(27) / 4 * k / 8
            a = f_direct(m, zz)
            b = horner(FS[m], zz)
            worst_rel = max(worst_rel, abs(a - b) / max(abs(a), mp.mpf(1)))
    print(f"      max relative disagreement, recurrence vs Horner: "
          f"{mp.nstr(worst_rel, 5)}")
    assert worst_rel < mp.mpf("1e-60")


def check_D1():
    print("(D1) deg F_M = M, leading coefficient (-1)^M")
    for m in [0, 1, 5, 20, 50, 80]:
        deg = len(FS[m]) - 1
        lead = FS[m][-1]
        print(f"      M = {m:>3}   deg = {deg:>3}   lead = {mp.nstr(lead, 4)}")
        assert deg == m
        assert lead == (-1) ** m


def check_D2():
    print("(D2) all M zeros of F_M are real and lie in I = (0, 27/4)")
    for m in [10, 20, 40, 80]:
        n = 200000
        prev = None
        changes = 0
        for k in range(1, n):
            v = f_direct(m, mp.mpf(27) / 4 * k / n)
            s = mp.sign(v)
            if prev is not None and s != 0 and prev != 0 and s != prev:
                changes += 1
            prev = s
        print(f"      M = {m:>3}   sign changes in I: {changes}   deg = {m}"
              f"   (Lean states M/4 = {m / 4:.1f})")
        assert changes == m


def remainder(m, th):
    t = tau(th)
    principal = 2 * mp.re(amp(th) * mp.exp(-1j * (m + 1) * th))
    return abs(t ** (m + 1) * f_direct(m, zof(th)) - principal)


def check_D3():
    print("(D3) cubic_shrinkingWindow at h = 1: dominance on the whole")
    print("     retained range with every deleted window of half-width h/M")
    for m in [10, 20, 40, 80]:
        e = mp.mpf(1) / m
        n = 4000
        bad = 0
        for k in range(n + 1):
            th = e + (mp.pi - 2 * e) * k / n
            if abs(th - mp.pi / 2) < e:
                continue
            if remainder(m, th) > abs(amp(th)) / 2:
                bad += 1
        print(f"      M = {m:>3}   h/M = {mp.nstr(e, 4):>8}   violations: {bad}/{n + 1}")
        assert bad == 0


def check_D4():
    print("(D4) the observed window is far narrower than h/M")
    for m in [10, 20, 40, 80]:
        d = None
        for k in range(1, 400):
            dd = mp.mpf(k) / 100000
            if remainder(m, mp.pi / 2 + dd) <= abs(amp(mp.pi / 2 + dd)) / 2:
                d = dd
                break
        print(f"      M = {m:>3}   dominance from |theta - pi/2| >= {mp.nstr(d, 3)}"
              f"   vs 1/M = {1 / m:.4f}")
        assert d is not None and d < mp.mpf(1) / m


if __name__ == "__main__":
    check_precision()
    check_D1()
    check_D2()
    check_D3()
    check_D4()
    print("ALL PASS")
