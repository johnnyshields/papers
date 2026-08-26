#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`, `eq:upper-residue-ratio`.

The upper endpoint's residue data is `hL_1 : forall i, ||L_1 i|| = 1` together
with `hratio_1 : ftAmp(g_1 i)/ftAmp(gamma) -> L_1 i`.  `L_1` is not a choice --
`hratio_1` pins it uniquely because limits are unique -- so the only content is
that the limit has MODULUS ONE.  That is the claim checked here, and it is
checked across pencils and across `r` rather than at one witness, because a
clean constant at a single pencil has already turned out pencil-specific twice
tonight (`gamma''(0) = beta - 1`, not `-2`).

At the upper endpoint `tau -> 0` for `r >= 2`, the cluster collapses to the
ORIGIN, and the normalized roots `zeta_j = t_j/tau` tend to the `r`-th roots of
`-1`.  The amplitude ratio is a ratio of normalized roots,
`W_j/W = zeta_j/zeta_+ (1 + O(tau))`, so its limit is a quotient of two `r`-th
roots of `-1` and has modulus one for a structural reason rather than a
numerical coincidence.

Asserted, each as a failing test:

  (U1) `tau -> 0` at the upper endpoint for every `r >= 2` pencil swept, so the
       geometry really is the collapse-to-origin one and not the lower
       endpoint's.
  (U2) The normalized roots tend to the `r`-th roots of `-1`: `zeta_j^r -> -1`.
  (U3) `|W_j/W| -> 1` for every nonprincipal member, at four pencils spanning
       `r = 2, 3, 4` and two different denominators -- so the modulus-one claim
       is not a property of one cofactor.
  (U4) Teeth: the ratios themselves are NOT all `1` -- their arguments spread
       over the `r`-th roots -- so (U3) is measuring a modulus and not
       reporting that the members coincide.

`mpmath` throughout: at `eta = 1e-6` the normalized roots agree to six digits
before they separate, and `|W_j/W| - 1` is the quantity under test.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50
I = mp.mpc(0, 1)

PENCILS = [
    ("(1-t)^3(2-t)", [mp.mpf(1), mp.mpf(1), mp.mpf(1), mp.mpf(2)], mp.mpf(1), 2),
    ("(1-t)^3(2-t)", [mp.mpf(1), mp.mpf(1), mp.mpf(1), mp.mpf(2)], mp.mpf(1), 3),
    ("2.5(0.4-t)^2(1.7-t)", [mp.mpf('0.4'), mp.mpf('0.4'), mp.mpf('1.7')], mp.mpf('2.5'), 2),
    ("0.8(2-t)^4(5-t)", [mp.mpf(2)] * 4 + [mp.mpf(5)], mp.mpf('0.8'), 4),
]


def make(a, c, r):
    def Q(t):
        out = mp.mpf(c)
        for ak in a:
            out = out * (1 - t / ak)
        return out
    def dQ(t):
        h = mp.mpf(10) ** (-20)
        return (Q(t + h) - Q(t - h)) / (2 * h)
    return Q, dQ


def branch(Q, r, th):
    """Minimum-modulus conjugate pair: sweep tau, objective sin(arg z) for scale."""
    def obj(s):
        t = s * mp.exp(I * th)
        z = -Q(t) / t ** r
        return mp.sin(mp.arg(z))
    lo, hi = mp.mpf('1e-12'), mp.mpf(20)
    N = 5000
    prev, sp = obj(lo), lo
    for k in range(1, N + 1):
        s = lo * (hi / lo) ** (mp.mpf(k) / N)
        cur = obj(s)
        if mp.sign(cur) != mp.sign(prev):
            aa, bb = sp, s
            for _ in range(200):
                m = mp.sqrt(aa * bb)
                if mp.sign(obj(m)) == mp.sign(obj(aa)):
                    aa = m
                else:
                    bb = m
            return mp.sqrt(aa * bb)
        prev, sp = cur, s
    raise AssertionError(f"no branch radius at theta={th}")


def data(name, a, c, r, eta):
    Q, dQ = make(a, c, r)
    th = mp.pi / r - eta
    tau = branch(Q, r, th)
    g = tau * mp.exp(I * th)
    z = mp.re(-Q(g) / g ** r)
    # roots of Q(t) + z t^r : build the polynomial coefficients
    deg = max(len(a), r)
    coeffs = [mp.mpf(0)] * (deg + 1)
    poly = [mp.mpf(c)]
    for ak in a:
        new = [mp.mpf(0)] * (len(poly) + 1)
        for i, v in enumerate(poly):
            new[i] += v
            new[i + 1] += -v / ak
        poly = new
    for i, v in enumerate(poly):
        coeffs[i] += v
    coeffs[r] += z
    rts = mp.polyroots(list(reversed(coeffs)), maxsteps=400, extraprec=800)
    return tau, z, g, rts, Q, dQ


# ---------------------------------------------------------------------------
worst_tau = mp.mpf(0)
worst_pow = mp.mpf(0)
worst_mod = mp.mpf(0)
spread_seen = mp.mpf(0)

for name, a, c, r in PENCILS:
    tau_s = []
    for k in (4, 5, 6):
        eta = mp.mpf(10) ** (-k)
        tau, z, g, rts, Q, dQ = data(name, a, c, r, eta)
        tau_s.append(tau)
        zetas = [rt / tau for rt in rts if abs(abs(rt) / tau - 1) < mp.mpf(1) / 2]
        assert len(zetas) >= 2, f"{name} r={r}: only {len(zetas)} normalized roots near modulus 1"
        for zt in zetas:
            worst_pow = max(worst_pow, abs(zt ** r + 1))
        # amplitude ratios against the principal point
        def amp(t):
            return -mp.mpf(1) / (dQ(t) + z * r * t ** (r - 1))
        Wp = amp(g)
        args = []
        for rt in rts:
            if abs(rt - g) < mp.mpf(10) ** (-25):
                continue
            if abs(abs(rt) / tau - 1) > mp.mpf(1) / 2:
                continue
            ratio = amp(rt) / Wp
            worst_mod = max(worst_mod, abs(abs(ratio) - 1))
            args.append(mp.arg(ratio))
        if len(args) >= 2:
            spread_seen = max(spread_seen, max(args) - min(args))
    worst_tau = max(worst_tau, tau_s[-1])
    print(f"  {name:22s} r={r}  tau(1e-4,1e-5,1e-6) = "
          f"{[mp.nstr(v,4) for v in tau_s]}")

assert worst_tau < mp.mpf(1) / 100, f"tau does not go to 0 at the upper endpoint: {worst_tau}"
print(f"PASS  (U1) tau -> 0 at the upper endpoint for every pencil, worst {mp.nstr(worst_tau,6)}")
assert worst_pow < mp.mpf(1) / 100, f"zeta^r does not tend to -1: {mp.nstr(worst_pow,8)}"
print(f"PASS  (U2) the normalized roots satisfy zeta^r -> -1, worst |zeta^r + 1| = {mp.nstr(worst_pow,6)}")
assert worst_mod < mp.mpf(1) / 100, f"|W_j/W| does not tend to 1: {mp.nstr(worst_mod,8)}"
print(f"PASS  (U3) |W_j/W| -> 1 across r = 2, 3, 4 and two denominators, worst "
      f"deviation {mp.nstr(worst_mod,6)}")
assert spread_seen > mp.mpf(1) / 2, (
    f"the ratios' arguments span only {mp.nstr(spread_seen,6)}; (U3) may be reporting "
    "coincident members rather than a modulus")
print(f"PASS  (U4) their arguments spread over {mp.nstr(spread_seen,6)} rad, so (U3) "
      f"measures a modulus and not coincidence")

print("ALL PASS  check_upper_residue_modulus")
