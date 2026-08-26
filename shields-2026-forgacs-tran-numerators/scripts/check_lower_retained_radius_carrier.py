#!/usr/bin/env python3
r"""What the `rho = 1` lower endpoint's retained radius can be expressed in.

The retained group needs a radius `R` with `t_a < R < min_j |w_j|`, where the
`w_j` are the roots of the endpoint pencil other than the double root at `t_a`.
`check_lower_clearance_no_constant.py` showed there is no uniform constant, so
`R` has to be a formula in the pencil, and the candidate was the **relative
gap** `g = (a_1 - a_0)/a_1` through

    min_j |w_j| / t_a  >=  1 + c_n * g .

That bound holds, but `c_n` decays too fast to use: the retained group consumes
`(n-2)` copies of it, and `(n-2)c_n` PEAKS and then falls, so there is no
positive floor and the radius degrades with `n`.

This asks what else could carry it, and finds one that does.  Writing
`u = (t_a - a_0)/t_a` for the relative distance from the smallest zero UP to the
critical point -- not the gap between the two smallest zeros --

    min_j |w_j| / t_a  >=  1 + kappa * u ,

with `kappa` flat in `n`, decaying in `r`, and **converging to a positive
constant** rather than to zero.  The constant is identified in closed form:
`kappa_inf = Re(s*) = 2.0888430156...`, where `s*` is the nonzero root of
`e^s = 1 + s` of least real part.

  (C1) `(n-2)c_n` peaks at n = 9 and falls -- the relative gap has no floor
  (C2) the precision trap, which manufactures refutations out of arithmetic
  (C3) the pipeline, validated against a closed form rather than against itself
  (C4) `u` is flat in `n` where `g` decays
  (C5) the spread limit in closed form, and `n`-independent
  (C6) `kappa_spread(r)` converges to `Re(s*)`, a POSITIVE floor
  (C7) and nothing anywhere is found below it

**Sampling is over the free parametrization, never over pencils.**  Fixing
`t_a = 1` by scale, any `v_1..v_m > 0` and `r >= 1` give `u = 1/(r + sum 1/v_k)`
and a pencil `a_0 = 1-u`, `a_k = 1+v_k` whose `Sigma(1) = 0` holds by
construction.  That IS the admissible set, and it reaches the degenerate
directions -- the tail collapsing onto `t_a`, and the tail escaping to infinity
-- by construction rather than by remembering to include them.  Both matter
here: the first sets the constant at small `r`, the second at large `r`, and a
sampler holding only one of them reports the other's constant as the answer.

Companion to `check_lower_clearance_no_constant.py` (no uniform constant) and
`check_lower_retained_clearance_gap.py` (the clearance is the wrong quantity).
"""
from __future__ import annotations

import math
import random

import mpmath as mp

KAPPA_INF_DIGITS = "2.088843015613043856"


# ---------------------------------------------------------------------------
# the pencil, its endpoint polynomial, and the separation
# ---------------------------------------------------------------------------
def _separation_at(v, r, dps):
    """`min_j |w_j|` at `t_a = 1`, computed at a fixed precision."""
    mp.mp.dps = dps
    vv = [mp.mpf(x) for x in v]
    u = 1 / (mp.mpf(r) + sum(1 / x for x in vv))
    a = [1 - u] + [1 + x for x in vv]
    coeff = [mp.mpf(1)]                        # prod_k (a_k - z), low -> high
    for ak in a:
        nxt = [mp.mpf(0)] * (len(coeff) + 1)
        for i, ci in enumerate(coeff):
            nxt[i] += ci * ak
            nxt[i + 1] -= ci
        coeff = nxt
    b = -sum(coeff)                            # -Q(1), the endpoint parameter
    while len(coeff) <= int(r):
        coeff.append(mp.mpf(0))
    coeff[int(r)] += b                         # D_b = Q + b z^r
    while len(coeff) > 1 and coeff[-1] == 0:
        coeff.pop()

    def synth(hi):                             # divide by (z - 1)
        out = [hi[0]]
        for k in range(1, len(hi)):
            out.append(hi[k] + out[-1])
        return out[:-1], out[-1]

    q1, _ = synth(coeff[::-1])
    q2, _ = synth(q1)                          # t_a is a DOUBLE root, deflate twice
    for extra in (2 * dps, 10 * dps):
        try:
            roots = mp.polyroots(q2, maxsteps=2000, extraprec=extra)
            return min(abs(z) for z in roots), u
        except Exception:
            continue
    return None, None


def separation(v, r):
    """`min_j |w_j|` and `u`, with the precision escalated to convergence."""
    dps, prev = 80, None
    for _ in range(6):
        sep, u = _separation_at(v, r, dps)
        if sep is None:
            dps *= 2
            continue
        if prev is not None and abs(sep - prev) <= abs(sep) * mp.mpf(10) ** (-15):
            mp.mp.dps = 40
            return +sep, +u
        prev, dps = sep, dps * 2
    raise RuntimeError("separation did not converge")


# ---------------------------------------------------------------------------
# (C1) the relative gap has no floor
# ---------------------------------------------------------------------------
c_n = {}
for n in range(3, 13):
    best = None
    for k in range(1, 8):
        eps = mp.mpf(10) ** (-k)
        sep, u = separation([eps] * (n - 1), 1)
        ratio = (sep - 1) / ((u + eps) / (1 + eps))
        if best is None or ratio < best:
            best = ratio
    c_n[n] = best

scaled = {n: (n - 2) * c for n, c in c_n.items()}
peak = max(scaled, key=lambda n: scaled[n])
assert peak == 9, f"expected (n-2)c_n to peak at n = 9, got n = {peak}"
assert scaled[12] < scaled[9], "expected (n-2)c_n to fall after its peak"
assert abs(c_n[3] - 1) < mp.mpf("1e-6") and abs(c_n[4] - 1) < mp.mpf("1e-6"), (
    "c_3 and c_4 should both be 1")
print(f"PASS  (C1) (n-2)c_n rises to {mp.nstr(scaled[9], 7)} at n = 9 and falls "
      f"to {mp.nstr(scaled[12], 7)} by n = 12, with c_3 = c_4 = 1 -- so the "
      f"relative gap carries no positive floor and the radius it gives decays")


# ---------------------------------------------------------------------------
# (C2) the precision trap
# ---------------------------------------------------------------------------
# A confluent pencil cancels to order `eps^n` in the coefficients of `Q`.  At a
# fixed precision the deflated polynomial is then noise, and the noise does not
# look like noise: it reports a separation BELOW `t_a`, which reads exactly like
# a refutation of the whole separation claim.  Every guard here would pass on
# it.  This is why `separation` escalates instead of trusting a setting.
trap_v = [mp.mpf(10) ** -11] * 7
naive, _ = _separation_at(trap_v, 1, 60)
mp.mp.dps = 40
honest, _ = separation(trap_v, 1)
assert naive is not None and naive < 1, (
    "the fixed-precision route was expected to report a separation below t_a "
    f"on a confluent 8-zero pencil; it gave {naive}")
assert honest > 1, f"the escalating route should stay above t_a; got {honest}"
print(f"PASS  (C2) on a confluent 8-zero pencil a fixed 60-digit setting puts "
      f"min|w_j| BELOW t_a by {mp.nstr(1 - naive, 4)} -- an apparent REFUTATION "
      f"that is pure arithmetic; escalating puts it ABOVE by "
      f"{mp.nstr(honest - 1, 4)}, and the two differ in the SIGN of the "
      f"separation rather than in a digit")


# ---------------------------------------------------------------------------
# (C3) the pipeline, checked against a closed form
# ---------------------------------------------------------------------------
# At `n = 3`, `r = 1` and `v = (eps, eps)` the endpoint polynomial is a cubic
# whose roots are `1, 1, w`, so Vieta gives `w = a_0 a_1 a_2` outright.  With
# `u = eps/(eps+2)` that is `(w-1)/u = 3 + 2 eps`, exactly.  A pipeline checked
# only against itself cannot catch a wrong deflation or a wrong `b`.
for k in (1, 2, 3, 4, 6):
    eps = mp.mpf(10) ** (-k)
    sep, u = separation([eps, eps], 1)
    predicted = 3 + 2 * eps
    assert abs((sep - 1) / u - predicted) < mp.mpf("1e-25"), (
        f"closed form disagrees at eps=1e-{k}: {(sep - 1) / u} vs {predicted}")
print("PASS  (C3) at n = 3, r = 1, v = (eps, eps) the measured (min|w_j|-1)/u "
      "equals the closed form 3 + 2eps to 25 digits at every eps tried, so the "
      "deflation and the endpoint parameter are right and not merely consistent")


# ---------------------------------------------------------------------------
# (C4) `u` is flat in `n` where `g` decays
# ---------------------------------------------------------------------------
# Both are functions of the pencil and `t_a` alone; the difference is which
# distance they measure.  `g` looks DOWN from the second zero to the first, and
# sees nothing of the other `n-2`; `u` looks UP from the first zero to the
# critical point, which every zero helps to place.
u_n = {}
for n in range(3, 13):
    best = None
    for k in range(1, 8):
        eps = mp.mpf(10) ** (-k)
        sep, u = separation([eps] * (n - 1), 1)
        ratio = (sep - 1) / u
        if best is None or ratio < best:
            best = ratio
    u_n[n] = best
spread_g = c_n[3] / c_n[12]
spread_u = max(u_n.values()) / min(u_n.values())
assert spread_g > 3, f"expected c_n to fall by more than 3x over n = 3..12"
assert spread_u < 1.6, (
    f"expected the u-constant to stay within 1.6x over n = 3..12; got {spread_u}")
print(f"PASS  (C4) over n = 3..12 the gap constant falls "
      f"{float(spread_g):.1f}x while the u-constant moves only "
      f"{float(spread_u):.2f}x ({mp.nstr(min(u_n.values()), 6)} to "
      f"{mp.nstr(max(u_n.values()), 6)}) -- flat in n, which is what the "
      f"retained radius needs")


# ---------------------------------------------------------------------------
# (C5) the spread limit, in closed form and independent of `n`
# ---------------------------------------------------------------------------
# Send the whole tail to infinity together, `a_k = 1 + V` with `V -> inf`.  Then
# `u -> 1/r`, and for `z = O(1)` the endpoint polynomial is `V^m` times
# `(a_0 - z) + z^r/r`, whose `r` times over is
#
#     z^r - r z + (r - 1)  =  (z - 1)^2 * sum_{i<r-1} (r-1-i) z^i ,
#
# the same factorization `EndpointUpperGeneralN.pow_sub_one_sub_smul` proves.
# So the `O(1)` roots are the roots of that sum, `m` and hence `n` have left the
# statement entirely, and the constant this family gives is a function of `r`
# alone.
def kappa_spread(r):
    """`r (min|root| - 1)` for `sum_{i<r-1} (r-1-i) z^i`; `None` when r <= 2,
    where the sum has no roots and this family imposes nothing."""
    if r <= 2:
        return None
    mp.mp.dps = 60
    coeff = [mp.mpf(r - 1 - i) for i in range(r - 1)]
    roots = mp.polyroots(coeff[::-1], maxsteps=3000, extraprec=400)
    out = r * (min(abs(z) for z in roots) - 1)
    mp.mp.dps = 40
    return +out


for r in (4, 7):
    predicted = kappa_spread(r)
    for n in (5, 9, 13):
        sep, u = separation([mp.mpf(10) ** 7] * (n - 1), r)
        got = (sep - 1) / u
        assert abs(got - predicted) < mp.mpf("1e-5"), (
            f"the spread family at n={n}, r={r} gave {got}, the n-free closed "
            f"form gives {predicted} -- so the limit is not n-independent after "
            f"all, or the reduction to z^r - rz + (r-1) is wrong")
print(f"PASS  (C5) the tail-to-infinity family reduces to the roots of "
      f"sum_(i<r-1) (r-1-i) z^i, with n gone from the statement: the closed form "
      f"matches the full pencil at n = 5, 9, 13 for r = 4 and r = 7 "
      f"(kappa = {mp.nstr(kappa_spread(4), 8)} and "
      f"{mp.nstr(kappa_spread(7), 8)})")


# ---------------------------------------------------------------------------
# (C6) and it converges to a POSITIVE constant
# ---------------------------------------------------------------------------
# `kappa_spread` decays in `r`, which is what killed the relative gap in `n`.
# The difference is where it goes.  Putting `z = 1 + s/r` sends
# `z^r - rz + (r-1)` to `e^s - s - 1`, so `r(|z| - 1) -> Re(s)` at the nonzero
# root of `e^s = 1 + s` of least real part -- a positive number, not zero.
mp.mp.dps = 40
s_star = mp.findroot(lambda w: mp.e ** w - 1 - w, mp.mpc(2, 7.5))
kappa_inf = mp.re(s_star)
assert abs(s_star) > 1, "findroot returned the trivial root s = 0"
assert abs(kappa_inf - mp.mpf(KAPPA_INF_DIGITS)) < mp.mpf("1e-18"), (
    f"kappa_inf drifted from its recorded value: {kappa_inf}")
assert kappa_inf > 2, "kappa_inf must be positive, and it is not even small"

seq = [(r, kappa_spread(r)) for r in (10, 30, 80, 200)]
gaps = [k - kappa_inf for _, k in seq]
assert all(g > 0 for g in gaps), "kappa_spread should approach kappa_inf from above"
assert all(gaps[i] > gaps[i + 1] for i in range(len(gaps) - 1)), (
    "kappa_spread should be decreasing toward kappa_inf")
assert gaps[-1] < mp.mpf("0.02"), f"expected convergence by r = 200; gap {gaps[-1]}"
print(f"PASS  (C6) kappa_spread falls monotonically to "
      f"Re(s*) = {mp.nstr(kappa_inf, 12)}, the least-real-part nonzero root of "
      f"e^s = 1 + s -- gap {mp.nstr(gaps[0], 4)} at r = 10 down to "
      f"{mp.nstr(gaps[-1], 4)} at r = 200.  It decays in r, but to a POSITIVE "
      f"floor, which is exactly what (n-2)c_n does not do in n")

# ---------------------------------------------------------------------------
# (C7) nothing anywhere is found below the floor
# ---------------------------------------------------------------------------
# (C5) and (C6) identify what ONE degenerate family gives.  By itself that is a
# lower bound on nothing -- reading a family's margin as the problem's is the
# mistake this whole item exists to correct.  So the space is searched: random
# starts, then a descent on `log v`, over `n` and `r` jointly, asked to go below
# `kappa_inf` and failing.
#
# `r <= 2` is included deliberately.  There the spread family imposes nothing at
# all -- the sum has no roots -- so if the floor came only from that family
# these would be free to dip.  They do not; the collapsing family holds them at
# 3, which is why both degenerate directions have to be in the sampler.
rng = random.Random(20260826)
floor_seen, arg_seen = None, None
for n in (3, 4, 6, 9):
    for r in (1, 2, 3, 5, 9, 12):
        for _seed in range(2):
            x = [math.log(rng.uniform(0.01, 60.0)) for _ in range(n - 1)]

            def at(pt, _r=r):
                try:
                    sep, u = separation([mp.mpf(math.exp(t)) for t in pt], _r)
                except RuntimeError:
                    return None
                return (sep - 1) / u

            cur = at(x)
            if cur is None:
                continue
            step = 1.5
            for _ in range(45):
                y = [max(-20.0, min(14.0, t + rng.gauss(0, step))) for t in x]
                got = at(y)
                if got is not None and got < cur:
                    cur, x = got, y
                else:
                    step *= 0.94
            if floor_seen is None or cur < floor_seen:
                floor_seen, arg_seen = cur, (n, r)

assert floor_seen >= kappa_inf, (
    f"found {floor_seen} at n, r = {arg_seen}, below kappa_inf = {kappa_inf} -- "
    f"the floor is not where the spread family puts it")
print(f"PASS  (C7) a descent over n = 3..9 and r = 1..12 got no lower than "
      f"{mp.nstr(floor_seen, 8)} (at n, r = {arg_seen}), never below "
      f"kappa_inf = {mp.nstr(kappa_inf, 8)} -- r <= 2 included, where the spread "
      f"family imposes nothing and the floor must come from elsewhere")

print("ALL PASS  check_lower_retained_radius_carrier")
