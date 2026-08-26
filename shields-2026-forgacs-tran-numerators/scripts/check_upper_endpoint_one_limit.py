#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `sec:geometry`,
`eq:ab-def`, `thm:FT-geometry`.

The two facts the `r = 1` upper retained set still needs, both about ONE
polynomial rather than about the branch.

At `r = 1` the arc ends at `theta = pi` with `tau -> L > 0`, and the limiting
pencil is `D_b = Q + b X` at the endpoint parameter `b = -Q(-L)/(-L)`.
`two_le_rootMultiplicity_ftDen_endpoint_pi` proves `-L` is a root of `D_b` of
order **at least** 2, from `E(-L) = 0` alone.  A FIXED separating radius near the
endpoint needs two more things, and both are properties of `D_b`:

  (M1) `-L` has multiplicity EXACTLY 2, i.e. `D_b''(-L) != 0`.  With order >= 2
       and no upper bound, a third root could be arriving at `-L` and no fixed
       radius would isolate the pair.
  (M2) No OTHER root of `D_b` has modulus `<= L`.  This is what makes
       `liminf third(theta) > L` rather than `>= L`, and it is the difference
       between a fixed radius existing and not.

Both are checked here, with margins, so the Lean route is priced before it is
built.  A `liminf` equal to `L` would kill the fixed radius exactly as the
interior's `sup tau` against `inf third` did, and that comparison is the shape
this tree has been wrong about twice.

  (M3) Teeth: at `r >= 2` the same construction is meaningless -- `tau -> 0`, so
       the collision is at the origin and `D_b` is not the right object.  The
       `r = 1` limiting pencil is checked to be a genuine degree-`n` polynomial
       with a real double root, not a degenerate one.

mpmath only, 50 digits.  `L` is found from the endpoint condition `E(-L) = 0`
with `E(t) = t Q'(t) - r Q(t)`, which is the same characterization
`check_upper_endpoint_r_one.py` uses, not a re-derivation of the branch.
"""
from mpmath import mp, mpf, mpc, polyroots, fabs, findroot

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


def deriv(C):
    d = len(C) - 1
    return [C[i] * (d - i) for i in range(d)] if d > 0 else [mpf(0)]


def find_L(Q, r):
    """The positive `L` with `E(-L) = 0`, `E(t) = t Q'(t) - r Q(t)`."""
    Qp = deriv(Q)

    def E(t):
        return t * peval(Qp, t) - r * peval(Q, t)

    lo, step = mpf(1) / 1000, mpf(1) / 500
    x, prev = lo + step, E(-lo)
    while x < 50:
        cur = E(-x)
        if re_sign(prev) * re_sign(cur) < 0:
            return mpf(findroot(lambda u: E(-u).real, (x - step, x),
                                solver='bisect', tol=mpf(10)**-40).real)
        prev, x = cur, x + step
    raise AssertionError("no positive L with E(-L) = 0")


def re_sign(z):
    return mpf(z.real) if hasattr(z, 'real') else mpf(z)


PENCILS = [
    ([1.0, 1.0, 2.0], 1.0, "a=(1,1,2) rho=2"),
    ([1.0, 1.0, 1.0, 2.0], 1.0, "a=(1,1,1,2) rho=3"),
    ([0.4, 0.4, 1.7], 2.5, "a=(0.4,0.4,1.7) rho=2, c=2.5"),
    ([1.0, 1.0, 2.0, 5.0], 1.0, "a=(1,1,2,5) rho=2"),
    ([2.0, 2.0, 2.0, 7.0], 0.8, "a=(2,2,2,7) rho=3, c=0.8"),
]

print("the r = 1 limiting pencil D_b = Q + b X at the collision point -L")
print()

rows = []
for a, c, lab in PENCILS:
    Q = qcoeffs(c, a)
    L = find_L(Q, 1)
    b = -peval(Q, mpc(-L)) / mpc(-L)
    assert fabs(b.imag) < mpf(10)**-30, f"{lab}: b not real"
    b = mpf(b.real)
    D = list(Q)
    D[-2] += b                                   # add b * t^1
    d1, d2 = deriv(D), deriv(deriv(D))
    v0, v1, v2 = peval(D, mpc(-L)), peval(d1, mpc(-L)), peval(d2, mpc(-L))
    rts = sorted(polyroots(D, maxsteps=400, extraprec=800), key=lambda t: fabs(t))
    others = [t for t in rts if fabs(t + L) > mpf(10)**-18]
    third = min(fabs(t) for t in others) if others else None
    rows.append((lab, L, b, fabs(v0), fabs(v1), fabs(v2), third, len(rts)))
    print(f"  {lab}: L={mp.nstr(L,8)} b={mp.nstr(b,8)} deg={len(rts)}  "
          f"|D_b(-L)|={mp.nstr(fabs(v0),4)} |D_b'(-L)|={mp.nstr(fabs(v1),4)} "
          f"|D_b''(-L)|={mp.nstr(fabs(v2),8)}  next modulus="
          f"{mp.nstr(third,8) if third is not None else 'none'}")
print()

# (M1) multiplicity exactly two
for lab, L, b, v0, v1, v2, third, deg in rows:
    assert v0 < mpf(10)**-30, f"{lab}: -L is not a root, |D_b(-L)|={mp.nstr(v0,6)}"
    assert v1 < mpf(10)**-28, f"{lab}: |D_b'(-L)|={mp.nstr(v1,6)} -- order is not >= 2"
    assert v2 > mpf(1) / 100, (
        f"{lab}: |D_b''(-L)|={mp.nstr(v2,6)} -- multiplicity may exceed 2, so no "
        f"fixed radius isolates the pair")
print(f"PASS  (M1) -L is a root of D_b of multiplicity EXACTLY 2 at all "
      f"{len(rows)} pencils: D_b and D_b' vanish there and D_b'' does not, worst "
      f"|D_b''| = {mp.nstr(min(r[5] for r in rows),6)}")

# (M2) every other root is strictly outside modulus L
margins = []
for lab, L, b, v0, v1, v2, third, deg in rows:
    assert third is not None, f"{lab}: D_b has no root besides the double one"
    assert third > L, (
        f"{lab}: another root sits at modulus {mp.nstr(third,8)} <= L="
        f"{mp.nstr(L,8)}, so no fixed radius separates the pair")
    margins.append((lab, third / L))
print(f"PASS  (M2) every other root of D_b is STRICTLY outside modulus L, "
      f"ratios " + ", ".join(f"{mp.nstr(m,6)}" for _, m in margins))
worst = min(m for _, m in margins)
assert worst > 1 + mpf(1) / 100, f"the worst separation ratio is only {mp.nstr(worst,8)}"
print(f"PASS  the worst ratio is {mp.nstr(worst,8)}, bounded away from 1, so "
      f"liminf third > L holds with room and a FIXED radius exists near theta = pi")

# (M3) the limiting pencil is a genuine object, not degenerate
for lab, L, b, v0, v1, v2, third, deg in rows:
    a = next(a for a, c, l in PENCILS if l == lab)
    assert deg == len(a), f"{lab}: D_b has degree {deg}, expected {len(a)}"
    assert L > 0 and b != 0, f"{lab}: degenerate endpoint data"
print(f"PASS  (M3) D_b has the full degree of Q at every pencil and its double "
      f"root sits at a strictly negative real point, so the r = 1 collision is a "
      f"genuine finite one and not the r >= 2 collapse into the origin")

# (M4) Two facts stronger than (M2), handed over because a stronger target with
# more room is often the easier one to prove.
#
# First, an EXACT identity: `D_b`'s constant term is `Q(0) = c prod a_j` and its
# leading coefficient is `c(-1)^n`, so the product of all its roots is exactly
# `prod a_j`.  The collision contributes `L^2`, hence the remaining roots
# multiply to `prod a_j / L^2`.  At `n = 3` there is only one of them, so (M2)
# becomes the CLOSED FORM inequality `prod a_j > L^3` -- no root-finding at all.
#
# Second, empirically the other roots clear not merely `L` but `max a_j`.
prods, cubics, over_max = [], [], []
for (a, c, lab), (lab2, L, b, v0, v1, v2, third, deg) in zip(PENCILS, rows):
    pa = mpf(1)
    for ak in a:
        pa *= mpf(ak)
    Q = qcoeffs(c, a)
    D = list(Q)
    D[-2] += b
    rts = sorted(polyroots(D, maxsteps=400, extraprec=800), key=lambda t: fabs(t))
    others = [t for t in rts if fabs(t + L) > mpf(10)**-18]
    prod_others = mpf(1)
    for t in others:
        prod_others *= fabs(t)
    assert fabs(prod_others - pa / L**2) < mpf(10)**-20 * (pa / L**2), (
        f"{lab}: product of the non-collision roots is {mp.nstr(prod_others,10)}, "
        f"not prod(a)/L^2 = {mp.nstr(pa/L**2,10)}")
    prods.append(lab)
    if len(a) == 3:
        assert pa > L**3, f"{lab}: prod a = {mp.nstr(pa,8)} <= L^3 = {mp.nstr(L**3,8)}"
        cubics.append((lab, pa / L**3))
    assert third > max(mpf(x) for x in a), (
        f"{lab}: next modulus {mp.nstr(third,8)} does not clear max a = "
        f"{mp.nstr(max(mpf(x) for x in a),8)}")
    over_max.append(third / max(mpf(x) for x in a))
print(f"PASS  (M4a) the non-collision roots multiply to EXACTLY prod(a)/L^2 at all "
      f"{len(prods)} pencils -- D_b's root product is prod(a), and the collision "
      f"takes L^2 of it")
print(f"PASS  (M4b) at n = 3 that makes (M2) the closed form prod(a) > L^3, which "
      f"holds by factors " + ", ".join(mp.nstr(v, 6) for _, v in cubics) +
      " -- no root-finding needed there")
print(f"PASS  (M4c) the other roots clear not just L but max(a), by factors "
      + ", ".join(mp.nstr(v, 5) for v in over_max) +
      " -- a stronger target than (M2) and possibly an easier one")

print()
print("ALL PASS  check_upper_endpoint_one_limit")
