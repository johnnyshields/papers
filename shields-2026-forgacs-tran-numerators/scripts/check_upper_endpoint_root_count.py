r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal
amplitude), the upper endpoint of the branch arc.

The upper endpoint block asserts, at angles `theta = pi/r - delta`, that there is
a radius `R_1` with `tau <= R_1 / 2` holding exactly the `r` roots of the pencil
`D(t) = Q(t) + z t^r` that carry the branch, with the principal root
`w = tau e^{i theta}` and its conjugate two of them, and that erasing both leaves
`r - 2`.

`r - 2` is truncated subtraction, so at `r = 2` and at `r = 1` it reads `0` either
way and the cardinality clause cannot tell the two apart.  This script asks what
the cardinality cannot: does a separating radius satisfying `tau <= R_1 / 2` exist
at all?  The block takes its existence as part of the conclusion, so a failure
here is a failure of the hypothesis `2 <= r` to be droppable, not of the block.

The predicate is the block's own and is not a heuristic: `R_1 = 2 tau` is the
smallest radius the constraint `tau <= R_1 / 2` allows, so the block's radius
exists exactly when `#{t : D(t) = 0, |t| < 2 tau} = r`.

Complements `check_upper_endpoint_r_one.py`, which pins the other side of the
same dichotomy from the radius: there `tau` converges to a positive limit `L` at
`r = 1` instead of collapsing, so `eq:ab-def`'s `b` is finite.  This script sees
the consequence the block cares about -- with no collapse there is no cluster to
separate -- so between them the hypothesis `2 <= r` is not a gap to be removed
but the correct side of a dichotomy the paper already draws.

mpmath only; roots via `mp.polyroots` at 50 digits.  The branch radius is found
from the reality of `z`, not transcribed: `z = -Q(w)/w^r` is real exactly on the
branch, so `tau` is a root of `Im(Q(tau e^{i theta}) / (tau e^{i theta})^r)`, and
`w` is then a root of `D` by construction rather than by assertion.
"""
from mpmath import mp, mpf, mpc, exp, pi, findroot, polyroots, im, re, fabs

mp.dps = 50


def qcoeffs(c, a):
    """Coefficients of Q(t) = c * prod_k (a_k - t), highest degree first."""
    poly = [mpf(c)]                      # ascending, starts as constant c
    for ak in a:
        nxt = [mpf(0)] * (len(poly) + 1)
        for i, co in enumerate(poly):
            nxt[i] += co * mpf(ak)       # a_k * (...)
            nxt[i + 1] -= co             # -t * (...)
        poly = nxt
    return poly[::-1]


def peval(coeffs, t):
    v = mpc(0)
    for co in coeffs:
        v = v * t + co
    return v


def branch(c, a, r, theta):
    """Smallest tau > 0 on the branch, and the real z it induces."""
    Q = qcoeffs(c, a)

    def f(tau):
        w = mpc(tau) * exp(mpc(0, 1) * theta)
        return im(peval(Q, w) / w**r)

    tau, step = None, mpf(1) / 512
    prev, x = f(step), step * 2
    while x < 20:
        cur = f(x)
        if re(prev) * re(cur) < 0 or prev * cur < 0:
            tau = findroot(f, (x - step, x), solver='bisect', tol=mpf(10)**-45)
            break
        prev, x = cur, x + step
    assert tau is not None, f"no branch radius found at r={r}, theta={theta}"
    w = mpc(tau) * exp(mpc(0, 1) * theta)
    z = -peval(Q, w) / w**r
    assert fabs(im(z)) < mpf(10)**-25, f"z not real: im(z)={im(z)}"
    return mpf(re(tau)), mpf(re(z)), Q


def roots_within(Q, z, r, tau):
    """All roots of D = Q + z X^r, and how many lie inside the block's radius.

    `R_1 = 2 tau` is the smallest radius the block's own constraint
    `tau <= R_1 / 2` permits, so this count IS the block's cardinality claim.
    """
    # D has degree max(n, r); pad Q up to degree r before adding z * t^r, or a
    # negative index silently lands on the constant term instead.
    D = [mpf(0)] * max(0, r + 1 - len(Q)) + list(Q)
    D[len(D) - 1 - r] += z
    while len(D) > 1 and D[0] == 0:
        D = D[1:]
    rts = sorted(polyroots(D, maxsteps=300, extraprec=600), key=lambda t: fabs(t))
    inside = [t for t in rts if fabs(t) < 2 * tau]
    return rts, inside


def report(c, a, r, delta):
    n = len(a)
    theta = pi / r - delta
    tau, z, Q = branch(c, a, r, theta)
    w = mpc(tau) * exp(mpc(0, 1) * theta)
    wbar = mpc(tau) * exp(mpc(0, -1) * theta)
    rts, inside = roots_within(Q, z, r, tau)

    def among(t):
        if not inside:
            return False
        return min(fabs(t - s) for s in inside) < mpf(10)**-20

    sep = fabs(w - wbar)
    ok = (len(inside) == r)
    print(f"  n={n} r={r}: tau={mp.nstr(tau,8)} z={mp.nstr(z,8)} deg={len(rts)} "
          f"|t|<2tau -> {len(inside)} (want r={r}) {'OK' if ok else 'NO RADIUS'}"
          f"  |w-conj(w)|={mp.nstr(sep,6)}")
    return len(inside), among(w), among(wbar), sep, r


print("upper endpoint theta = pi/r - delta, pencil Q + z X^r")
print()
A = [1.0, 2.0, 3.0]
rows = []
for r in (1, 2, 3, 4, 5):
    for n in (2, 3):
        rows.append(report(1.0, A[:n], r, mpf(1) / 64))

print()
rge2 = [w for w in rows if w[4] >= 2]
r1 = [w for w in rows if w[4] == 1]

for cut, pin, cjin, sep, r in rge2:
    assert cut == r, f"r = {r}: {cut} roots inside 2*tau, the block claims r = {r}"
    assert pin, f"r = {r}: the principal root is not inside the block's radius"
    assert cjin, f"r = {r}: the conjugate is not inside the block's radius"
    assert sep > mpf(10)**-10, f"r = {r}: the principal met its conjugate"
print(f"PASS  at every r >= 2 ({len(rge2)} cases) the radius R_1 = 2*tau holds "
      f"exactly r roots, the principal and its conjugate among them and distinct, "
      f"so the double erase removes two of r and leaves r - 2")

# r = 1 is NOT the r >= 2 statement with a truncated index.  The conjugate is a
# second root at the same modulus, so 2 roots sit inside every radius the
# constraint tau <= R_1/2 permits, while the block allows exactly r = 1.
for cut, pin, cjin, sep, r in r1:
    assert cut == 2, f"r = 1: expected the conjugate pair, counted {cut}"
    assert cut > r, "r = 1: the count must strictly exceed r for the radius to fail"
    assert sep > mpf(10)**-3, (
        "r = 1 fails by the conjugate being a SECOND root inside the radius, "
        "not by colliding with the principal -- but they collided")
print(f"PASS  at r = 1 ({len(r1)} cases) no radius with tau <= R_1/2 isolates r "
      f"roots: the conjugate is a second root at the same modulus, and it is "
      f"{mp.nstr(r1[0][3], 4)} away from the principal rather than on top of it")

# The mechanism: at r >= 2 the branch radius is far below the pencil's own roots,
# so the cluster separates.  At r = 1 it is comparable to them and cannot.
A2 = [mpf(x) for x in A[:2]]
tau_r1, _, _ = branch(1.0, A[:2], 1, pi / 1 - mpf(1) / 64)
tau_r5, _, _ = branch(1.0, A[:2], 5, pi / 5 - mpf(1) / 64)
amin = min(A2)
assert tau_r5 / amin < mpf(1) / 10, "the r = 5 branch is not well inside the pencil"
assert tau_r1 / amin > 1, "the r = 1 branch is not comparable to the pencil roots"
print(f"PASS  the mechanism is scale: tau/min(a) is "
      f"{mp.nstr(tau_r5 / amin, 4)} at r = 5 and {mp.nstr(tau_r1 / amin, 4)} at "
      f"r = 1, so the cluster the block separates does not exist at r = 1")

print()
print("ALL PASS  check_upper_endpoint_root_count")
