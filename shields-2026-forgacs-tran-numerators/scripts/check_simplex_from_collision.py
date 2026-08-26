r"""Paper section `sec:dominance` (Proof of the main theorem).

Where the simplex condition of the `n \ge 4` endpoint route comes from, and
that the route's conclusion holds at real pencils rather than at abstract
simplex points.

The route normalizes a pencil root `w` by `s = (w + L)/L` and the exponents by
`u_k = L/(a_k + L)`, and then works on the simplex `\sum_k u_k = 1`.  That
condition is not a normalization anyone is free to impose: writing
`\Sigma(s) = \sum_k s/(a_k - s) + r` for the real critical function of
`eq:ab-def`, evaluation at `s = -L` gives

    \Sigma(-L) = -\sum_k L/(a_k + L) + r = r - \sum_k u_k ,

so `\sum_k u_k = 1` holds exactly when `-L` is a real zero of `\Sigma` AT
`r = 1`.  The simplex point is produced by the collision, and the route is the
`r = 1` case rather than a general one.  Three things are checked:

  (i)   `\sum_k L/(a_k + L) = 1` has exactly one root `L > 0` for `n \ge 2`,
        and none for `n = 1` -- the map is strictly increasing from `0` to `n`;
  (ii)  the `u` it produces is an INTERIOR simplex point, which is what
        `prod_one_add_lt_of_interior` needs and what fails at a vertex;
  (iii) at those pencils every root of `F(s) = \prod_k (1 - u_k s) - (1 - s)`
        other than the double root at `s = 0` satisfies `|s - 1| > 2`, which
        is `\|w\| > 2L`.

(iii) is the route's conclusion, so it is measured with its own margin
reported rather than against a tolerance chosen in advance.

mpmath only.
"""

from mpmath import mp, mpf, mpc, fabs, findroot, polyroots

mp.dps = 40


def sigma_at(a, L):
    """r - sum u_k at r = 1, i.e. the real critical function at s = -L."""
    return mpf(1) - sum(L / (ak + L) for ak in a)


def solve_L(a):
    """The unique L > 0 with sum_k L/(a_k + L) = 1, by bisection."""
    lo, hi = mpf(10) ** -30, mpf(1)
    while sigma_at(a, hi) > 0:          # sum still below 1, push out
        hi *= 2
        assert hi < mpf(10) ** 30, "no bracket found"
    assert sigma_at(a, lo) > 0, "the map does not start below 1"
    for _ in range(400):
        mid = (lo + hi) / 2
        if sigma_at(a, mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def other_roots(u):
    """Roots of prod(1 - u_k s) - (1 - s), with the double root at 0 divided out."""
    # prod (1 - u_k s) as ascending coefficients
    p = [mpf(1)]
    for uk in u:
        q = [mpf(0)] * (len(p) + 1)
        for i, c in enumerate(p):
            q[i] += c
            q[i + 1] += -uk * c
        p = q
    p[0] -= mpf(1)                       # subtract (1 - s)
    p[1] += mpf(1)
    assert fabs(p[0]) < mpf(10) ** -30, f"F(0) = {p[0]}, expected 0"
    assert fabs(p[1]) < mpf(10) ** -30, f"F'(0) = {p[1]}, expected 0 (double root)"
    tail = p[2:]                         # F(s)/s^2, ascending
    while tail and fabs(tail[-1]) < mpf(10) ** -30:
        tail.pop()
    if len(tail) < 2:
        return []
    return polyroots(list(reversed(tail)), maxsteps=200, extraprec=200)


def pencil(n, seed):
    """A deterministic positive exponent vector, no numpy."""
    return [mpf(1) + fabs(mp.sin(mpf(seed) * (k + 2) * mpf(11) / mpf(5))) * mpf(4)
            for k in range(n)]


# (i) no positive solution at n = 1: the map rises to 1 and never reaches it
a1 = [mpf(3)]
assert sigma_at(a1, mpf(10) ** 12) > 0, "n = 1 attains the simplex condition"
print("PASS  (i) at n = 1 the simplex condition has no positive solution")

worst_interior = mpf(1)
worst_margin = mpf("inf")
worst_at = None
count = 0

for n in (2, 3, 4, 5, 6, 8):
    for seed in range(1, 26):
        a = pencil(n, seed)
        L = solve_L(a)
        assert L > 0, f"L = {L} at n={n}, seed={seed}"

        u = [L / (ak + L) for ak in a]
        d = fabs(sum(u) - 1)
        assert d < mpf(10) ** -30, f"sum u = {sum(u)} at n={n}, seed={seed}"

        # uniqueness: the map is strictly increasing, so a second crossing
        # would need it to fall somewhere.  Check monotonicity on a ladder.
        vals = [sum(Lj / (ak + Lj) for ak in a)
                for Lj in [L * mpf(2) ** (mpf(j - 30) / 4) for j in range(1, 60)]]
        assert all(vals[i] < vals[i + 1] for i in range(len(vals) - 1)), (
            f"the simplex map is not increasing at n={n}, seed={seed}")

        # (ii) interior
        assert all(0 < uk < 1 for uk in u), f"u on the boundary at n={n}, seed={seed}"
        worst_interior = min(worst_interior, min(min(uk, 1 - uk) for uk in u))

        # (iii) the conclusion
        for s in other_roots(u):
            m = fabs(mpc(s) - 1)
            if m < worst_margin:
                worst_margin, worst_at = m, (n, seed)
            assert m > 2, f"|s-1| = {m} at n={n}, seed={seed}"
        count += 1

print(f"PASS  (i) exactly one L > 0 at every pencil tested ({count} pencils, "
      f"n = 2..8); the map is strictly increasing on a 59-point ladder about it")
print(f"PASS  (ii) u is interior at every pencil; closest approach to a face "
      f"{mp.nstr(worst_interior, 6)}")
print(f"PASS  (iii) every root but the collision has |s-1| > 2; thinnest "
      f"{mp.nstr(worst_margin, 8)} at n={worst_at[0]}, seed={worst_at[1]}")

# The family above is not a stress test and its margin must not be read as one.
# Every interior simplex point is REACHABLE from a positive pencil -- given `u`,
# take `L = 1` and `a_k = (1 - u_k)/u_k` -- so the thin configurations are
# ordinary pencils, merely skewed ones the sampler above never produces.  The
# thinnest known point, `u = (0.01, 0.01, 0.98)`, is the pencil
# `a = (99, 99, 1/49)`.  Sweeping toward the boundary is therefore a sweep over
# pencils, and it is where the bound is actually tested.
skew_worst = mpf("inf")
skew_at = None
for n in (3, 4, 5, 6):
    for j in range(1, 13):
        # start where the last coordinate is exactly 1/2 and walk the others in
        eps = mpf(1) / (2 * (n - 1)) * mpf(10) ** (-mpf(j - 1) / 3)
        u = [eps] * (n - 1) + [mpf(1) - (n - 1) * eps]
        assert all(0 < uk < 1 for uk in u), f"degenerate u at n={n}, j={j}"
        a = [(1 - uk) / uk for uk in u]            # L = 1 by construction
        assert all(ak > 0 for ak in a), "the inverse pencil is not positive"
        assert fabs(sum(mpf(1) / (ak + 1) for ak in a) - 1) < mpf(10) ** -30, (
            "L = 1 does not solve the collision equation for the inverse pencil")
        for sroot in other_roots(u):
            m = fabs(mpc(sroot) - 1)
            if m < skew_worst:
                skew_worst, skew_at = m, (n, mp.nstr(eps, 3))
            assert m > 2, f"|s-1| = {m} at the skewed pencil n={n}, eps={eps}"

print(f"PASS  (iii) holds along the whole approach to a face too; thinnest "
      f"{mp.nstr(skew_worst, 8)} at n={skew_at[0]}, eps={skew_at[1]} -- so the "
      f"margin above is a property of that sampler, not of pencils")
print("ALL PASS")
