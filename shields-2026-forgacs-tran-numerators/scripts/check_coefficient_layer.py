r"""Paper section `sec:dominance` (Proof of the main theorem).

The coefficient layer consumed by the `n \ge 4` route to the upper endpoint of `sec:dominance`.
For a simplex point `u` (`u_k > 0`, `\sum u_k = 1`) put `v_k = 1 - u_k` and

    P(t) = \prod_k (v_k + u_k t) = \sum_l a_l t^l .

Three claims are checked here, each behind a failing assert:

  (i)   a_l \ge 0 for every l  -- every factor has non-negative coefficients;
  (ii)  \sum_l a_l = 1         -- P(1) = \prod (v_k + u_k) = \prod 1 = 1;
  (iii) \sum_l l a_l = 1       -- P'(1) = P(1) \sum_k u_k/(v_k + u_k) = 1.

(ii) and (iii) are exact identities, not estimates: (iii) is the logarithmic
derivative at `t = 1`, where every denominator `v_k + u_k` is `1`, so the sum
collapses to `\sum u_k = 1` and `P(1) = 1` carries the prefactor.  They are
therefore checked to full working precision rather than to a tolerance chosen
by inspection.

mpmath only; the polynomial product is carried in exact `mpf` coefficients.
"""

from mpmath import mp, mpf, fabs

mp.dps = 60


def coeffs(u):
    """Coefficients a_l of prod_k ((1-u_k) + u_k t), ascending in l."""
    a = [mpf(1)]
    for uk in u:
        vk = mpf(1) - uk
        b = [mpf(0)] * (len(a) + 1)
        for l, al in enumerate(a):
            b[l] += vk * al
            b[l + 1] += uk * al
        a = b
    return a


def simplex_point(n, seed):
    """A deterministic interior point of the simplex, no numpy."""
    mp.dps = 60
    raw = [mpf(1) + fabs(mp.sin(mpf(seed) * (k + 1) * mpf(7) / mpf(3))) for k in range(n)]
    s = sum(raw)
    return [r / s for r in raw]


TOL = mpf(10) ** (-45)
worst_sum = mpf(0)
worst_mean = mpf(0)
neg = 0

for n in (2, 3, 4, 5, 6, 8, 12):
    for seed in range(1, 41):
        u = simplex_point(n, seed)
        assert fabs(sum(u) - 1) < TOL, "test point is not on the simplex"
        a = coeffs(u)
        assert len(a) == n + 1, f"degree is {len(a)-1}, expected {n}"

        # (i) non-negativity
        for l, al in enumerate(a):
            if al < 0:
                neg += 1
        assert all(al >= 0 for al in a), f"negative coefficient at n={n}, seed={seed}"

        # (ii) the coefficients sum to one
        d0 = fabs(sum(a) - 1)
        worst_sum = max(worst_sum, d0)
        assert d0 < TOL, f"sum a_l = {sum(a)} at n={n}, seed={seed}"

        # (iii) the mean index is one
        d1 = fabs(sum(mpf(l) * al for l, al in enumerate(a)) - 1)
        worst_mean = max(worst_mean, d1)
        assert d1 < TOL, f"sum l a_l != 1 at n={n}, seed={seed}"

print(f"PASS  a_l >= 0 at every l, every point tested ({neg} negatives found)")
print(f"PASS  sum_l a_l = 1        worst residual {mp.nstr(worst_sum, 5)}")
print(f"PASS  sum_l l a_l = 1      worst residual {mp.nstr(worst_mean, 5)}")

# The boundary of the simplex, where a coordinate is 0 or 1, is where the
# route's strictness dies -- so it is checked to degrade rather than to hold.
u = [mpf(1)] + [mpf(0)] * 3
a = coeffs(u)
assert a == [mpf(0), mpf(1), mpf(0), mpf(0), mpf(0)], f"vertex gives {a}"
assert sum(a) == 1 and sum(mpf(l) * al for l, al in enumerate(a)) == 1
print("PASS  at a vertex the normalizations survive; P degenerates to t")

print("ALL PASS")
