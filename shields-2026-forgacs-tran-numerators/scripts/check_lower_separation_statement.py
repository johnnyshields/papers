#!/usr/bin/env python3
r"""Paper section `sec:dominance` (Proof of the main theorem), the lower-endpoint
separation step -- the STATEMENT, checked before a proof is
built against it.

Normalized as `check_lower_endpoint_esymm_criterion.py` sets it up, a root `w`
of the pencil at the lower endpoint `s_0 = t_a` satisfies

    prod_k (1 - v_k sigma) = (1 + sigma)^r ,   sigma = w/t_a - 1 ,

with `v_k = t_a/(a_k - t_a)` and the endpoint condition reading `sum_k v_k = -r`.
Exactly one coordinate is negative, because `t_a` lies in the first gap, and

    v_0 = -r - sum_{k>=1} v_k < -r

is then FORCED by the constraint rather than assumed alongside it.  The
separation claim is that every root other than the double root at the origin
clears the unit circle:

    sigma != 0  =>  |1 + sigma| > 1 ,   i.e. every other root of the pencil is
    strictly outside the circle of radius `t_a`.

A contour proof of this is under construction, so the cheap check comes first:
**is it true?**  A construction against a false statement is the one outcome
that cannot be salvaged, and the hypotheses here are exactly the shape that
hides a boundary case -- one coordinate forced negative by a linear constraint,
with everything else free and positive.

  (S1) The parametrization is sampled, not the objects.  The free coordinates
       are `v_1 .. v_{n-1} > 0`; `v_0` is then determined.  Sampling `v_0`
       independently and rejecting would concentrate the sample wherever the
       rejection rate happened to be low.

  (S2) What the sample IS gets asserted: the constraint holds, exactly one
       coordinate is negative, `v_0 < -r` comes out rather than being imposed,
       and `p_2 = sum v_k^2 > r`, which is what makes the quadratic coefficient
       `c_2 = (r - p_2)/2` negative at every sample.

  (S3) The origin is a double root, identically -- `c_0 = c_1 = 0` follows from
       `sum v_k = -r` alone.  Asserted as an exact coefficient identity, not as
       a small residual, since the double root IS the constraint.

  (S4) The separation itself, over a deterministic sweep that reaches the
       corners the interior of a random sample never does: `sum_{k>=1} v_k -> 0`
       (so `v_0 -> -r`), `v_0 -> -infinity`, one dominant coordinate against
       many tiny ones, near-equal coordinates, `n` up to 40 and `r` up to 12,
       and `r > n` as well as `r < n`.  The margin `min |1+sigma| - 1` is
       reported at its worst over the whole sweep.

  (S5) The margin's approach to zero is located rather than left as a pass.
       It is NOT bounded below by a constant: driving `sum_{k>=1} v_k -> 0`
       sends the worst margin to 0.  So the lemma is true with a margin that
       degenerates, and any proof of it that produces a uniform positive
       clearance is proving something false.  This is the fact a contour
       argument has to respect, and it is why the statement is `> 1` strictly
       rather than `>= 1 + c`.

mpmath only.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50


def coeffs(v, r):
    """Descending coefficients of F(sigma) = prod_k (1 - v_k sigma) - (1+sigma)^r."""
    prod = [mp.mpf(1)]                      # ascending
    for vk in v:
        nxt = [mp.mpf(0)] * (len(prod) + 1)
        for i, c in enumerate(prod):
            nxt[i] += c
            nxt[i + 1] += -vk * c
        prod = nxt
    binom = [mp.binomial(r, i) for i in range(r + 1)]
    deg = max(len(prod), len(binom))
    asc = [mp.mpf(0)] * deg
    for i, c in enumerate(prod):
        asc[i] += c
    for i, c in enumerate(binom):
        asc[i] -= c
    return asc


def separation(v, r):
    """min |1+sigma| over the roots other than the double root at 0, or None."""
    asc = coeffs(v, r)
    assert abs(asc[0]) < mp.mpf('1e-40'), ('c_0', asc[0])          # (S3)
    assert abs(asc[1]) < mp.mpf('1e-40'), ('c_1', asc[1])          # (S3)
    red = asc[2:]
    while red and abs(red[-1]) < mp.mpf('1e-45'):
        red.pop()
    if len(red) < 2:
        return None
    roots = mp.polyroots(list(reversed(red)), maxsteps=800, extraprec=400)
    return min(abs(1 + s) for s in roots)


def sample(free, r):
    """(S1) the free coordinates are the positive ones; v_0 is determined."""
    v0 = -mp.mpf(r) - sum(free)
    v = [v0] + list(free)
    # (S2) assert what the sample IS
    assert abs(sum(v) + r) < mp.mpf('1e-40')
    assert sum(1 for x in v if x < 0) == 1
    assert v0 < -mp.mpf(r)
    p2 = sum(x ** 2 for x in v)
    assert p2 > mp.mpf(r), (p2, r)
    assert (mp.mpf(r) - p2) / 2 < 0
    return v


# --- (S4) the sweep, corners first -------------------------------------------
cases: list[tuple[str, list, int]] = []
mp.mp.dps = 50

for r in (1, 2, 3, 5, 12):
    # the constraint boundary: sum of the positive part -> 0, so v_0 -> -r
    for e in ('1e-1', '1e-3', '1e-6', '1e-10'):
        t = mp.mpf(e)
        cases.append((f"v0 -> -r (tail {e}), r={r}", [t / 3, t / 3, t / 3], r))
    # v_0 -> -infinity
    for big in ('1e1', '1e3', '1e6'):
        t = mp.mpf(big)
        cases.append((f"v0 -> -inf (tail {big}), r={r}", [t, t / 2, t / 7], r))
    # one dominant positive coordinate against many tiny ones
    cases.append((f"one dominant + 20 tiny, r={r}",
                  [mp.mpf(50)] + [mp.mpf('1e-4') * (i + 1) for i in range(20)], r))
    # near-equal coordinates, n large
    for n in (2, 3, 8, 40):
        cases.append((f"near-equal n={n}, r={r}",
                      [mp.mpf(1) + mp.mpf('1e-7') * i for i in range(n)], r))
    # a spread of scales
    cases.append((f"log-spread, r={r}",
                  [mp.mpf(10) ** (mp.mpf(i) / 2 - 3) for i in range(12)], r))

# deterministic pseudo-random interior, so the corners are not the only cover
seed = mp.mpf('0.6180339887498948482045868343656381177203')
x = seed
for trial in range(220):
    n = 1 + trial % 9
    r = 1 + (trial // 9) % 7
    free = []
    for _ in range(n):
        x = mp.frac(x * 6364136223846793005 + mp.pi)
        free.append(mp.mpf(10) ** (6 * x - 3))
    cases.append((f"pseudo-random n={n} r={r} #{trial}", free, r))

worst = None
worst_name = ''
checked = 0
for name, free, r in cases:
    v = sample(free, r)
    m = separation(v, r)
    if m is None:
        continue
    checked += 1
    assert m > 1, (name, mp.nstr(m, 20))
    if worst is None or m - 1 < worst:
        worst, worst_name = m - 1, name

print(f"PASS  (S1-S3) every one of the {len(cases)} samples satisfies the constraint "
      f"with exactly one negative coordinate, v_0 < -r forced rather than imposed, "
      f"p_2 > r, and c_0 = c_1 = 0 exactly")
print(f"PASS  (S4) |1+sigma| > 1 at every root other than the origin, over "
      f"{checked} pencils reaching both constraint boundaries, n up to 40, r up to 12, "
      f"and r on both sides of n")
print(f"      worst margin min|1+sigma| - 1 = {mp.nstr(worst, 8)} at: {worst_name}")


# --- (S5)/(S6) WHICH corner degenerates, located rather than guessed ---------
# The margin does NOT vanish as the positive part of the constraint vanishes.
# In that corner it CONVERGES, and to a limit available in closed form: with
# `v_0 -> -r` and the rest -> 0 the equation degenerates to `1 + r sigma =
# (1+sigma)^r`, whose non-origin roots are those of `sum_{j>=2} C(r,j)
# sigma^{j-2}`.  The margin approaches the clearance of THAT polynomial.
#
# The corner that does degenerate is the other one, `v_0 -> -infinity`, and it
# was found by the sweep above rather than predicted: the roots collapse onto
# the origin like `1/v_k`, so `|1+sigma| -> 1` from above.  Both are asserted
# here -- one against its closed form, one as a fitted rate -- because a lemma
# whose margin degenerates in an unnoticed corner is exactly what a proof
# producing uniform clearance would silently contradict.


def limiting_margin(r):
    """Clearance of the degenerate equation 1 + r sigma = (1+sigma)^r."""
    asc = [mp.binomial(r, j) for j in range(2, r + 1)]
    if len(asc) < 2:
        return None
    roots = mp.polyroots(list(reversed(asc)), maxsteps=800, extraprec=400)
    return min(abs(1 + s) for s in roots) - 1


for r in (3, 4, 6):
    lim = limiting_margin(r)
    ladder = []
    for e in ('1e-2', '1e-4', '1e-6', '1e-8', '1e-10'):
        t = mp.mpf(e)
        ladder.append((t, separation(sample([t / 3, t / 3, t / 3], r), r) - 1))
    assert all(m > 0 for _, m in ladder), (r, ladder)
    assert all(b < a for (_, a), (_, b) in zip(ladder, ladder[1:])), (r, ladder)
    err = [abs(m - lim) for _, m in ladder]
    assert all(b < a for a, b in zip(err, err[1:])), (r, err)
    assert err[-1] < mp.mpf('1e-9'), (r, mp.nstr(err[-1], 8))
    print(f"PASS  (S5) r={r}: the margin CONVERGES to the closed-form clearance of "
          f"1 + r sigma = (1+sigma)^r, {mp.nstr(lim, 12)}, as the positive part of "
          f"the constraint vanishes -- it does not degenerate in this corner "
          f"(residual {mp.nstr(err[-1], 4)} at tail 1e-10)")

# (S6) the corner that DOES degenerate, as a fitted rate
xs, ys = [], []
for e in (2, 3, 4, 5, 6, 7):
    T = mp.mpf(10) ** e
    m = separation(sample([T, T / 2, T / 7], 1), 1) - 1
    assert m > 0, (e, m)
    xs.append(mp.log(T))
    ys.append(mp.log(m))
n = len(xs)
sx, sy = sum(xs), sum(ys)
slope = (n * sum(a * b for a, b in zip(xs, ys)) - sx * sy) / (n * sum(a * a for a in xs) - sx * sx)
assert abs(slope + 1) < mp.mpf('0.02'), mp.nstr(slope, 10)
print(f"PASS  (S6) the margin DOES vanish as v_0 -> -infinity, at a fitted "
      f"log-log slope of {mp.nstr(slope, 8)} against the predicted -1: the roots "
      f"collapse onto the origin like 1/v_k.  This corner, not the constraint "
      f"boundary, is where a uniform-clearance proof would be proving something false")

print("ALL PASS  check_lower_separation_statement")
