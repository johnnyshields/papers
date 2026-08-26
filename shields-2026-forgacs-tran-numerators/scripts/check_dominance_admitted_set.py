#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `eq:dominance-bound`,
`eq:retained-range`, `eq:amplitude-deletion`.

`ft_weighted_dominance_unconditional` carries no antecedent, so its content rests
entirely on the set of angles it admits being NON-EMPTY.  It concludes, for
`M >= M_0`,

    h/M <= theta <= pi/r - h/M,
    for every theta_j in S:  exp(-((-log sigma)/(2|S|) * M / nu_j)) <= |theta - theta_j|
      ==>  ftRemainder <= ftPrincipalAmp / 2.

If the deletion windows never shrink below the arc, no `theta` satisfies the
hypothesis and the theorem is true and empty.  That is not hypothetical: the
`exists Theta` form this replaced WAS trivially true, at `Theta M := univ`, and
compiled on the first attempt.  So the admitted set is measured here rather than
argued.

  (A1) With `nu_j >= 1` the window radius decays exponentially in `M`, the
       admitted set is non-empty from a finite `M`, and its measure tends to the
       full arc `pi/r`.
  (A2) The clause `forall theta_j in S, 1 <= B.rootMultiplicity(...)` is
       LOAD-BEARING, not bookkeeping.  Lean's division by zero is zero, so at
       `nu_j = 0` the radius is `exp(-0) = 1`, a window that never shrinks; and
       `pi/r <= pi/2 < 1` for `r >= 2`, so a single divisor point empties the arc
       at every `M`.  Dropping that clause makes the theorem vacuous.
  (A3) `sigma < 1` STRICTLY is load-bearing for the same reason from the other
       side: at `sigma = 1`, `-log sigma = 0`, the radius is `exp(0) = 1` again
       and the arc is emptied.
  (A4) The threshold `M` at which the arc opens is finite for every `sigma < 1`
       and scales as `1/(-log sigma)`.  It is NOT bounded by a constant: the
       theorem produces `sigma`, so as `sigma -> 1` the arc opens later without
       bound.  This script's first draft asserted `M <= 4096` and the measured
       worst case is 16384 -- a ceiling written from a guess rather than a
       measurement.

mpmath only.  `|S| <= deg B` because the multiplicity clause pins `S` to angles
where `B` vanishes at the principal point, so the sweeps here are over the
`(|S|, nu, sigma, r)` a real pencil can present.
"""
from mpmath import mp, mpf, exp, log, pi

mp.dps = 40


def radius(sigma, card, nu, M):
    """The deletion radius of `eq:amplitude-deletion`, with Lean's `x/0 = 0`."""
    inner = (-log(sigma)) / (2 * card)
    q = inner * M / nu if nu != 0 else mpf(0)   # Lean: division by zero is zero
    return exp(-q)


def admitted_measure(sigma, card, nu, M, r, h):
    """Measure of the admitted angles: the retained range minus the windows.

    An upper bound on what the windows remove is `2 * card * radius`; the
    retained range has length `pi/r - 2h/M`.  Worst case, the windows are
    disjoint and wholly inside.
    """
    arc = pi / r - 2 * mpf(h) / M
    if arc <= 0:
        return mpf(0)
    return max(mpf(0), arc - 2 * card * radius(sigma, card, nu, M))


CASES = [   # card, nu, sigma, r
    (1, 1, mpf('0.5'), 2), (2, 1, mpf('0.5'), 2), (4, 1, mpf('0.5'), 3),
    (2, 2, mpf('0.9'), 2), (6, 3, mpf('0.99'), 5), (3, 1, mpf('0.999'), 4),
]
H = 1

print("admitted angles of ft_weighted_dominance_unconditional")
print()

# (A1) non-empty from a finite M, and filling the arc
opens = []
for card, nu, sigma, r in CASES:
    M = 1
    while M <= 2 ** 22 and admitted_measure(sigma, card, nu, M, r, H) <= 0:
        M *= 2
    assert M <= 2 ** 22, (
        f"card={card} nu={nu} sigma={sigma} r={r}: arc never opens by M=2^22")
    big = admitted_measure(sigma, card, nu, 2 ** 24, r, H)
    assert big > mpf('0.999') * pi / r, (
        f"card={card} nu={nu}: admitted measure {mp.nstr(big,6)} does not fill "
        f"the arc {mp.nstr(pi/r,6)}")
    opens.append((card, nu, sigma, r, M))
    print(f"  card={card} nu={nu} sigma={mp.nstr(sigma,4)} r={r}: arc opens at "
          f"M={M}, measure at M=2^24 is {mp.nstr(big,8)} of {mp.nstr(pi/r,8)}")
print("PASS  with nu >= 1 and sigma < 1 the admitted set is non-empty from a "
      "finite M and its measure tends to the full retained arc, so the "
      "conclusion is not vacuous")
print()

# (A2) the multiplicity clause is load-bearing
for card, _, sigma, r in CASES:
    for M in (1, 10, 10 ** 3, 10 ** 6, 10 ** 9):
        assert admitted_measure(sigma, card, 0, M, r, H) == 0, (
            f"nu=0 should empty the arc at every M, but card={card} r={r} M={M} "
            f"admits measure {mp.nstr(admitted_measure(sigma,card,0,M,r,H),6)}")
    assert radius(sigma, card, 0, 10 ** 9) == 1
print("PASS  at nu = 0 the radius is exp(-0) = 1 at every M (Lean's x/0 = 0), "
      "and pi/r <= pi/2 < 1 for r >= 2, so one divisor point empties the arc -- "
      "the clause `1 <= B.rootMultiplicity` is what makes the theorem non-vacuous")
print()

# (A3) sigma < 1 strictly, from the other side
for card, nu, _, r in CASES:
    for M in (1, 10 ** 3, 10 ** 9):
        assert admitted_measure(mpf(1), card, nu, M, r, H) == 0, (
            f"sigma=1 should empty the arc, card={card} r={r} M={M}")
print("PASS  at sigma = 1 the radius is exp(0) = 1 at every M as well, so the "
      "STRICT sigma < 1 is load-bearing and not a convenience")
print()

# (A4) the threshold is finite for every sigma < 1, and it SCALES like
# 1/(-log sigma).  It is not "small": the theorem produces sigma and we do not
# choose it, so as sigma -> 1 the arc opens later without bound.  Asserting a
# fixed ceiling here would be asserting a guess -- the first draft of this
# script demanded M <= 4096 and the measured worst case is 16384.
def opens_at(card, nu, sigma, r, h=1, cap=2 ** 26):
    M = 1
    while M <= cap and admitted_measure(sigma, card, nu, M, r, h) <= 0:
        M *= 2
    return M if M <= cap else None


pairs = []
for sig in (mpf('0.5'), mpf('0.75'), mpf('0.9'), mpf('0.99')):
    M = opens_at(2, 1, sig, 2)
    assert M is not None, f"sigma={sig}: arc never opens"
    pairs.append((sig, -log(sig), M))
for sig, nl, M in pairs:
    print(f"  sigma={mp.nstr(sig,5)}  -log sigma={mp.nstr(nl,6)}  opens at M={M}")
# halving -log sigma should roughly double the threshold
for (s0, n0, M0), (s1, n1, M1) in zip(pairs, pairs[1:]):
    ratio_n = n0 / n1
    ratio_M = mpf(M1) / M0
    assert ratio_M <= 4 * ratio_n and ratio_M >= ratio_n / 4, (
        f"threshold scaling is not 1/(-log sigma): -log ratio {mp.nstr(ratio_n,4)} "
        f"against M ratio {mp.nstr(ratio_M,4)}")
print("PASS  the threshold is finite at every sigma < 1 and scales as "
      "1/(-log sigma), within a factor of 4 across three decades of margin -- so "
      "it is bounded for each pencil and unbounded as sigma -> 1, which is why "
      "no fixed ceiling is asserted")

print()
print("ALL PASS  check_dominance_admitted_set")
