"""Out-of-window rigidity sample for the ten-negative theorem.

Paper section `sec:ten-negative`, `thm:ten-negative-classification`.
CLAIM: every connected D with nu = 10, n_min = 7 is rotation-rigid except the
four-member classes of families A and B.  T's census covers seven rows with span <= 16.

This samples seven-row sources OUTSIDE that window (span 17..40), common betas allowed,
and computes each class over the FULL mate space (every valid row/gap arrangement; the
multisets are Schur invariants) by random evaluation mod 2^61-1.  A source not in family A
or B must have class exactly {D, D*}; a family member must have exactly four members.

Coverage is asserted, not assumed: every one of the 8 conjugation orbits must be hit, and
at least 150 sources tested.  This is a random sample, not an exhaustive census.
"""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_separated_support_rigidity import arrangements, det_mod, POINTS, betas, rot
from check_ten_negative_full_mate_space import fam, nu_rho, nmin


def conj(p):
    return tuple(sum(1 for x in p if x > j) for j in range(p[0])) if p else ()


def schur_class(src):
    sig = [det_mod(*src, pt) for pt in POINTS]
    return {c for c in arrangements(*src)
            if all(det_mod(*c, pt) == s for pt, s in zip(POINTS, sig))}


def family_members():
    """All family members over a parameter box larger than any sampled span needs."""
    out = set()
    for a in range(1, 14):
        for d in range(0, 14):
            for b in range(a + d + 1, 16):
                for i in 'AB':
                    F, H = fam(i, a, b, d)
                    out |= {F, rot(*F), H, rot(*H)}
    return out


def main():
    rng = random.Random(20260924)
    fams = family_members()
    tested, orbits, exceptional = 0, set(), 0
    tries = 0
    while tested < 150 or len(orbits) < 8:
        tries += 1
        assert tries < 3_000_000, f"sampling stalled: {tested} tested, orbits {sorted(orbits)}"
        rows = tuple(rng.randint(1, 12) for _ in range(7))
        gaps = tuple(rng.randint(0, min(rows[k], rows[k + 1]) - 1) for k in range(6))
        D = (rows, gaps)
        x, y = betas(*D)
        span = x[0] - y[-1]
        if not 17 <= span <= 40:
            continue
        nu, rho = nu_rho(D)
        if nu != 10 or nmin(rho) != 7:
            continue
        orb = frozenset({rho, conj(rho)})
        if orb in orbits and tested >= 150:
            continue
        cls = schur_class(D)
        if D in fams:
            assert len(cls) == 4, (D, len(cls))
            exceptional += 1
        else:
            assert cls == {D, rot(*D)}, ("NONRIGID OUTSIDE A/B", D, sorted(cls - {D, rot(*D)})[:3])
        tested += 1
        orbits.add(orb)
    print(f"PASS: {tested} seven-row sources with nu = 10, n_min = 7, span 17..40, from all "
          f"{len(orbits)} conjugation orbits: every non-family source rotation-rigid over its full "
          f"mate space; {exceptional} family members hit, each with exactly 4 members")
    print("ALL PASS")


if __name__ == "__main__":
    main()
