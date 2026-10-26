"""Coordinator's arbitrary-mate check of lane X's four-row consequence (round 169).

CLAIM (r169-x.md): every positive constant-gap Hessenberg inner with at most four rows has
    Cl(I_t F_alpha(E)) = {I_t F_beta, (I_t F_beta)* : r_beta = r_alpha}   for 0 <= t < p,
                       = {I_t F_alpha, (I_t F_alpha)*}                  for t >= p,
p = min(r_1 - c, r_n - c).  X proved the WITHIN-IMAGE wall theorem and derived this from
held results (thm:five-row-classification for P(E), thm:exposure, thm:main).

MECHANISM, not X's: the FULL mate space.  Row- and gap-multisets are Schur invariants, so
every connected mate of a source is an arrangement of its rows and gaps; all are
enumerated and separated by random evaluation mod 2^61-1 (a differing value proves
inequality).  X's scripts compare the image of one inner only; this compares against
every diagram with the same row and gap multisets.

Definitions, from the papers:
  I_t(r; g) = (r_1+t, ..., r_n+t; g_1+t, ..., g_{n-1}+t)     (skew-class-inflation, l.139)
  E_m = (a, I, (a+b, I)^{m-1}, b; G^m),  F_alpha = E_{alpha_1} .0 E_{alpha_2} .0 ...

Asserts, for X's nonsymmetric witness E = (2,4,5,2;1,1,1) (p = 1) and a second
nonsymmetric constant-gap inner E = (3,4,5,3;1,1,1) (p = 2), alpha = (1,2):
  (1) pre-wall t < p: the class is exactly the four predicted members;
  (2) at the wall t = p and at t = p+1: the class is exactly {source, rotation};
  (3) CONTROL that must fire: at t = 0 the rotation-only prediction is rejected.
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_r168_coord_separated_support import arrangements, det_mod, POINTS, rot
from check_r168_coord_general_exposure import F


def inflate(D, t):
    rows, gaps = D
    return tuple(r + t for r in rows), tuple(g + t for g in gaps)


def schur_class(src):
    sig = [det_mod(*src, pt) for pt in POINTS]
    return {c for c in arrangements(*src)
            if all(det_mod(*c, pt) == s for pt, s in zip(POINTS, sig))}


def main():
    fired = 0
    cases = [(((2, 4, 5, 2), (1, 1, 1)), 1), (((3, 4, 5, 3), (1, 1, 1)), 2)]
    alpha, rev = (1, 2), (2, 1)
    for E, p in cases:
        rows, gaps = E
        assert p == min(rows[0] - gaps[0], rows[-1] - gaps[-1]), (E, p)
        assert E != (tuple(reversed(rows)), tuple(reversed(gaps))), "inner must be nonsymmetric"
        for t in sorted({0, p - 1, p, p + 1}):
            if t < 0:
                continue
            src = inflate(F(E, alpha), t)
            got = schur_class(src)
            if t < p:
                other = inflate(F(E, rev), t)
                want = {src, rot(*src), other, rot(*other)}
                label = "pre-wall"
            else:
                want = {src, rot(*src)}
                label = "wall" if t == p else "post-wall"
            assert got == want, (E, t, label, sorted(got ^ want)[:4])
            print(f"PASS: E={E} p={p} t={t} ({label}, {sum(src[0])} cells): class has exactly "
                  f"the {len(want)} predicted members")
            if t == 0:
                assert got != {src, rot(*src)}, "CONTROL DID NOT FIRE"
                fired += 1
    assert fired == len(cases)
    print(f"PASS (control fires): the rotation-only prediction is rejected at t = 0 in {fired} cases")
    print("ALL PASS")


if __name__ == "__main__":
    main()
