"""Full mate-space check of the two ten-negative quartet families.

Paper section `sec:threshold-boundaries`, `prop:ten-negative-quartet` (`eq:ten-profiles`).
CLAIM: for a >= 1, d >= 0, b > a + d, and i in {A, B}, the complete connected
class of F_i is exactly {F_i, F_i*, H_i, H_i*}, four distinct members, in the stratum
nu = 10, n_min = 7.  Profiles (rows; gaps), from the paper:
  F_A = (a+d, b+d, a+b+d, 2b+d, 2b+d, a+2b+d, 3b+d;  d, a+d, b+d, b+d, a+b+d, 2b+d)
  H_A = (a+d, b+d, a+b+d, 2b+d, a+2b+d, 3b+d, 2b+d;  d, a+d, b+d, a+b+d, 2b+d, b+d)
  F_B = (a+d, b+d, a+b+d, 2b+d, a+2b+d, a+2b+d, 3b+d; d, a+d, b+d, a+b+d, a+b+d, 2b+d)
  H_B = (a+d, b+d, a+b+d, 2b+d, a+2b+d, 3b+d, a+2b+d; d, a+d, b+d, a+b+d, 2b+d, a+b+d)

MECHANISM, not T's census: the class of F_i is computed over the FULL mate space -- every
arrangement of its rows and gaps (row/gap multisets are Schur invariants) -- by random
evaluation mod 2^61-1, and compared with the predicted set AS A SET.  nu and n_min are
computed here from the beta lists, not taken from the paper.  Parameters include
(a,b,d) = (2,5,1), outside T's span <= 16 census window.

Asserts per (family, parameters): stratum membership of all four; the computed class
equals the predicted four-member set; area matches 3a+11b+7d (A) or 4a+11b+7d (B);
zero-free exactly when d >= 1.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_separated_support_rigidity import arrangements, det_mod, POINTS, betas, rot, zero_free


def fam(i, a, b, d):
    if i == 'A':
        F = ((a+d, b+d, a+b+d, 2*b+d, 2*b+d, a+2*b+d, 3*b+d), (d, a+d, b+d, b+d, a+b+d, 2*b+d))
        H = ((a+d, b+d, a+b+d, 2*b+d, a+2*b+d, 3*b+d, 2*b+d), (d, a+d, b+d, a+b+d, 2*b+d, b+d))
    else:
        F = ((a+d, b+d, a+b+d, 2*b+d, a+2*b+d, a+2*b+d, 3*b+d), (d, a+d, b+d, a+b+d, a+b+d, 2*b+d))
        H = ((a+d, b+d, a+b+d, 2*b+d, a+2*b+d, 3*b+d, a+2*b+d), (d, a+d, b+d, a+b+d, 2*b+d, a+b+d))
    return F, H


def nu_rho(D):
    x, y = betas(*D)
    n = len(x)
    nu = sum(1 for i in range(n) for j in range(n) if x[i] < y[j])
    rho = tuple(sorted((sum(1 for j in range(n) if y[j] > x[i]) for i in range(n)), reverse=True))
    rho = tuple(r for r in rho if r)
    return nu, rho


def nmin(rho):
    return 1 + max(rho[i] + i + 1 for i in range(len(rho))) if rho else 1


def schur_class(src):
    sig = [det_mod(*src, pt) for pt in POINTS]
    return {c for c in arrangements(*src)
            if all(det_mod(*c, pt) == s for pt, s in zip(POINTS, sig))}


def main():
    for i in ('A', 'B'):
        for a, b, d in ((1, 2, 0), (1, 3, 1), (2, 5, 1)):
            F, H = fam(i, a, b, d)
            want = {F, rot(*F), H, rot(*H)}
            assert len(want) == 4, (i, a, b, d, "not four distinct")
            area = sum(F[0])
            assert area == (3 * a if i == 'A' else 4 * a) + 11 * b + 7 * d, (i, area)
            assert sum(H[0]) == area
            rhos = []
            for D in want:
                nu, rho = nu_rho(D)
                assert nu == 10 and nmin(rho) == 7, (i, D, nu, rho)
                rhos.append(rho)
            assert zero_free(*F) == (d >= 1), (i, a, b, d, "zero-free should hold iff d >= 1")
            got = schur_class(F)
            assert got == want, (i, a, b, d, sorted(got ^ want)[:4])
            print(f"PASS: family {i} (a,b,d)=({a},{b},{d}), {area} cells, "
                  f"{'zero-free' if d >= 1 else 'common betas'}: class = exactly the 4 predicted "
                  f"members; nu = 10, n_min = 7; partitions {sorted(set(rhos))}")
    print("ALL PASS")


if __name__ == "__main__":
    main()
