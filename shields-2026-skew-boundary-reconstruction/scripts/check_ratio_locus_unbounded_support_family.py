"""The ratio-identity locus is populated well past the two-support configuration.

SCOPE.  This checks k = 1, 2, 3 exactly, by the cheap `skew_core` recurrences.  `cor:locus-family`
is proved for every k from `prop:staircase-reversal` and `lem:two-series-reversal`; the
all-k determinant identity is covered by `check_locus_family_census.py` and the full symbolic
determinants by `check_locus_family_independent.py`.  The members here grow in LENGTH rather than
by scaling (unlike the dilation family of subsec:floor-margin), so no substitution carries one
to the next.

WHY.  The Strict-Monge ratio-rigidity theorem is stated on the ratio-identity locus with no bound
on the number of changed rows or supported cap shifts, and every guard that exists for it is a
guard for the CAP-FIXED theorem instead -- whose antecedent alpha_0 > m_+ is assumed rather than
supplied by an identity.  So the locus itself has never been shown to reach beyond the trivial
two-support configuration, and a theorem about a locus that is populated only trivially in range
is worth exactly as much as its population.

WHAT IS CHECKED.  The staircase family: with N = 2k+2, mu = (N-1, ..., 1, 0) and row-length words

    rho(A_k) = (2, 2^k, 3^k, 2),      rho(B_k) = (2, 3^k, 2^k, 2),

added coordinatewise to mu.  For each k the assertions are, in exact integer arithmetic:

  (1) both shapes are connected, share mu, and have equal row-length multisets;
  (2) G = C(A) - C(B) is nonzero and G_0 != 0;
  (3) the ratio identity P_3(G) = h_1 P_2(G) holds exactly, i.e. (r, a) = (2, 1);
  (4) the number of positive supported shifts is m = 2k, hence 2, 4 and 6 over the
      three cases checked;
  (5) the ratio-rigidity conclusion holds: T_0^+ = {d_1, d_2} and
      alpha_0 > alpha_1 = alpha_2 < alpha_3 < ... , with every later supported coordinate higher;
  (6) alpha_0 - m_+ = 2*gamma*d_1 with gamma = r = 2, the exact square gap.

k = 1, 2, 3 only: det_h expands over all n! permutations and N = 2k+2 rows, so k = 4 is a
10x10 determinant per cofactor.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from skew_core import cofactors, padd, pmul, h, Pk                        # noqa: E402


def wt(p):
    """Square valuation: min over monomials of sum of squared indices."""
    if not p:
        return None
    return min(sum(j * j for j in m) for m in p)


def family(k):
    N = 2 * k + 2
    mu = tuple(range(N - 1, -1, -1))
    rhoA = (2,) + (2,) * k + (3,) * k + (2,)
    rhoB = (2,) + (3,) * k + (2,) * k + (2,)
    lamA = tuple(m + r for m, r in zip(mu, rhoA))
    lamB = tuple(m + r for m, r in zip(mu, rhoB))
    return (lamA, mu), (lamB, mu), rhoA, rhoB


def connected(sh):
    lam, mu = sh
    return all(lam[i + 1] > mu[i] for i in range(len(lam) - 1))


for k in (1, 2, 3):
    A, B, rhoA, rhoB = family(k)
    assert connected(A) and connected(B), (k, "not connected")
    assert A[1] == B[1], (k, "inner boundaries differ")
    assert sorted(rhoA) == sorted(rhoB), (k, "row multisets differ")
    assert rhoA != rhoB, (k, "shapes coincide")

    CA, CB = cofactors(A), cofactors(B)
    shifts = sorted(set(CA) | set(CB))
    assert sorted(CA) == sorted(CB), (k, "shift grids differ")
    G = {}
    for d in shifts:
        g = padd(CA.get(d, {}), CB.get(d, {}), -1)
        if g:
            G[d] = g
    assert G, (k, "defect vanishes")
    assert 0 in G, (k, "G_0 vanishes")

    r, a = 2, 1
    lhs, rhs = Pk(G, r + a), pmul(h(a), Pk(G, r))
    assert padd(lhs, rhs, -1) == {}, (k, "ratio identity fails")

    pos = sorted(d for d in G if d > 0)
    assert len(pos) == 2 * k, (k, "support count", len(pos), 2 * k)

    alpha = {d: wt(G[d]) + d * d for d in G}
    m_plus = min(alpha[d] for d in pos)
    T0 = sorted(d for d in pos if alpha[d] == m_plus)
    assert T0 == pos[:2], (k, "floor set is not {d_1, d_2}", T0, pos[:2])
    assert alpha[0] > m_plus, (k, "floor antecedent fails")
    prof = [alpha[d] for d in pos]
    assert prof[0] == prof[1], (k, "adjacent tie fails", prof)
    assert all(prof[i] < prof[i + 1] for i in range(1, len(prof) - 1)), (k, "profile", prof)
    assert alpha[0] - m_plus == 2 * r * pos[0], (k, "square gap", alpha[0] - m_plus, 2 * r * pos[0])

    print("k=%d  N=%2d  A=%s/%s  supports=%s  alpha=%s  T0+=%s  alpha_0=%d  gap=%d"
          % (k, 2 * k + 2, A[0], A[1], pos, [alpha[d] for d in sorted(G)], T0,
             alpha[0], alpha[0] - m_plus))

print("PASS")
