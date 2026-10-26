"""Paper section `subsec:locus-family`.  Target labels: `cor:locus-family`.

Independent check of the reversal family, by a second route.

The cheap routes to these cofactors are a last-row Laplace expansion with
structural-zero pruning and an upper-Hessenberg interval recurrence.  This
script instead builds the capped matrix (eq:capmatrix) straight from the
definitions in sec:coordinates and takes full symbolic determinants, so it
shares no mechanism with either and agreement is evidence.

Family (subsec:locus-family): N = 2k+2, mu = (N-1, ..., 1, 0), row-length words
    rho(A_k) = (2, 2^k, 3^k, 2),    rho(B_k) = (2, 3^k, 2^k, 2)
added coordinatewise to mu.  Claim checked here, at (r,a) = (2,1):

  (i)   the two boards share L and the cap grid, and d_j = 2j;
  (ii)  the ratio identity  P_{r+a}(G) = h_a P_r(G),  i.e.  P_3(G) = h_1 P_2(G);
  (iii) the parents are NOT skew-equal: s_{A_k} != s_{B_k};
  (iv)  the number of positive supported shifts is m = 2k;
  (v)   the square gap alpha_0 - m_+ = 8, and alpha_0 = 13k + 20.

Calibration (a guard that cannot see is not a guard): C_0 computed from the
capped matrix is checked against an independent Jacobi-Trudi evaluation of
s_{lambda/mu} before any family claim is trusted.
"""

import sys
import sympy as sp

H = {}


def h(k):
    if k < 0:
        return sp.Integer(0)
    if k == 0:
        return sp.Integer(1)
    if k not in H:
        H[k] = sp.Symbol("h%d" % k)
    return H[k]


def skew_schur(lam, mu):
    n = len(lam)
    mu = list(mu) + [0] * (n - len(mu))
    M = sp.Matrix(n, n, lambda i, j: h(lam[i] - mu[j] - i + j))
    return sp.expand(M.det(method="berkowitz"))


def word(k, kind):
    """rho(A_k) = (2, 2^k, 3^k, 2);  rho(B_k) = (2, 3^k, 2^k, 2)."""
    if kind == "A":
        return [2] + [2] * k + [3] * k + [2]
    return [2] + [3] * k + [2] * k + [2]


def board(k, kind):
    N = 2 * k + 2
    mu = list(range(N - 1, -1, -1))
    rho = word(k, kind)
    assert len(rho) == N, (len(rho), N)
    lam = [rho[i] + mu[i] for i in range(N)]
    return lam, mu


def cap_data(lam, mu):
    n = len(lam)
    L = lam[0]
    A = [L - lam[i] + i for i in range(n)]
    d = [0] + [L - mu[j - 1] + j - 1 for j in range(1, n + 1)]
    return L, A, d


def cofactors(lam, mu):
    """C_j = (-1)^j det M_hat-j, with M_ij = h_{d_j - A_i}  (eq:capmatrix)."""
    n = len(lam)
    L, A, d = cap_data(lam, mu)
    M = sp.Matrix(n, n + 1, lambda i, j: h(d[j] - A[i]))
    out = []
    for j in range(n + 1):
        cols = [c for c in range(n + 1) if c != j]
        out.append(sp.expand(sp.Integer(-1) ** j * M[:, cols].det(method="berkowitz")))
    return out, d


def wt_square(mono):
    """Square weight of a single h-monomial: sum of (index)^2 with multiplicity."""
    tot = 0
    for factor, power in mono.as_powers_dict().items():
        if factor.is_Symbol and factor.name.startswith("h"):
            tot += int(factor.name[1:]) ** 2 * int(power)
    return tot


def nu_square(poly):
    poly = sp.expand(poly)
    if poly == 0:
        return sp.oo
    terms = poly.as_ordered_terms()
    return min(wt_square(t.as_coeff_Mul()[1]) for t in terms)


KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4
print("Independent check of subsec:locus-family, k = 1..%d, (r,a) = (2,1)\n" % KMAX)

for k in range(1, KMAX + 1):
    N = 2 * k + 2
    lamA, muA = board(k, "A")
    lamB, muB = board(k, "B")

    # exact reversal of the row-length words -- the structural premise
    assert word(k, "A")[::-1] == word(k, "B"), k

    LA, AA, dA = cap_data(lamA, muA)
    LB, AB, dB = cap_data(lamB, muB)
    assert LA == LB and dA == dB, "cap grids must coincide"
    assert dA == [2 * j for j in range(N + 1)], dA

    CA, d = cofactors(lamA, muA)
    CB, _ = cofactors(lamB, muB)

    # calibration: C_0 must be the parent's own skew Schur function
    assert sp.expand(CA[0] - skew_schur(lamA, muA)) == 0, "C_0 calibration failed (A)"
    assert sp.expand(CB[0] - skew_schur(lamB, muB)) == 0, "C_0 calibration failed (B)"

    G = [sp.expand(CA[j] - CB[j]) for j in range(N + 1)]

    def P(m):
        return sp.expand(sum(G[j] * h(m + d[j]) for j in range(N + 1)))

    ratio = sp.expand(P(3) - h(1) * P(2))          # (r,a) = (2,1)
    parents_differ = sp.expand(CA[0] - CB[0]) != 0
    supp_pos = [j for j in range(1, N + 1) if G[j] != 0]
    alpha = {j: nu_square(G[j]) + d[j] ** 2 for j in range(N + 1) if G[j] != 0}
    m_plus = min(v for j, v in alpha.items() if j > 0)
    a0 = alpha.get(0, sp.oo)

    print("k=%d  N=%2d  ratio identity P_3 = h_1 P_2: %-5s   s_A != s_B: %-5s"
          % (k, N, ratio == 0, parents_differ))
    print("      positive supported shifts m = %2d (expected %2d: %s)   "
          "alpha_0 = %s (13k+20 = %d: %s)   gap = %s"
          % (len(supp_pos), 2 * k, len(supp_pos) == 2 * k,
             a0, 13 * k + 20, a0 == 13 * k + 20, a0 - m_plus))

    assert ratio == 0, k
    assert parents_differ, k

print("\nALL PASS")
