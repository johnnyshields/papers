"""Paper section `subsec:locus-family`.  Target labels: `rem:staircase-boundary`.

Cross-check of the boundary-3 exclusion argument of the remark.  A failed
identity here refutes the bridge the remark prints.

Everything is rebuilt from the lambda/mu and capped-matrix definitions of
sec:coordinates; nothing is imported from the other checks in this directory.

Checks, over every ordered w = (3, interior, 3) with interior in {2,3}^(N-2):

  1. grid:      d_0 = 0 and d_j = 2j+1 for j >= 1   (false at j = 0)
  2. bridge:    h_1 P_r(C(X_w)) = D(r+1,w) + (h_1 h_r - h_{r+1}) D(w),  r = 1,2,3
  3. relation:  h_1 P_2(G) - h_1^2 P_1(G) + e_3 G_0 = 0,  e_3 = h_1^3 - 2h_1h_2 + h_3
  4. nonpalindromes:  G_0 != 0  and  P_3(G) - h_1 P_2(G) != 0
  5. calibration at w = (3,2,3,3):  nu(G_0) = 43, nu(P_1(G)) = 44, nu(P_2(G)) = 47,
     so the three terms of (3) carry valuations 48, 46, 46 -- a TIE, which is what
     lets the relation vanish for an actual word.  The proof's contradiction is in
     the hypothetical case, where the assumed ratio identity forces a UNIQUE
     minimum instead; these numbers are not that case and must not be read as it.
"""

import itertools
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


def wt(mono):
    t = 0
    for f, p in mono.as_powers_dict().items():
        if f.is_Symbol and f.name.startswith("h"):
            t += int(f.name[1:]) ** 2 * int(p)
    return t


def nu(poly):
    poly = sp.expand(poly)
    if poly == 0:
        return None
    return min(wt(t.as_coeff_Mul()[1]) for t in poly.as_ordered_terms())


def cofactors(w):
    N = len(w)
    mu = list(range(N - 1, -1, -1))
    lam = [w[i] + mu[i] for i in range(N)]
    L = lam[0]
    A = [L - lam[i] + i for i in range(N)]
    d = [0] + [L - mu[j - 1] + j - 1 for j in range(1, N + 1)]
    M = sp.Matrix(N, N + 1, lambda i, j: h(d[j] - A[i]))
    C = [sp.expand(sp.Integer(-1) ** j
                   * M[:, [c for c in range(N + 1) if c != j]].det(method="berkowitz"))
         for j in range(N + 1)]
    return C, d


def P_of(C, d, r):
    return sp.expand(sum(C[j] * h(r + d[j]) for j in range(len(C))))


def D(rho):
    n = len(rho)
    if n == 0:
        return sp.Integer(1)
    return sp.expand(sp.Matrix(n, n,
                     lambda i, j: h(rho[i] + 2 * (j - i))).det(method="berkowitz"))


E3 = sp.expand(h(1) ** 3 - 2 * h(1) * h(2) + h(3))
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7

print("Boundary-3 exclusion cross-check, N = 4..%d\n" % NMAX)
for N in range(4, NMAX + 1):
    grid = bridge = rel = nz = tot = npal = 0
    for interior in itertools.product((2, 3), repeat=N - 2):
        w = [3] + list(interior) + [3]
        ws = w[::-1]
        C, d = cofactors(w)
        tot += 1

        grid += (d[0] == 0 and all(d[j] == 2 * j + 1 for j in range(1, N + 1)))

        okb = True
        for r in (1, 2, 3):
            lhs = sp.expand(h(1) * P_of(C, d, r))
            rhs = sp.expand(D([r + 1] + w) + (h(1) * h(r) - h(r + 1)) * D(w))
            okb &= sp.expand(lhs - rhs) == 0
        bridge += okb

        Cs, ds = cofactors(ws)
        G = [sp.expand(C[j] - Cs[j]) for j in range(N + 1)]
        P1 = P_of(G, d, 1)
        P2 = P_of(G, d, 2)
        P3 = P_of(G, d, 3)
        rel += sp.expand(h(1) * P2 - h(1) ** 2 * P1 + E3 * G[0]) == 0

        if w != ws:
            npal += 1
            nz += (G[0] != 0 and sp.expand(P3 - h(1) * P2) != 0)

    print("  N=%d (%2d words, %2d nonpalindromic):  grid %2d/%2d   bridge %2d/%2d   "
          "relation %2d/%2d   G_0!=0 and ratio fails %2d/%2d"
          % (N, tot, npal, grid, tot, bridge, tot, rel, tot, nz, npal))
    assert grid == bridge == rel == tot, N
    assert nz == npal, N

print("\nCalibration at w = (3,2,3,3):")
w = [3, 2, 3, 3]
C, d = cofactors(w)
Cs, _ = cofactors(w[::-1])
G = [sp.expand(C[j] - Cs[j]) for j in range(len(C))]
P1 = P_of(G, d, 1)
P2 = P_of(G, d, 2)
n0, n1, n2 = nu(G[0]), nu(P1), nu(P2)
print("  nu(G_0)      = %s  (claimed 43)  %s" % (n0, n0 == 43))
print("  nu(P_1(G))   = %s  (claimed 44)  %s" % (n1, n1 == 44))
print("  nu(P_2(G))   = %s  (claimed 47)  %s" % (n2, n2 == 47))
terms = (nu(sp.expand(h(1) * P2)), nu(sp.expand(h(1) ** 2 * P1)), nu(sp.expand(E3 * G[0])))
print("  term valuations = %s  (claimed 48, 46, 46 -- a tie, so the sum can vanish)"
      % (terms,))
assert (n0, n1, n2) == (43, 44, 47)
assert terms == (48, 46, 46)

init = sp.expand(h(1) * P2 - P_of(G, d, 3))
lo = nu(init)
form = sum(t for t in init.as_ordered_terms() if wt(t.as_coeff_Mul()[1]) == lo)
print("  in_wt(h_1 P_2(G) - P_3(G)) = %s  (claimed -h1^3 h2 h4 h5)  %s"
      % (sp.factor(form), sp.expand(form + h(1) ** 3 * h(2) * h(4) * h(5)) == 0))
assert sp.expand(form + h(1) ** 3 * h(2) * h(4) * h(5)) == 0

print("\nALL PASS")
