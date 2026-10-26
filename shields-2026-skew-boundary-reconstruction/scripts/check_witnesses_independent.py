"""Paper sections `subsec:intro-main` and `rem:one-extension-insufficient`.
Target labels: `ex:actual-equal-chain`.

Independent check of the three witness pairs asserted in the front matter.

Route: build the Jacobi-Trudi matrix directly from lambda/mu and expand the
determinant symbolically over Z[h_1, h_2, ...], with h_0 = 1 and h_k = 0 for
k < 0.  Nothing is imported from the paper's other scripts; the diagrams and
the claimed differences are transcribed from the manuscript text alone.

Checks:
  1. subsec:intro-main   U = (7,7,5,4)/(6,4,2,0), V = (7,7,6,3)/(6,4,2,0):
                         s_U = s_V, and s_Ubar - s_Vbar = h_3 h_7 - h_4 h_6.
  2. ex:actual-equal-chain  X = (4,4,4,2)/(3,2,1,0), Y = (4,4,3,3)/(3,2,1,0):
                         s_X = s_Y.
  3. rem:one-extension-insufficient, a = 1, 2, 3:
                         s_{U_a.(a)} = s_{V_a.(a)} while
                         s_{U_a} - s_{V_a} = h_{3a} h_{4a} - h_{2a} h_{5a} != 0.
"""

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
    """Jacobi-Trudi: s_{lam/mu} = det( h_{lam_i - mu_j - i + j} ), 1-based i,j."""
    n = len(lam)
    mu = list(mu) + [0] * (n - len(mu))
    M = sp.Matrix(n, n, lambda i, j: h(lam[i] - mu[j] - i + j))
    return sp.expand(M.det(method="berkowitz"))


def delete_first_row(lam, mu):
    """Delete the entire first row: drop lam_0 and mu_0."""
    return list(lam[1:]), list(mu[1:])


def northeast_extend(lam, mu, a):
    """X.(a): a new top row of length a meeting the old top row in one column.

    The new row occupies columns [lam_0 - 1, lam_0 - 1 + a) in lam-coordinates,
    so the new outer boundary is (lam_0 - 1 + a, lam_0, lam_1, ...) and the new
    inner boundary is (lam_0 - 1, mu_0, mu_1, ...).
    """
    return [lam[0] - 1 + a] + list(lam), [lam[0] - 1] + list(mu)


def report(name, expr, expected=None):
    if expected is None:
        ok = expr == 0
        print("  %-46s %s" % (name, "= 0  OK" if ok else "NONZERO  FAIL: %s" % expr))
        assert ok, name
    else:
        diff = sp.expand(expr - expected)
        ok = diff == 0
        print("  %-46s %s" % (name, "matches  OK" if ok else "MISMATCH  %s" % expr))
        assert ok, name


print("1. subsec:intro-main overlap-hierarchy witness")
U, Umu = [7, 7, 5, 4], [6, 4, 2, 0]
V, Vmu = [7, 7, 6, 3], [6, 4, 2, 0]
report("s_U - s_V", sp.expand(skew_schur(U, Umu) - skew_schur(V, Vmu)))
Ub, Ubm = delete_first_row(U, Umu)
Vb, Vbm = delete_first_row(V, Vmu)
report(
    "s_Ubar - s_Vbar  vs  h3 h7 - h4 h6",
    sp.expand(skew_schur(Ub, Ubm) - skew_schur(Vb, Vbm)),
    sp.expand(h(3) * h(7) - h(4) * h(6)),
)

print("2. ex:actual-equal-chain")
X, Xmu = [4, 4, 4, 2], [3, 2, 1, 0]
Y, Ymu = [4, 4, 3, 3], [3, 2, 1, 0]
report("s_X - s_Y", sp.expand(skew_schur(X, Xmu) - skew_schur(Y, Ymu)))

print("3. rem:one-extension-insufficient, a = 1, 2, 3")
for a in (1, 2, 3):
    m = [4 * a - 2, 2 * a - 1, 0]
    Ua = [6 * a - 2, 5 * a - 1, 2 * a]
    Va = [6 * a - 2, 4 * a - 1, 3 * a]
    Ue, Uem = northeast_extend(Ua, m, a)
    Ve, Vem = northeast_extend(Va, m, a)
    report(
        "a=%d  s_{U.(a)} - s_{V.(a)}" % a,
        sp.expand(skew_schur(Ue, Uem) - skew_schur(Ve, Vem)),
    )
    report(
        "a=%d  s_U - s_V  vs  h_3a h_4a - h_2a h_5a" % a,
        sp.expand(skew_schur(Ua, m) - skew_schur(Va, m)),
        sp.expand(h(3 * a) * h(4 * a) - h(2 * a) * h(5 * a)),
    )

print("ALL PASS")

# ---------------------------------------------------------------------------
# 4. subsec:child-separation: the diagrams (3+t,3)/(t,0), t = 0,1,2, are said
#    to share the row-length multiset {3,3} and to be "separated only by the
#    second observation".  Check both halves: are the s_X themselves already
#    distinct, and do the first-row deletions separate them?
# ---------------------------------------------------------------------------
print("4. subsec:child-separation example (3+t,3)/(t,0)")
fams = {}
for t in (0, 1, 2):
    lam, mu = [3 + t, 3], [t, 0]
    rows = [lam[0] - mu[0], lam[1] - mu[1]]
    sX = skew_schur(lam, mu)
    lb, mb = delete_first_row(lam, mu)
    sXbar = skew_schur(lb, mb)
    fams[t] = (sX, sXbar)
    print("   t=%d  rows=%s  s_X = %s   s_Xbar = %s" % (t, rows, sX, sXbar))
for t1 in (0, 1, 2):
    for t2 in (0, 1, 2):
        if t1 < t2:
            dX = sp.expand(fams[t1][0] - fams[t2][0])
            dB = sp.expand(fams[t1][1] - fams[t2][1])
            print("   t=%d vs t=%d:  s_X differ? %-5s   s_Xbar differ? %s"
                  % (t1, t2, dX != 0, dB != 0))

# ---------------------------------------------------------------------------
# 5. subsec:child-separation summary: "read n and d_1 off the initial monomial
#    of C_0".  Witness that C_0 -- let alone its initial monomial -- does not
#    determine d_1.  By (eq:dexplicit), d_1 = L - mu_0 with L = lambda_0.
# ---------------------------------------------------------------------------
print("5. Does C_0 determine d_1?")
for lam, mu, name in (([2, 1], [0, 0], "(2,1)"), ([2, 2], [1, 0], "(2,2)/(1,0)")):
    C0 = skew_schur(lam, mu)
    d1 = lam[0] - mu[0]
    rho = [lam[i] - mu[i] for i in range(len(lam))]
    o0 = lam[1] - mu[0]
    print("   %-12s C_0 = %-18s d_1 = %d   rows=%s  overlap o_0=%d (connected: %s)"
          % (name, C0, d1, rho, o0, o0 >= 1))
A = skew_schur([2, 1], [0, 0])
B = skew_schur([2, 2], [1, 0])
assert sp.expand(A - B) == 0, "C_0 should coincide"
print("   C_0 coincide: %s        d_1 differ: 2 vs 1  ->  C_0 does NOT determine d_1"
      % (sp.expand(A - B) == 0))
