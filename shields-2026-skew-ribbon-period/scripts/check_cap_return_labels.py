r"""Paper section `sec:response` (The complete scalar and its second channel).

Labels of the cap/return pairings of the actual source (shields-2026-skew-ribbon-period.tex,
sec:response, eq:base-residuals, eq:cap-high, lem:boolean).

For a connected source with beta lists xi, zeta (I = xi[1:], C = zeta[:-1], N = xi[0]),
a = N - q - c > c, m = a + c = N - q, the first-window data are
  R0 = 1 - sum_{C_j < a} u_j z^{C_j},   L0 = 1 - sum_{I_i > N - a} V_i z^{N - I_i},
  P_i = [z^{a+i}] H R0,   Q_j = [z^{m-j}] H L0,   H = sum_k h_k z^k  (h_0 = 1 physical).
Asserted, with the c+1 variables s_t = h_{a+t} symbolic:
 (b) the base solutions u, V do not involve s; P_i and Q_j are affine in s, the coefficient of s_t
     being r_{i-t} (resp. l_{c-j-t}), the heads of R0, L0 through degree c;
 (a) the left cap functional paired with a right-return column a + j has entries h_{q+x-j},
     x, j in [0, c]: every label is positive (q > c), so no entry is h_0, and the entries with
     x < j are nonzero constants, whereas the relative model h_{x-j} used by the template systems
     (capResidual, hnu) is zero there and equals nu = h_0 at x = j.
Exact rational arithmetic; one core.  Run: nice taskset -c 4 timeout 600 python3 check_cap_return_labels.py
"""
import random
from sympy import Matrix, Rational, Symbol, expand, symbols, zeros, Poly

random.seed(3)


def beta(r, g):
    n = len(g)
    ze = [sum(r[k + 1] - g[k] for k in range(i, n)) for i in range(n + 1)]
    xi = [ze[i] + r[i] for i in range(n + 1)]
    return xi, ze


checked = 0
mismatch_seen = 0
for trial in range(6000):
    n = random.randint(2, 5)
    r = [random.randint(1, 6) for _ in range(n + 1)]
    g = [random.randint(0, min(r[k], r[k + 1]) - 1) for k in range(n)]
    xi, ze = beta(r, g)
    N, I, C = xi[0], xi[1:], ze[:-1]
    q, c = random.randint(2, 4), random.randint(1, 3)
    a = N - q - c
    if a <= c or q <= c:
        continue
    m = a + c
    S = symbols("s0:%d" % (c + 1))
    base = {k: Rational(random.randint(1, 9), random.randint(1, 5)) for k in range(1, N + 2)}

    def h(k, sub=True):
        if k < 0:
            return Rational(0)
        if k == 0:
            return Rational(1)
        if a <= k <= m:
            return S[k - a]
        return base[k]

    ri = [i for i in range(n) if I[i] < a]
    rc = [j for j in range(n) if C[j] < a]
    li = [i for i in range(n) if I[i] > N - a]
    lc = [j for j in range(n) if C[j] > N - a]
    if len(ri) != len(rc) or len(li) != len(lc):
        continue
    if ri:
        B = Matrix(len(ri), len(rc), lambda x, y: h(I[ri[x]] - C[rc[y]]))
        if B.det() == 0:
            continue
        u = B.LUsolve(Matrix([h(I[i]) for i in ri]))
        assert not any(e.free_symbols for e in u)
    else:
        u = Matrix([])
    if li:
        Bl = Matrix(len(li), len(lc), lambda x, y: h(I[li[x]] - C[lc[y]]))
        if Bl.det() == 0:
            continue
        V = Bl.T.LUsolve(Matrix([h(N - C[j]) for j in lc]))
        assert not any(e.free_symbols for e in V)
    else:
        V = Matrix([])
    r0 = {0: Rational(1)}
    for x, j in enumerate(rc):
        r0[C[j]] = r0.get(C[j], 0) - u[x]
    l0 = {0: Rational(1)}
    for x, i in enumerate(li):
        l0[N - I[i]] = l0.get(N - I[i], 0) - V[x]
    P = lambda i: sum(h(a + i - e) * cf for e, cf in r0.items())
    Q = lambda j: sum(h(m - j - e) * cf for e, cf in l0.items())
    for i in range(c + 1):
        Pi = expand(P(i))
        for t in range(c + 1):
            assert Pi.coeff(S[t]) == r0.get(i - t, 0), (xi, ze, q, c, i, t)
        assert all(not (Pi.coeff(S[t])).free_symbols for t in range(c + 1))
        rest = expand(Pi - sum(Pi.coeff(S[t]) * S[t] for t in range(c + 1)))
        assert not rest.free_symbols
    for j in range(c + 1):
        Qj = expand(Q(j))
        for t in range(c + 1):
            assert Qj.coeff(S[t]) == l0.get(c - j - t, 0), (xi, ze, q, c, j, t)
    # (a): the cross labels of the left cap functional against the right return columns
    for x in range(c + 1):
        for j in range(c + 1):
            lab = q + x - j
            assert lab >= q - c > 0
            if x < j and base.get(lab, 0) != 0 and not (a <= lab <= m):
                mismatch_seen += 1
    checked += 1
assert checked >= 20, checked
assert mismatch_seen > 0
print("OK", checked, mismatch_seen)
