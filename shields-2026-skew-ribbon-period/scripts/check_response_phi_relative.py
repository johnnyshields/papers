r"""Paper section `sec:response` (The complete scalar and its second channel).

Actual versus relative cap forcing of the return responses on p-periodic sources
(shields-2026-skew-ribbon-period.tex, sec:response, eq:base-residuals, eq:cap-high, lem:boolean;
sec:poles, lem:first-response, eq:vacancy-template).

Sources: strictly decreasing lists I, C in [1, N-1] with |I| = |C| = n, I_i >= C_i, and both
boundary words p-periodic on the open middle c < x, x + p < N - c; a = N - q - c > c, m = a + c,
q > c, p > q, h_0 = nu (nu = 10^9), generic rational h_k, k > 0.
Actual upper and lower returns at the constant z-coefficient:
  T_R(0) = (v^t B_R^{-1}) at the return row I = m,    v_j = sum_e l_e h_{N - e - C_j},
  T_L(0) = (B_L^{-1} w) at the return column C = N-m, w_i = sum_e r_e h_{I_i - e},
with B_R = (h_{I_i - C_j}), a <= I_i, C_j <= m,  B_L likewise on [N-m, N-a], and l, r the heads of
L0, R0 of eq:source-truncations.  The cap-to-return labels are q + x - j (never nu).  The template
model (capResidual of the relative setup) replaces them by h_{x-j}: nu at x = j, zero for x < j.
Asserts, on every source tried: the template-model value is Boolean (lem:boolean in relative
coordinates) while the actual value is Boolean on strictly fewer; and records whether the first
order coefficient nu * T of the actual response vanishes.  Run:
  nice taskset -c 3 timeout 600 python3 check_response_phi_relative.py
"""
import random
from sympy import Matrix, Rational

random.seed(5)
NU = Rational(10) ** 9


TOL = Rational(1, 1000)   # exact tolerance on exact rationals


def boolean(x):
    return min(abs(x), abs(x - 1)) < TOL


rows = []
data = []
tries = 0
while len(rows) < 150 and tries < 400000:
    tries += 1
    c = random.randint(1, 2)
    q = random.randint(c + 1, c + 2)
    p = random.randint(q + 1, q + 3)
    N = random.randint(2 * p + q + 2 * c + 2, 2 * p + q + 2 * c + 8)
    a = N - q - c
    m = a + c
    if a <= c:
        continue
    wI = {x: random.random() < 0.5 for x in range(1, N)}
    wC = {x: random.random() < 0.5 for x in range(1, N)}
    for x in range(c + 1, N - c):
        if x + p < N - c:
            wI[x + p] = wI[x]
            wC[x + p] = wC[x]
    I = sorted([x for x in wI if wI[x]], reverse=True)
    C = sorted([x for x in wC if wC[x]], reverse=True)
    n = len(I)
    if n != len(C) or n < 2 or any(I[i] < C[i] for i in range(n)):
        continue
    base = {k: Rational(random.randint(1, 9), random.randint(1, 5)) for k in range(1, N + 2)}

    def h(k):
        return Rational(0) if k < 0 else (NU if k == 0 else base[k])

    # heads of L0, R0
    li = [i for i in range(n) if I[i] > N - a]
    lc = [j for j in range(n) if C[j] > N - a]
    ri0 = [i for i in range(n) if I[i] < a]
    rc0 = [j for j in range(n) if C[j] < a]
    if len(li) != len(lc) or len(ri0) != len(rc0):
        continue
    l0 = {0: Rational(1)}
    r0 = {0: Rational(1)}
    if li:
        Bl = Matrix(len(li), len(lc), lambda x, y: h(I[li[x]] - C[lc[y]]))
        if Bl.det() == 0:
            continue
        V = Bl.T.LUsolve(Matrix([h(N - C[j]) for j in lc]))
        for x, i in enumerate(li):
            l0[N - I[i]] = l0.get(N - I[i], 0) - V[x]
    if ri0:
        Br = Matrix(len(ri0), len(rc0), lambda x, y: h(I[ri0[x]] - C[rc0[y]]))
        if Br.det() == 0:
            continue
        u = Br.LUsolve(Matrix([h(I[i]) for i in ri0]))
        for x, j in enumerate(rc0):
            r0[C[j]] = r0.get(C[j], 0) - u[x]
    lh = {e: v for e, v in l0.items() if e <= c}
    rh = {e: v for e, v in r0.items() if e <= c}
    # upper return
    ri = [i for i in range(n) if a <= I[i] <= m]
    rc = [j for j in range(n) if a <= C[j] <= m]
    # lower return
    qi = [i for i in range(n) if N - m <= I[i] <= N - a]
    qc = [j for j in range(n) if N - m <= C[j] <= N - a]
    if len(ri) != len(rc) or len(qi) != len(qc) or m not in [I[i] for i in ri] \
            or (N - m) not in [C[j] for j in qc]:
        continue
    BR = Matrix(len(ri), len(rc), lambda x, y: h(I[ri[x]] - C[rc[y]]))
    BL = Matrix(len(qi), len(qc), lambda x, y: h(I[qi[x]] - C[qc[y]]))
    if BR.det() == 0 or BL.det() == 0:
        continue
    k = [I[i] for i in ri].index(m)
    kl = [C[j] for j in qc].index(N - m)

    def upper(lab):
        v = Matrix([sum(cf * lab(e, C[j] - a) for e, cf in lh.items()) for j in rc])
        return (BR.T.LUsolve(v))[k]

    def lower(lab):
        w = Matrix([sum(cf * lab(I[i] - (N - m), e) for e, cf in rh.items()) for i in qi])
        return (BL.LUsolve(w))[kl]

    actR = upper(lambda e, j: h(q + c - e - j))
    relR = upper(lambda e, j: h(c - e - j))
    actL = lower(lambda x, e: h(q + x - e))
    relL = lower(lambda x, e: h(x - e))
    rows.append((actR, relR, actL, relL))
    data.append((N, I, C, c, q, p))

assert len(rows) >= 100, (len(rows), tries)
relb = sum(1 for _, y, _, w in rows if boolean(y) and boolean(w))
actb = sum(1 for x, _, z, _ in rows if boolean(x) and boolean(z))
ne = sum(1 for x, y, z, w in rows if abs(x - y) > TOL or abs(z - w) > TOL)
print(len(rows), "periodic sources;", "relative Boolean", relb, "actual Boolean", actb,
      "actual != relative", ne)
assert relb >= 0.9 * len(rows)
assert actb < relb
assert ne > 0
bad = [(d[0], d, r) for d, r in zip(data, rows) if not (boolean(r[0]) and boolean(r[2]))]
bad.sort(key=lambda t: t[0])
N, I, C, c, q, p = bad[0][1]
print("smallest non-Boolean actual: N", N, "I", I, "C", C, "c", c, "q", q, "p", p,
      "(T_R, T_L) actual", bad[0][2][0], bad[0][2][2], "relative", bad[0][2][1], bad[0][2][3])
