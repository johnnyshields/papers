r"""Paper section `sec:response` (The complete scalar and its second channel).

Check of the core bridge (shields-2026-skew-ribbon-period.tex, sec:response, eq:base-residuals,
eq:cap-high): on sampled periodic sources, the unweighted return solution `x_R^u` (the system
`sum_i h_{I_i - C_j} xi_i = [z^{m - C_j}] H L0`, rows `I in [a, m]`, columns `C in [a, m]`) is the
core projection of the template: with the cap vector `l_i = -v_i` on the rows `I_i in [N - c, N)`
(relative `I_i - (N - c)`) the template residual at the relative column `j = C_j - a`,

    capResidual(j) = h_{c - j}[c - j > 0] + sum_i l_i h_{i - j},

equals `[z^{m - C_j}] H L0` for every window column, and the projection of the residual on the
window rows has the coefficients `xi_i` at the relative labels `I_i - a`.  Also checks the
weighted split `xi = xi^0 - lam xi^u`: the weighted reading is the difference of the two.
Exact `Fraction` arithmetic.
Run: nice taskset -c 4 timeout 600 python3 check_core_bridge.py
"""
import random
from fractions import Fraction as Fr

from _source_common import alphabet, coframes, sample, solve

rng = random.Random(11)
seen = 0
for _ in range(400):
    s = sample(rng)
    X, Y, N, c, a, m = (s[k] for k in ('X', 'Y', 'N', 'c', 'a', 'm'))
    h = alphabet(rng, 4 * N)
    fr = coframes(X, Y, N, h)
    if fr is None:
        continue
    R, L = fr
    I, C = list(X[1:]), list(Y[:-1])
    # left base L0: terms with N - I_i < a (exponents below a)
    L0 = {e: v for e, v in L.items() if e < a}
    rows = [i for i in I if a <= i <= m]
    cols = [j for j in C if a <= j <= m]
    if m in C:
        continue  # the template requires c outside the cap columns (hcols); at j = c the residual lacks the diagonal nu
    if len(rows) != len(cols) or not rows:
        continue
    # unweighted reading
    def Lu(j):
        k = m - j
        return sum(h(k - e) * v for e, v in L0.items() if e <= k)
    # template residual: cap vector l_i = -v_i = coefficient of L at exponent N - i, rows N - c <= i
    ell = {i - (N - c): L.get(N - i, Fr(0)) for i in I if N - c <= i < N}
    def capres(jrel):
        base = h(c - jrel) if c - jrel > 0 else Fr(0)
        return base + sum(v * h(i - jrel) for i, v in ell.items())
    for j in cols:
        assert capres(j - a) == Lu(j), (s, j)
    A = [[h(i - j) for j in cols] for i in rows]
    xi = solve([[A[r][t] for r in range(len(rows))] for t in range(len(cols))], [Lu(j) for j in cols])
    if xi is None:
        continue
    # same system through the template residual and relative labels
    rel = [i - a for i in rows]
    B = [[h(i - (j - a) - 0) if False else h((i + a) - j) for i in rel] for j in cols]
    y = solve(B, [capres(j - a) for j in cols])
    assert y == xi
    # weighted split
    lam = Fr(rng.randint(-5, 5), rng.randint(1, 4))
    def Lw(j):
        k = m - j
        return sum((k - lam - e) * h(k - e) * v for e, v in L0.items() if e <= k)
    def L1(j):
        k = m - j
        return sum((k - e) * h(k - e) * v for e, v in L0.items() if e <= k)
    for j in cols:
        assert Lw(j) == L1(j) - lam * Lu(j)
    seen += 1
assert seen >= 20, seen
print("OK", seen)
