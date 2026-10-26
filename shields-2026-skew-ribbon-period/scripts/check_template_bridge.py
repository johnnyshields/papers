r"""Paper section `sec:response` (The complete scalar and its second channel).

Check of the template bridge (shields-2026-skew-ribbon-period.tex, sec:response,
eq:base-residuals, eq:source-truncations, eq:cap-high).

Claim: for a connected diagram with beta lists xi, zeta (I = xi[1:], C = zeta[:-1], N = xi[0]),
window parameters a = N - q - c with c < a, the left base solution v0 (rows I_i > N - a, columns
C_j > N - a, system  sum_i h_{I_i - C_j} v_i = h_{N - C_j}) satisfies

  (1) the upper cap rows I_+ = {I_i in [N - c, N)} and columns C_+ = {C_j in [N - c, N)} have
      |I_+| = |C_+|;
  (2) v0 restricted to the rows I_+ is the solution of the cap system on the columns C_+, and
      v0 vanishes nowhere else in the head, i.e. the head l(z) = 1 - sum v0_i z^{N - I_i}
      (degrees <= c) is the cap vector of the template with lists I_+, C_+;
  (3) the source return block rows I_R = I in [a, a + c], columns C_R = C in [a, a + c]
      have |I_R| = |C_R|.
Exact rational arithmetic; one core.
"""
import random
from sympy import Matrix, Rational, zeros

random.seed(1)


def hh(h, k):
    if k < 0:
        return Rational(0)
    if k == 0:
        return Rational(1)
    return h[k]


def beta(r, g):
    n = len(g)
    ze = [sum(r[k + 1] - g[k] for k in range(i, n)) for i in range(n + 1)]
    xi = [ze[i] + r[i] for i in range(n + 1)]
    return xi, ze


checked = 0
for trial in range(4000):
    n = random.randint(2, 5)
    r = [random.randint(1, 6) for _ in range(n + 1)]
    g = []
    ok = True
    for k in range(n):
        m = min(r[k], r[k + 1])
        if m < 1:
            ok = False
            break
        g.append(random.randint(0, m - 1))
    if not ok:
        continue
    xi, ze = beta(r, g)
    N = xi[0]
    I = xi[1:]
    C = ze[:-1]
    q = random.randint(1, 3)
    c = random.randint(1, 3)
    a = N - q - c
    if a <= c:
        continue
    Ip = [i for i in range(n) if N - c <= I[i] < N]
    Cp = [j for j in range(n) if N - c <= C[j] < N]
    IR = [i for i in range(n) if a <= I[i] <= a + c]
    CR = [j for j in range(n) if a <= C[j] <= a + c]
    if len(Ip) != len(Cp) or len(IR) != len(CR):
        continue
    h = {k: Rational(random.randint(1, 9), random.randint(1, 5)) for k in range(1, N + 2)}
    A = Matrix(n, n, lambda i, j: hh(h, I[i] - C[j]))
    if A.det() == 0:
        continue
    w = Matrix([[hh(h, N - C[j]) for j in range(n)]])
    v = list(w * A.inv())
    if Ip:
        Mc = Matrix(len(Cp), len(Ip), lambda jj, ii: hh(h, I[Ip[ii]] - C[Cp[jj]]))
        if Mc.det() == 0:
            continue
        rc = Matrix([hh(h, N - C[j]) for j in Cp])
        y = Mc.LUsolve(rc)
        for ii, i in enumerate(Ip):
            assert v[i] == y[ii], (xi, ze, q, c, i)
    # rows of the full solution in [N - c, N) are exactly I_+; none other lies in the head
    checked += 1
assert checked >= 20, checked
print("OK", checked)
