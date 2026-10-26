r"""Paper section `sec:response` (The complete scalar and its second channel).

The Hall cap-high equations (shields-2026-skew-ribbon-period.tex, sec:response, eq:base-residuals,
eq:cap-high, `D(z) = w_c (1 - T_R - T_L)`, `prop:clocks`; Lean: `cap_high_hall`).  The Hall
observer is the unweighted reading `readH P k = sum_{e<=k} h_{k-e} P_e` (weight 1 in place of
`k - lambda - e`); the equations read `[z^s] R0 L0 = [z^s](R0 X + L0 Y)` for `s <= m - a`, `xi`, `eta`
solving the transposed return systems against `readH` of the base coframes.  Same instances as
check_cap_high_poly.py.  For a source (I, C, N) with generic rational
h_k (h_0 = 1, h_k = 0 for k < 0), u = M^{-1} b, v = w M^{-1}, a <= m < 2a
with balanced window counts, and xi, eta solving the transposed return systems
  sum_{i in IR} h_{I_i - C_j} xi_i = readH(L0)(m - C_j),   j in CR,
  sum_{j in CL} h_{I_i - C_j} eta_j = readH(R0)(m - N + I_i),  i in IL,
the derivative of the Hall observer readH (R_S L_S) m with respect to h_t, t = m - s >= a
(computed from dU = M^{-1}(db - dM u), dV = (dw - v dM) M^{-1}) equals
  [z^s] R0 L0 - [z^s](R0 X + L0 Y),   X = sum xi_i z^{m - I_i},
  Y = sum eta_j z^{m - N + C_j}.
The observer vanishes identically in h at a Hall zero, so its derivative vanishes and the
Hall cap-high equation [z^s] R0 L0 = [z^s](R0 X + L0 Y) follows.
Exact rational arithmetic; one core.  Run: nice taskset -c 4 timeout 600 python3 check_cap_high_hall.py
"""
import random
from sympy import Matrix, Rational, Symbol, expand, Poly, zeros

random.seed(11)
z = Symbol("z")


def H(h, k):
    return Rational(1) if k == 0 else (Rational(0) if k < 0 else h[k])


def obs(lam, P, k, h):
    # readH P k = sum_{e<=k} h_{k-e} P_e (lam is ignored)
    cf = Poly(P, z).all_coeffs()[::-1] if P != 0 else [0]
    return sum(H(h, k - e) * (cf[e] if e < len(cf) else 0) for e in range(k + 1))


checked = 0
for trial in range(4000):
    n = random.randint(2, 4)
    a = random.randint(2, 5)
    c = random.randint(0, a - 1)
    m = a + c
    if not (m < 2 * a):
        continue
    N = random.randint(m, m + 6)
    if n > N + 1:
        continue
    I = sorted(random.sample(range(0, N + 1), n), reverse=True)
    C = sorted(random.sample(range(0, N + 1), n), reverse=True)
    cnt = lambda L, P: sum(1 for x in L if P(x))
    if cnt(I, lambda x: x <= m) != cnt(C, lambda x: x <= m):
        continue
    if cnt(I, lambda x: N - m <= x) != cnt(C, lambda x: N - m <= x):
        continue
    if cnt(I, lambda x: x <= a - 1) != cnt(C, lambda x: x <= a - 1):
        continue
    if cnt(I, lambda x: N - (a - 1) <= x) != cnt(C, lambda x: N - (a - 1) <= x):
        continue
    h = {k: Rational(random.randint(1, 9), random.randint(1, 5)) for k in range(1, 3 * N + 3)}
    M = Matrix(n, n, lambda i, j: H(h, I[i] - C[j]))
    if M.det() == 0:
        continue
    b = Matrix([H(h, I[i]) for i in range(n)])
    w = Matrix([[H(h, N - C[j]) for j in range(n)]])
    u = M.inv() * b
    v = (w * M.inv()).T
    RS = 1 - sum(u[j] * z ** C[j] for j in range(n))
    LS = 1 - sum(v[i] * z ** (N - I[i]) for i in range(n))
    lamv = Rational(random.randint(-7, 7), random.randint(1, 4))
    R0 = 1 - sum(u[j] * z ** C[j] for j in range(n) if C[j] < a)
    L0 = 1 - sum(v[i] * z ** (N - I[i]) for i in range(n) if N - a < I[i])
    IR = [i for i in range(n) if a <= I[i] <= m]
    CR = [j for j in range(n) if a <= C[j] <= m]
    IL = [i for i in range(n) if N - m <= I[i] <= N - a]
    CL = [j for j in range(n) if N - m <= C[j] <= N - a]
    assert len(IR) == len(CR) and len(IL) == len(CL)
    if IR:
        BR = Matrix(len(IR), len(CR), lambda p, q: H(h, I[IR[p]] - C[CR[q]]))
        if BR.det() == 0:
            continue
        phi = Matrix([obs(lamv, L0, m - C[j], h) for j in CR])
        xi = BR.T.inv() * phi
    if IL:
        BL = Matrix(len(IL), len(CL), lambda p, q: H(h, I[IL[p]] - C[CL[q]]))
        if BL.det() == 0:
            continue
        psi = Matrix([obs(lamv, R0, m - (N - I[i]), h) for i in IL])
        eta = BL.inv() * psi
    X = sum(xi[p] * z ** (m - I[IR[p]]) for p in range(len(IR))) if IR else 0
    Y = sum(eta[p] * z ** (m - N + C[CL[p]]) for p in range(len(CL))) if IL else 0
    for s in range(0, m - a + 1):
        t = m - s
        dM = Matrix(n, n, lambda i, j: Rational(1) if I[i] - C[j] == t else Rational(0))
        db = Matrix([Rational(1) if I[i] == t else Rational(0) for i in range(n)])
        dw = Matrix([[Rational(1) if N - C[j] == t else Rational(0) for j in range(n)]])
        du = M.inv() * (db - dM * u)
        dv = ((dw - (v.T * dM)) * M.inv()).T
        dRS = -sum(du[j] * z ** C[j] for j in range(n))
        dLS = -sum(dv[i] * z ** (N - I[i]) for i in range(n))
        P = expand(RS * LS)
        dP = expand(dRS * LS + RS * dLS)
        cfP = Poly(P, z).all_coeffs()[::-1]
        cfdP = Poly(dP, z).all_coeffs()[::-1] if dP != 0 else [0]
        g = lambda cf, e: cf[e] if e < len(cf) else 0
        dobs = sum(((Rational(1) if m - e == t else Rational(0)) * g(cfP, e)
                                     + H(h, m - e) * g(cfdP, e)) for e in range(m + 1))
        l = Poly(expand(R0 * L0), z).coeff_monomial(z ** s)
        r = Poly(expand(R0 * X + L0 * Y), z).coeff_monomial(z ** s)
        assert dobs == l - r, (I, C, N, a, m, s)
    checked += 1
    if checked >= 40:
        break
assert checked >= 20, checked
print("cap-high polynomial form: instances checked", checked)
print("PASS")
