r"""Paper section `sec:response` (The complete scalar and its second channel).

Boolean limit of the cap response (shields-2026-skew-ribbon-period.tex, sec:response,
lem:boolean, eq:clock-infinity, eq:cap-high) in the observer model.

The cross term of the observer is [z^m] H R_t L0 with m = a + c: for a return term z^{a+j} and a
term z^k of L0 it reads h_{m-(a+j)-k} = h_{c-j-k}, a RELATIVE label whose value is nu = h_0 when
k = c - j, whatever q is.  So x_R = sum_i (v_L(C_R)^t B_R^{-1})_i z^{c-i} has v_L(j) =
sum_i l_i h_{i-j} (relative labels, h_0 = nu), the form of the template systems.

Part 1 (the observer reading, on actual sources): [z^m] H (R_t L0) equals
sum_j rho_j * sum_k L0_k h_{c-j-k}.   Part 2 (T_R -> e_R in {0,1}): on a cap with top row c = 3,
cap rows {3, 1}, cap columns {0}, return core (rows {1}, columns {0}):
  - return unit z = 3 (the vacancy c is a return unit):  [nu^0]_inf T_R(z^0) = 1;
  - return unit z = 2 (c absent from the returns):       [nu^0]_inf T_R(z^0) = 0.
nu-Laurent coefficients at infinity by exact sympy series in t = 1/nu.
Run: nice taskset -c 4 timeout 600 python3 check_boolean_limit.py
"""
import random
import sympy as sp
from sympy import Matrix, Rational

nu = sp.Symbol("nu", positive=True)
t = sp.Symbol("t", positive=True)
hs = sp.symbols("h1:6", positive=True)


def H(k):
    if k < 0:
        return 0
    if k == 0:
        return nu
    return hs[k - 1]


c = 3
ell = {3: sp.Integer(1), 1: -H(3) / H(1)}
assert sp.simplify(sum(ell[i] * H(i - 0) for i in ell)) == 0


def v(j):
    return sp.simplify(sum(ell[i] * H(i - j) for i in ell))


def top_coeff(unit):
    rows, cols = [1, unit], [0, unit]
    M = Matrix([[H(i - j) for j in cols] for i in rows])
    rhs = Matrix([[v(j) for j in cols]])
    y = (rhs * M.inv()).applyfunc(sp.simplify)
    # numerator x_R = sum y_i z^{c-i}; l = 1 + sum ell_i z^{c-i}; [z^0] T_R = y_c (c a return row)
    yc = y[1] if unit == c else 0
    ser = sp.series(sp.simplify(yc.subs(nu, 1 / t)) if yc != 0 else sp.Integer(0), t, 0, 2).removeO()
    return sp.simplify(ser.coeff(t, 0)), sp.simplify(ser.coeff(t, 1)) if yc != 0 else 0


e1, _ = top_coeff(3)
assert e1 == 1, e1
e0, _ = top_coeff(2)
assert e0 == 0, e0

# Part 1: the reading of the return term against L0 on a random nu-polynomial pair
random.seed(5)
for _ in range(200):
    a = random.randint(4, 9)
    cc = random.randint(1, 3)
    m = a + cc
    rho = {a + j: Rational(random.randint(-5, 5)) for j in range(cc + 1)}
    L0 = {k: Rational(random.randint(-5, 5)) for k in range(0, a)}
    L0[0] = Rational(1)
    hv = {k: Rational(random.randint(1, 9)) for k in range(1, 3 * a)}
    hv[0] = Rational(random.randint(1, 9))
    hh = lambda k: Rational(0) if k < 0 else hv[k]
    lhs = sum(hh(m - e - k) * rho[e] * L0[k] for e in rho for k in L0)
    rhs = sum(rho[a + j] * sum(L0[k] * hh(cc - j - k) for k in L0 if k <= cc - j) for j in range(cc + 1))
    assert lhs == rhs
print("OK")
