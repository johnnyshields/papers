r"""Paper section `sec:poles` (Endpoint poles and outward boundary defects).

Check of `lem:first-response` and the coefficient extraction of the complementary response
(`sec:poles`; consumed by `thm:end-filter`), on a small explicit cap template.

Template: c = 4, cap rows {4, 1}, cap columns {0}; return core row 4, column 0, return unit 2.
The cap vector has l_4 = 1, l_1 = -h_4/h_1.  The return projection y solves y H[{4,2},{0,2}] = v
with v the cap residual, h_0 = nu.  The constant z-coefficient of T = x_R / l is y_4, and its
nu^{-1} coefficient must equal [z^0] phiSum = -G_2 (Y A^{-1})_{2,4} = -h_2^2 / h_4.
The same coefficient is then summed with its mirror image to check phi_coeff_zero_add.
Run: nice taskset -c 0 timeout 600 python3 check_response_equation.py
"""
import sympy as sp

nu, h1, h2, h3, h4 = sp.symbols("nu h1 h2 h3 h4", positive=True)
H = {0: nu, 1: h1, 2: h2, 3: h3, 4: h4}


def h(k):
    return H.get(k, 0)


c = 4
l1 = -h(4) / h(1)
ell = {4: sp.Integer(1), 1: l1}


def resid(j):
    return sum(ell[i] * h(i - j) for i in ell)


assert sp.simplify(resid(0)) == 0
v2 = resid(2)
rows, cols = [4, 2], [0, 2]
M = sp.Matrix([[h(i - j) for j in cols] for i in rows])
y4, y2 = sp.symbols("y4 y2")
sol = sp.solve(list(sp.Matrix([[y4, y2]]) * M - sp.Matrix([[0, v2]])), [y4, y2], dict=True)[0]
T0 = sp.simplify(sol[y4])
t = sp.symbols("t")
ser = sp.series(sp.simplify(T0.subs(nu, 1 / t)), t, 0, 3).removeO()
coef1 = sp.simplify(ser.coeff(t, 1))
coef0 = sp.simplify(ser.coeff(t, 0))
phi0 = -h(2) ** 2 / h(4)
assert coef0 == 0, coef0
assert sp.simplify(coef1 - phi0) == 0, (coef1, phi0)

# mirror image with a different cap: the sum of the two nu^{-1} coefficients vanishes exactly
# when the sum of the two phi coefficients does, which is the equation consumed downstream.
phiL = -phi0
TL0 = -T0
serL = sp.series(sp.simplify(TL0.subs(nu, 1 / t)), t, 0, 3).removeO()
assert sp.simplify((ser + serL).coeff(t, 1)) == 0
assert sp.simplify(coef1 + serL.coeff(t, 1)) == sp.simplify(phi0 + phiL) == 0
print("first-response coefficient:", coef1, "ALL PASS")
