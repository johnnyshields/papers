r"""Paper section `app:coincident` (Positive coincident attachment phases).

The caps of the coincident marked matrix carry the class pole, and the cap minors are nonzero.

Section: app:coincident, lem:coincident-reader ("All component slots B_1, ..., B_{L-1} have the
class phi = s_{B_*} ... Put B_0 = B_L = B_* ... The actual cap cofactors have smaller span and are
phi-units.  At this prime the cap contact coefficient at tau is phi divided by a nonzero cap
minor, hence zero; the remaining cap coframe is exactly the endpoint coframe of B_*").

The marked matrix is bordered by the column tau at band 0 and the row L g + tau at band L, so its
two cap blocks are B_* itself: every diagonal block, caps included, has determinant phi and a
simple pole at phi = 0.  The script asserts, with exact rationals in the low variables:

1. with all L + 1 blocks equal to B_* (pole order 1 at every band), every path term
   r X_{L,a} E_{a,b} X_{b,0} c has pole order at most L - (a - b) + 2; the end-row and end-column
   terms have order at most L - B + 1; the whole numerator has order at most R + 2, R = L - B, and
   its phi^{-(R+2)} coefficient is that of the B-edges alone;
2. that coefficient is kappa_R kappa_L (-y rho)^R sum_{a = b + B} V_a E_{a,b} U_b, with U, V the
   normalized port column and row of the residue of phi M^{-1}, rho the port residue,
   kappa_R = rho (r . U_L) and kappa_L = rho (V_0 . c);
3. over every coincident mark W = (X, Y) on [0, u], u <= 6, with u in X, 0 in Y, 0 < tau < u,
   tau in X and Y, W and B_* = (X - tau, Y - tau) of nonzero Jacobi-Trudi determinant and the
   h_u-coefficient c_f of phi nonzero: the two cap minors r . adj(B_*) e_{j0} = det(X - {u}, Y - tau)
   and e_{k0} adj(B_*) . c = det(X - tau, Y - {0}) are nonzero polynomials free of h_u.  These are
   the factors kappa_R / rho, kappa_L / rho of item 2 at phi = 0.
"""
import itertools
import random
from fractions import Fraction

import sympy as sp

random.seed(5)
t, eps = sp.symbols("t eps")


def rnd():
    return sp.Rational(random.randint(-9, 9) or 1, random.randint(1, 4))


# ---------------------------------------------------------------- items 1 and 2
u = 3
TAU = 1
L, B = 4, 2
R = L - B
H = {k: (rnd() if k > 0 else sp.Integer(0)) for k in range(-u - 1, u + 1)}
H[0] = sp.Integer(1)
H[u] = t
J, K = [3, 2], [0, 2]              # B_* : rows X - tau, columns Y - tau, X = {3,2,1}, Y = {0,1,2}
n = len(J)


def block(rows, cols):
    return sp.Matrix(len(rows), len(cols), lambda i, j: H[rows[i] - cols[j]])


Mb = block(J, K)
phi = sp.expand(Mb.det())
c_f = sp.Poly(phi, t).coeff_monomial(t)
d_f = sp.Poly(phi, t).coeff_monomial(1)
assert c_f != 0
y = rnd()
N = (L + 1) * n
A = sp.zeros(N, N)
for a in range(L + 1):
    A[a * n:(a + 1) * n, a * n:(a + 1) * n] = Mb
    if a > 0:
        A[a * n + 0, (a - 1) * n + 0] = y          # row label u (index 0), column label 0 (index 0)
cvec = sp.zeros(N, 1)
rvec = sp.zeros(1, N)
for i in range(n):
    cvec[i, 0] = H[J[i] - TAU]                    # the column tau against the rows of band 0
    rvec[0, L * n + i] = H[TAU - K[i]]            # the row L g + tau against the columns of band L


def to_eps(expr):
    return sp.together(sp.expand(expr).subs(t, (eps - d_f) / c_f))


def pole_order(expr):
    num, den = sp.fraction(sp.together(expr))
    if num == 0:
        return -10**9
    vn = min(m[0] for m in sp.Poly(num, eps).monoms())
    vd = min(m[0] for m in sp.Poly(den, eps).monoms())
    return vd - vn


def coeff_top(expr, k):
    return sp.simplify(sp.limit(sp.together(expr) * eps**k, eps, 0))


Ainv = A.inv().applyfunc(sp.cancel)
total_E = sp.zeros(N, N)
Eblocks = {}
terms = {}
for a in range(L + 1):
    for b in range(L + 1):
        if a - b < B:
            continue
        Eab = sp.zeros(N, N)
        blk = sp.zeros(n, n)
        for i in range(n):
            for j in range(n):
                v = rnd() + rnd() * t
                Eab[a * n + i, b * n + j] = v
                blk[i, j] = v
        Eblocks[(a, b)] = blk
        total_E += Eab
        term = to_eps((rvec * Ainv * Eab * Ainv * cvec)[0, 0])
        assert pole_order(term) <= L - (a - b) + 2, (a, b)
        terms[(a, b)] = term
# end row on bands b <= R, end column on bands a >= B
er = sp.zeros(1, N)
ec = sp.zeros(N, 1)
for b in range(R + 1):
    for j in range(n):
        er[0, b * n + j] = rnd() + rnd() * t
for a in range(B, L + 1):
    for i in range(n):
        ec[a * n + i, 0] = rnd() + rnd() * t
assert pole_order(to_eps((er * Ainv * cvec)[0, 0])) <= R + 1
assert pole_order(to_eps((rvec * Ainv * ec)[0, 0])) <= R + 1
num = to_eps((rvec * Ainv * total_E * Ainv * cvec)[0, 0] - (er * Ainv * cvec)[0, 0]
             - (rvec * Ainv * ec)[0, 0])
assert pole_order(num) <= R + 2
top = coeff_top(num, R + 2)
top_B = coeff_top(sum(v for (a, b), v in terms.items() if a - b == B), R + 2)
assert sp.simplify(top - top_B) == 0 and top != 0

# item 2: the residue coframes of phi M^{-1} at phi = 0
adj0 = Mb.adjugate().subs(t, -d_f / c_f)              # residue of eps M^{-1}, eps = phi = det M
rho = adj0[0, 0]                                      # (k0, j0) = (0, 0)
assert rho != 0
U = [adj0[k, 0] / rho for k in range(n)]              # port column, indexed by the columns of M
V = [adj0[0, j] / rho for j in range(n)]              # port row, indexed by the rows of M
r0 = [H[TAU - K[k]].subs(t, -d_f / c_f) for k in range(n)]
c0 = [H[J[j] - TAU].subs(t, -d_f / c_f) for j in range(n)]
kR = rho * sum(r0[k] * U[k] for k in range(n))
kL = rho * sum(V[j] * c0[j] for j in range(n))
assert kR != 0 and kL != 0
pred = 0
for b in range(R + 1):
    blk = Eblocks[(b + B, b)].subs(t, -d_f / c_f)
    pred += sum(V[i] * blk[i, j] * U[j] for i in range(n) for j in range(n))
pred *= kR * kL * (-y * rho) ** R
assert sp.simplify(top - pred) == 0
print(f"L={L}, B={B}, R={R}: caps of det phi, numerator of order R+2 from the B-edges, "
      f"coefficient kappa_R kappa_L (-y rho)^R sum V E U")

# ---------------------------------------------------------------- item 3


def jt(rows, cols, h):
    m = [[h(x - y_) for y_ in cols] for x in rows]
    return sp.Matrix(m).det() if m else sp.Integer(1)


hs = sp.symbols("h1:8")


def hsym(k):
    if k < 0:
        return 0
    if k == 0:
        return 1
    return hs[k - 1]


count = 0
for uu in range(2, 7):
    hu = hs[uu - 1]
    inner = range(1, uu)
    for xs in itertools.chain.from_iterable(itertools.combinations(inner, s) for s in range(uu)):
        X = sorted(set(xs) | {uu}, reverse=True)
        for ys in itertools.combinations(inner, len(X) - 1):
            Y = sorted(set(ys) | {0})
            for tau in set(X) & set(Y):
                if not 0 < tau < uu:
                    continue
                if sp.expand(jt(X, Y, hsym)) == 0:
                    continue
                Jx = [x for x in X if x != tau]
                Ky = [y_ for y_ in Y if y_ != tau]
                ph = sp.expand(jt(Jx, Ky, hsym))
                if ph == 0 or sp.Poly(ph, hu).coeff_monomial(hu) == 0:
                    continue
                mR = sp.expand(jt([x for x in X if x != uu], Ky, hsym))
                mL = sp.expand(jt(Jx, [y_ for y_ in Y if y_ != 0], hsym))
                assert mR != 0 and mL != 0, (uu, X, Y, tau)
                assert hu not in mR.free_symbols and hu not in mL.free_symbols
                count += 1
assert count > 0
print(f"{count} coincident marks with u <= 6: both cap minors nonzero and free of h_u")
print("ALL PASS")
