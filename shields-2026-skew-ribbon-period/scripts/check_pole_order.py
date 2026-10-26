r"""Paper section `app:coincident` (Positive coincident attachment phases).

Pole order of the band-path sum at the marked class.

Section: app:coincident, lem:coincident-reader ("Each actual internal block has one simple phi pole
... Hence the whole highest pole phi^{-r} comes from precisely the r+1 paths with a B-edge from i to
i+B, 0 <= i <= r").

Bands 0..L carry diagonal blocks M_a.  The interior bands 1..L-1 all carry the same block (one
marked class), whose determinant phi = c h_u + d is affine in the port variable h_u = t with
c != 0; the two caps M_0, M_L carry other blocks, whose determinants are phi-units.  The coupling
from band a-1 to band a is the rank-one y E_{u,0}.  E is a band-lower matrix supported on band
pairs (a, b) with a - b >= B, with entries affine in t.  With r = L - B, the script asserts, with
exact rationals in the remaining variables:

1. every path term  r X_{L,a} E_{a,b} X_{b,0} c  has pole order at phi at most the number of
   interior bands in [0, b] and [a, L], which is L - (a - b);
2. the generic B-edge term between interior bands reaches order exactly r;
3. the whole sum  r A^{-1} E A^{-1} c  has pole order at most r, and its phi^{-r} coefficient is the
   phi^{-r} coefficient of the sum over the B-edges alone;
4. rho = r A^{-1} c has pole order exactly L - 1.
"""
import random
import sympy as sp

random.seed(11)
t, eps = sp.symbols("t eps")
u = 3
L, B = 5, 2
R_ORDER = L - B


def rnd():
    return sp.Rational(random.randint(-9, 9) or 1, random.randint(1, 4))


H = {k: (rnd() if k > 0 else 0) for k in range(-u - 1, u + 1)}
H[0] = 1
H[u] = t


def block(J, K):
    return sp.Matrix(len(J), len(K), lambda i, j: H[J[i] - K[j]])


J_INT, K_INT = [3, 2], [0, 1]          # interior: phi = t h_1 - h_2^2
J_CAP0, K_CAP0 = [3, 1], [0, 1]        # cap 0:  t - h_1 h_2
J_CAPL, K_CAPL = [3, 2], [0, 2]        # cap L:  t - h_1 h_2 (up to labels)
n = 2
blocks = [block(J_CAP0, K_CAP0)] + [block(J_INT, K_INT)] * (L - 1) + [block(J_CAPL, K_CAPL)]
phi = sp.expand(blocks[1].det())
c_f = sp.Poly(phi, t).coeff_monomial(t)
d_f = sp.Poly(phi, t).coeff_monomial(1)
assert c_f != 0
for a in (0, L):
    assert sp.rem(sp.Poly(blocks[a].det(), t), sp.Poly(phi, t)).as_expr() != 0  # cap is a phi-unit
y = rnd()
N = (L + 1) * n
A = sp.zeros(N, N)
for a in range(L + 1):
    A[a * n:(a + 1) * n, a * n:(a + 1) * n] = blocks[a]
    if a > 0:
        A[a * n + 0, (a - 1) * n + 0] = y      # j0 = row of label u (index 0), k0 = column of label 0
cvec = sp.zeros(N, 1)
rvec = sp.zeros(1, N)
for i in range(n):
    cvec[i, 0] = rnd()
    rvec[0, L * n + i] = rnd()


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


Ainv = A.inv()
Ainv = Ainv.applyfunc(sp.cancel)
total_E = sp.zeros(N, N)
terms = {}
for a in range(L + 1):
    for b in range(L + 1):
        if a - b < B:
            continue
        Eab = sp.zeros(N, N)
        for i in range(n):
            for j in range(n):
                Eab[a * n + i, b * n + j] = rnd() + rnd() * t
        total_E += Eab
        term = to_eps((rvec * Ainv * Eab * Ainv * cvec)[0, 0])
        order = pole_order(term)
        bound = len([x for x in range(1, L) if x <= b or x >= a])
        assert bound == L - (a - b), (a, b)
        assert order <= bound, (a, b, order, bound)
        terms[(a, b)] = term
        if a - b == B and 0 < b and a < L:
            assert order == R_ORDER, (a, b, order)
total = to_eps((rvec * Ainv * total_E * Ainv * cvec)[0, 0])
assert pole_order(total) <= R_ORDER
top_total = coeff_top(total, R_ORDER)
top_B = coeff_top(sum(v for (a, b), v in terms.items() if a - b == B), R_ORDER)
assert sp.simplify(top_total - top_B) == 0
assert top_total != 0
rho = to_eps((rvec * Ainv * cvec)[0, 0])
assert pole_order(rho) == L - 1
print(f"L={L}, B={B}, r={R_ORDER}: path orders <= L-(a-b), B-edge order r, top coefficient "
      f"from B-edges alone, rho of order L-1")
print("ALL PASS")
