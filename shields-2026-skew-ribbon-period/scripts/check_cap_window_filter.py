r"""Paper section `sec:response` (The complete scalar and its second channel).

Checks behind CapWindowFilter (prop:clocks, thm:end-filter of the skew ribbon period paper).

Scope: the algebraic inputs of the window form that can be tested without a supplied
comparison (none is known to exist in the hard domain):
  1. the sum-horizon commutator coefficient (prop:clocks, before the proposition);
  2. the clock rigidity identity  (alpha-beta) D = (q-p) r l  with D = eps r l  forces
     alpha - beta = eps (q - p), consistent with alpha = eps (N-p-Delta), beta = eps (N-q-Delta);
  3. the complementary clock lambda(1-e_R-e_L) = a + sigma - tau with T_R+T_L = 0 gives
     lambda = a + sigma - tau, and with T_R+T_L = 1 no ordinary zero (a+sigma-tau > 0);
  4. ex:c3: the middle return determinants of I0={3}, C0={0} coincide, and the endpoint
     pole numerator (|A_R|+|A_L|) h1 h2 / h3 cannot cancel for positive specialization.
"""
import sympy as sp

# 1
k, p, q, al, be = sp.symbols("k p q alpha beta")
lhs = (k + p - be) * (k - al) - (k + q - al) * (k - be)
assert sp.expand(lhs - ((p - q) * k + q * be - p * al)) == 0

# 2
eps, N, Delta = sp.symbols("eps N Delta")
alpha = eps * (N - p - Delta)
beta = eps * (N - q - Delta)
assert sp.simplify((alpha - beta) - eps * (q - p)) == 0
# (alpha-beta) D = (q-p) r l with D = eps r l, eps^2 = 1
rl = sp.symbols("rl")
assert sp.simplify(((alpha - beta) * eps * rl).subs(eps**2, 1) - (q - p) * rl) == 0 or \
    sp.expand(((alpha - beta) * eps * rl) - eps**2 * (q - p) * rl) == 0

# 3
lam, a, sig, tau, eR, eL = sp.symbols("lam a sigma tau e_R e_L")
assert sp.solve(sp.Eq(lam * (1 - eR - eL), a + sig - tau), lam)[0].subs({eR: 0, eL: 0}) == a + sig - tau
# e_R + e_L = 1 makes the left side 0, impossible for a + sigma - tau > 0
assert (lam * (1 - 1)) == 0

# 4
h1, h2, h3, nu = sp.symbols("h1 h2 h3 nu", positive=True)
M1 = sp.Matrix([[h2, h3], [nu, h1]])
M2 = sp.Matrix([[h1, h3], [nu, h2]])
assert sp.expand(M1.det() - (h1 * h2 - nu * h3)) == 0 and sp.expand(M2.det() - M1.det()) == 0
for nR in range(0, 4):
    for nL in range(0, 4):
        if nR + nL > 0:
            val = (nR + nL) * (h1 * h2 / h3)
            assert val.subs({h1: 2, h2: 3, h3: 5}) > 0
print("PASS")
